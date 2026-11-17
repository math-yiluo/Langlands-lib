import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.RelativeDerivedGroupExistenceConstruction
import Langlands.GroupScheme.Reductive.RelativeSemisimpleFppfPerfectProof
import Langlands.GroupScheme.Derived.RelativeMaximalTorusIntersection
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof

/-! # Simply connected derived groups of relative split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Relative

variable {R : CommRingCat.{u}} {G C D : GroupScheme (Spec R)}
  {T : CommGroupScheme (Spec R)} (a : T.toGrp ⟶ G)
  (hT : IsSplitTorus T.toGrp) (j : C ⟶ G)
  (hj : (torusCentralizer a).IsRepresentedBy j)

include a hT hj in
/-- Every smooth closed representative of a split-torus centralizer in a
relative reductive group is reductive over the original affine base. -/
theorem isReductive_splitTorusCentralizer_overRing (hG : IsReductive G)
    (hjc : IsClosedSubgroup j) (hCs : Smooth C.X.hom) : IsReductive C := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  refine ⟨hCs, hjc.isAffineHom, fun s => ?_⟩
  let k := AlgebraicClosure ((Spec R).residueField s)
  let b := geometricPoint (Spec R) s
  let Gs := (baseChange b).obj G
  let Ts := (CommGroupScheme.baseChange b).obj T
  let Cs := (baseChange b).obj C
  let as := (baseChange b).map a
  let js := (baseChange b).map j
  have hTs : IsSplitTorus Ts.toGrp := hT.baseChange b
  let : IsAffineHom Gs.X.hom := (hG.isConnectedReductive_baseChange b).isAffineHom
  let : Smooth Gs.X.hom := (hG.isConnectedReductive_baseChange b).smooth
  have hjs : (torusCentralizer (T := Ts) as).IsRepresentedBy js := by
    have h := hj.baseChange b
    rwa [← torusCentralizer_baseChange b a] at h
  let χ := CommGroupScheme.groupHom (centralizingCocharacter hTs as) ≫ as
  have hχ : (Dynamic.centralizer χ).IsRepresentedBy js := by
    change (Dynamic.centralizer
      (CommGroupScheme.groupHom (centralizingCocharacter hTs as) ≫ as)).IsRepresentedBy js
    rw [centralizingCocharacter_spec hTs as]
    exact hjs
  exact (dynamicCentralizerReductive k Gs (hG.isConnectedReductive_baseChange b)
    χ Cs js (hjc.baseChange b) hχ).isPseudoReductive

include a hT hj in
/-- An admissible relative derived subgroup of a split-subtorus centralizer
has simply connected geometric fibres whenever the ambient group does. -/
theorem isFibrewiseSimplyConnected_relativeDerived_splitCentralizer
    (hG : IsFibrewiseSimplyConnected G) (hac : IsClosedSubgroup a)
    (d : D ⟶ C) (hd : RelativeDerived.IsAdmissible d) :
    IsFibrewiseSimplyConnected D := by
  intro s
  let k := AlgebraicClosure ((Spec R).residueField s)
  let b := geometricPoint (Spec R) s
  have hjs : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map a)).IsRepresentedBy
      ((baseChange b).map j) := by
    have h := hj.baseChange b
    rwa [← torusCentralizer_baseChange b a] at h
  obtain ⟨Q, q, hQ, hq⟩ := hd.2.2.2.2
  have hds : IsDerivedSubgroup ((baseChange b).map d) :=
    isDerivedSubgroup_fieldFiber_of_semisimple_torusQuotient d hd.1 hd.2.2.1
      hd.2.2.2.1 q hQ hq b
  exact splitTorusCentralizerDerivedSimplyConnected k ((baseChange b).obj G) (hG s)
    ((CommGroupScheme.baseChange b).obj T) ((baseChange b).map a)
    ⟨hT.baseChange b, hac.baseChange b⟩ ((baseChange b).obj C)
    ((baseChange b).map j) hjs ((baseChange b).obj D) ((baseChange b).map d) hds

end Relative

/-- Actual relative centralizer and derived-group data for a split subtorus,
retaining both inclusions into the ambient group. -/
structure SplitTorusCentralizerDerivedModel {R : CommRingCat.{u}}
    {G : GroupScheme (Spec R)} {T : CommGroupScheme (Spec R)} (a : T.toGrp ⟶ G) where
  centralizer : GroupScheme (Spec R)
  inclusion : centralizer ⟶ G
  closed : IsClosedSubgroup inclusion
  represents : (torusCentralizer a).IsRepresentedBy inclusion
  reductive : IsReductive centralizer
  derivedGroup : GroupScheme (Spec R)
  derivedInclusion : derivedGroup ⟶ centralizer
  admissible : RelativeDerived.IsAdmissible derivedInclusion
  simplyConnected : IsFibrewiseSimplyConnected derivedGroup

namespace SplitTorusCentralizerDerivedModel

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {T : CommGroupScheme (Spec R)} {a : T.toGrp ⟶ G}
  (M : SplitTorusCentralizerDerivedModel a)

/-- The actual derived-centralizer inclusion in the original ambient group. -/
def ambientInclusion : M.derivedGroup ⟶ G := M.derivedInclusion ≫ M.inclusion

/-- The constructed factor is a closed subgroup of the original group. -/
theorem ambientInclusion_closed : IsClosedSubgroup M.ambientInclusion :=
  M.admissible.1.comp M.closed

/-- The constructed factor is reductive over the original base. -/
theorem isReductive : IsReductive M.derivedGroup := M.admissible.2.2.1

/-- Every actual field-valued fibre of the chosen relative derived group is
the scheme-theoretic derived group of the corresponding centralizer. -/
theorem isDerivedSubgroup_fieldFiber {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec R) :
    IsDerivedSubgroup ((baseChange b).map M.derivedInclusion) := by
  obtain ⟨Q, q, hQ, hq⟩ := M.admissible.2.2.2.2
  exact isDerivedSubgroup_fieldFiber_of_semisimple_torusQuotient M.derivedInclusion
    M.admissible.1 M.isReductive M.admissible.2.2.2.1 q hQ hq b

end SplitTorusCentralizerDerivedModel

/-- Construct an actual relative derived centralizer with simply connected
geometric fibres, over any affine base and for any closed split subtorus. -/
theorem nonempty_splitTorusCentralizerDerivedModel
    {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) (hG : IsReductive G)
    (hsc : IsFibrewiseSimplyConnected G) (T : CommGroupScheme (Spec R))
    (a : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ha : IsClosedSubgroup a) :
    Nonempty (SplitTorusCentralizerDerivedModel a) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, j, hjc, hCs, hj⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing a hT hG.smooth
  have hC : IsReductive C :=
    isReductive_splitTorusCentralizer_overRing a hT j hj hG hjc hCs
  obtain ⟨D, d, hd⟩ :=
    relativeDerivedGroupExistence_of_relativeSemisimpleFppfPerfect
      relativeSemisimpleFppfPerfect (Spec R) C hC
  exact ⟨⟨C, j, hjc, hj, hC, D, d, hd,
    isFibrewiseSimplyConnected_relativeDerived_splitCentralizer a hT j hj hsc ha d hd⟩⟩

/-- Choose the actual relative centralizer and its simply connected derived
group constructed by the published centralizer and derived-group theorems. -/
def splitTorusCentralizerDerivedModel
    {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) (hG : IsReductive G)
    (hsc : IsFibrewiseSimplyConnected G) (T : CommGroupScheme (Spec R))
    (a : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ha : IsClosedSubgroup a) :
    SplitTorusCentralizerDerivedModel a :=
  Classical.choice (nonempty_splitTorusCentralizerDerivedModel G hG hsc T a hT ha)

end Langlands.GroupScheme
