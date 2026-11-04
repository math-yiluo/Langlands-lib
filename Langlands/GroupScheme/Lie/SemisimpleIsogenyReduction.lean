import Langlands.GroupScheme.Lie.SemisimpleIsogenyReductionStatement
import Langlands.GroupScheme.Lie.CharZeroCentralTorus
import Langlands.GroupScheme.CentralIsogeny.RootDescent
import Langlands.GroupScheme.CentralIsogeny.GeometricSemisimpleKernel
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Torus.IsogenyLift

/-! # Isogeny reduction to nilpotence or a noncentral semisimple tangent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k : Type u} [Field k]

/-- A smooth connected affine target reached by an actual isogeny which
lifts all closed target tori up to isogeny. -/
structure SemisimpleReductionTarget (G : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  smooth : Smooth group.X.hom
  affine : IsAffineHom group.X.hom
  connected : ConnectedSpace group.X.left
  map : G ⟶ group
  isogeny : IsIsogeny map
  lifts : LiftsClosedToriUpToIsogeny map

namespace SemisimpleReductionTarget

variable {G : GroupScheme (Spec (CommRingCat.of k))}

instance (A : SemisimpleReductionTarget G) : Smooth A.group.X.hom := A.smooth
instance (A : SemisimpleReductionTarget G) : IsAffineHom A.group.X.hom := A.affine
instance (A : SemisimpleReductionTarget G) : ConnectedSpace A.group.X.left := A.connected

/-- The actual algebraic-closure pullback of a reachable target. -/
abbrev geometricGroup (A : SemisimpleReductionTarget G) :=
  (GroupScheme.baseChange (toAlgebraicClosure k)).obj A.group

instance (A : SemisimpleReductionTarget G) :
    Smooth A.geometricGroup.X.hom := by
  change Smooth (Limits.pullback.snd A.group.X.hom (toAlgebraicClosure k))
  infer_instance

instance (A : SemisimpleReductionTarget G) :
    IsAffineHom A.geometricGroup.X.hom := by
  change IsAffineHom (Limits.pullback.snd A.group.X.hom (toAlgebraicClosure k))
  infer_instance

instance (A : SemisimpleReductionTarget G) :
    ConnectedSpace A.geometricGroup.X.left :=
  A.group.connectedSpace_baseChange_of_smooth_affine (toAlgebraicClosure k)

/-- The original group is a reachable target. -/
def identity (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    SemisimpleReductionTarget G where
  group := G
  smooth := inferInstance
  affine := inferInstance
  connected := inferInstance
  map := 𝟙 G
  isogeny := isIsogeny_id G
  lifts := liftsClosedToriUpToIsogeny_id G

/-- A further central quotient remains a reachable target. Centrality of
the composite ambient isogeny is not required. -/
def centralQuotient (A : SemisimpleReductionTarget G)
    (Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : A.group ⟶ Q) (hq : IsCentralIsogeny q) : SemisimpleReductionTarget G where
  group := Q
  smooth := inferInstance
  affine := inferInstance
  connected := inferInstance
  map := A.map ≫ q
  isogeny := A.isogeny.comp hq.isIsogeny
  lifts := A.lifts.comp hq.liftsClosedToriUpToIsogeny

/-- A central geometric maximal torus gives nilpotence over the original
field directly from the uniform bound on geometric points. -/
theorem isNilpotent_of_geometric_central_maximalTorus (A : SemisimpleReductionTarget G)
    {T : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    {i : T.toGrp ⟶ A.geometricGroup}
    (hi : IsMaximalTorus i) (hc : IsCentral i) : IsNilpotentGroupScheme A.group := by
  obtain ⟨d, hd⟩ := (hi.centralQuotient hc).exists_hasUniformNilpotentPoints_of_isAlgClosed
  exact Subgroup.nilpotent_iff_lowerCentralSeries.2 ⟨d, hd _⟩

/-- In characteristic zero, central geometric semisimple tangents already
force the original reachable target to be nilpotent. -/
theorem isNilpotent_of_geometric_semisimple_central [CharZero k]
    (A : SemisimpleReductionTarget G)
    (hcen : ∀ X : lieKernel A.geometricGroup (AlgebraicClosure k),
      Lie.IsSemisimpleElement A.geometricGroup X →
        Lie.elementCentralizerLie A.geometricGroup X = ⊤) :
    IsNilpotentGroupScheme A.group := by
  obtain ⟨T, i, hi⟩ := TorusExistence.exists_isMaximalTorus A.geometricGroup
  have hT := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  apply A.isNilpotent_of_geometric_central_maximalTorus hi
  apply hT.isCentral_of_tangentCentralizers_eq_top
  intro X
  exact hcen _ ((Lie.isSemisimpleElement_of_isSplitTorus hT X).map i)

/-- If every reachable target has central geometric semisimple tangents,
characteristic division forces every fixed split-torus action on these
geometric targets to have empty roots. -/
theorem roots_eq_empty_of_geometric_semisimple_central
    (p : ℕ) [CharP k p] [ExpChar k p] (hp : 1 < p)
    (hcen : ∀ (A : SemisimpleReductionTarget G)
      (X : lieKernel A.geometricGroup (AlgebraicClosure k)),
      Lie.IsSemisimpleElement A.geometricGroup X →
        Lie.elementCentralizerLie A.geometricGroup X = ⊤)
    {T : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (hT : IsSplitTorus T.toGrp) :
    ∀ (A : SemisimpleReductionTarget G) (i : T.toGrp ⟶ A.geometricGroup),
      roots i = ∅ := by
  apply hT.roots_eq_empty_of_centralIsogeny_descent
    (fun A : SemisimpleReductionTarget G => A.geometricGroup) p hp
  intro A i
  obtain ⟨Q, q, hs, ha, hc, hq, hker⟩ :=
    exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie k p hp A.group
  let B := A.centralQuotient Q q hq
  let qbar : A.geometricGroup ⟶ B.geometricGroup :=
    (GroupScheme.baseChange (toAlgebraicClosure k)).map q
  refine ⟨B, qbar, hq.baseChange (toAlgebraicClosure k), ?_⟩
  intro X
  have hX : Lie.IsSemisimpleElement A.geometricGroup (Lie.targetMap i _ X) :=
    (Lie.isSemisimpleElement_of_isSplitTorus hT X).map i
  have hz := (Lie.targetMap_baseChange_eq_one_iff_elementCentralizerLie_eq_top
    q (hker (AlgebraicClosure k)) hX).2 (hcen A _ hX)
  apply Subtype.ext
  change X.val ≫ (i ≫ qbar).hom.hom = 1
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact congrArg Subtype.val hz

end SemisimpleReductionTarget

/-- The exact arbitrary-field isogeny reduction, retaining actual closed
torus lifting and a geometric noncentral semisimple witness. -/
theorem semisimpleIsogenyReduction : SemisimpleIsogenyReductionStatement.{u} := by
  intro k _ G _ _ _
  classical
  have hex : ∃ A : SemisimpleReductionTarget G,
      IsNilpotentGroupScheme A.group ∨
        ∃ X : lieKernel A.geometricGroup (AlgebraicClosure k),
          Lie.IsSemisimpleElement A.geometricGroup X ∧
            Lie.elementCentralizerLie A.geometricGroup X ≠ ⊤ := by
    by_contra h
    have hnil : ∀ A : SemisimpleReductionTarget G, ¬ IsNilpotentGroupScheme A.group := by
      intro A hn
      exact h ⟨A, Or.inl hn⟩
    have hcen : ∀ (A : SemisimpleReductionTarget G)
        (X : lieKernel A.geometricGroup (AlgebraicClosure k)),
        Lie.IsSemisimpleElement A.geometricGroup X →
          Lie.elementCentralizerLie A.geometricGroup X = ⊤ := by
      intro A X hX
      by_contra hn
      exact h ⟨A, Or.inr ⟨X, hX, hn⟩⟩
    let A := SemisimpleReductionTarget.identity G
    rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
    · let _ : CharZero k := hzero
      exact hnil A (A.isNilpotent_of_geometric_semisimple_central (hcen A))
    · let _ : Fact p.Prime := hp
      let _ : CharP k p := hchar
      obtain ⟨T, i, hi⟩ := TorusExistence.exists_isMaximalTorus A.geometricGroup
      have hT := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
      have hroot := SemisimpleReductionTarget.roots_eq_empty_of_geometric_semisimple_central
        p hp.out.one_lt hcen hT A i
      exact hnil A (A.isNilpotent_of_geometric_central_maximalTorus hi
        (isCentral_of_roots_eq_empty hT i hroot))
  obtain ⟨A, hA⟩ := hex
  exact ⟨A.group, A.map, A.smooth, A.affine, A.connected, A.isogeny, hA, A.lifts⟩

end Langlands.GroupScheme
