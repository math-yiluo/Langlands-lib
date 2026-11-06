import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphFactorProjections
import Langlands.GroupScheme.Absolute.TripleCellIsomorphism

/-! # Comparison graph isomorphisms from the actual factor maps -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}

local instance factorIso_affine_of_affineHom {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

namespace SimpleComparisonGraph

variable (D : SimpleComparisonGraph i₁ i₂)

section TargetCentralizer

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hroots : roots i₁ = roots i)
    (hG : IsConnectedReductive G) (hi : IsMaximalTorus i)

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
include hroots hG hi in
/-- The actual common torus represents the full middle factor in either target. -/
theorem targetCentralizerRep :
    (Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i)).IsRepresentedBy i := by
  have hν : IsGenericCocharacter i D.directions.chamber := by
    intro a ha
    apply D.directions.generic a
    change a ∈ roots i₁
    rw [hroots]
    exact ha
  have hself := maximalTorusCentralizer_of_structuralInputs dynamicCentralizerReductive
    noTorusUnipotent solvableTorusQuotient k G hG T i hi
  have hZ := (genericCentralizer k G hG T i (hi.isMaximalSplitTorus D.split)
    D.directions.chamber hν).trans hself
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  exact ⟨Over.mono_of_mono_left _, hZ.symm⟩

end TargetCentralizer

namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)

section Projection

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : T.toGrp ⟶ G) (p : D.envelope.group ⟶ G)
    (ht : D.envelope.torusLift ≫ p = i)
    (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i)).IsRepresentedBy i)
    (positive : UnipotentProjectionData p E.positive.inclusion D.directions.chamber i)
    (negative : UnipotentProjectionData p E.negative.inclusion (-D.directions.chamber) i)
    [IsIso positive.hom] [IsIso negative.hom]

set_option maxHeartbeats 800000 in
/-- The actual projection is an isomorphism once its two full unipotent
restrictions are isomorphisms and the common torus is the middle factor. -/
def projectionIso : D.envelope.group ≅ G := by
  have hMG : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      (CommGroupScheme.groupHom D.directions.chamber ≫ i))).IsRepresentedBy
      (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom (-D.directions.chamber) ≫ i)) := by
    change (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom D.directions.chamber ≫ i))).IsRepresentedBy _
    rw [← groupHom_neg_comp_eq_oppositeCocharacter]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom _
  exact Dynamic.isoOfTripleCellIsomorphisms
    (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift)
    (CommGroupScheme.groupHom D.directions.chamber ≫ i)
    E.negativeRep E.torusRep E.positiveRep hMG hZ
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    p (asIso negative.hom) (Iso.refl T.toGrp) (asIso positive.hom)
    negative.comp (by simpa only [Iso.refl_hom, Category.id_comp] using ht.symm) positive.comp

/-- The constructed isomorphism has the supplied actual projection as its map. -/
@[simp]
theorem projectionIso_hom : (E.projectionIso i p ht hZ positive negative).hom = p := rfl

end Projection

variable (F : D.GraphFactorProjections E)

section First

variable (hG₁ : IsConnectedReductive G₁) (hi₁ : IsMaximalTorus i₁)
    [IsIso F.positiveFirst.hom] [IsIso F.negativeFirst.hom]

/-- Assemble the first actual graph projection from its actual factor isomorphisms. -/
def firstProjectionIso : D.envelope.group ≅ G₁ := by
  let : ConnectedSpace G₁.X.left := hG₁.connectedSpace
  exact E.projectionIso i₁ D.envelope.first D.envelope.torusLift_first
    (D.targetCentralizerRep i₁ rfl hG₁ hi₁) F.positiveFirst F.negativeFirst

@[simp]
theorem firstProjectionIso_hom : (E.firstProjectionIso F hG₁ hi₁).hom = D.envelope.first := rfl

include E F hG₁ hi₁ in
theorem isIso_first_of_factorIsomorphisms : IsIso D.envelope.first := by
  exact inferInstanceAs (IsIso (E.firstProjectionIso F hG₁ hi₁).hom)

end First

section Second

variable (hG₂ : IsConnectedReductive G₂) (hi₂ : IsMaximalTorus i₂)
    (hroots : roots i₁ = roots i₂)
    [IsIso F.positiveSecond.hom] [IsIso F.negativeSecond.hom]

/-- Assemble the second actual graph projection from its actual factor isomorphisms. -/
def secondProjectionIso : D.envelope.group ≅ G₂ := by
  let : ConnectedSpace G₂.X.left := hG₂.connectedSpace
  exact E.projectionIso i₂ D.envelope.second D.envelope.torusLift_second
    (D.targetCentralizerRep i₂ hroots hG₂ hi₂) F.positiveSecond F.negativeSecond

@[simp]
theorem secondProjectionIso_hom :
    (E.secondProjectionIso F hG₂ hi₂ hroots).hom = D.envelope.second := rfl

include E F hG₂ hi₂ hroots in
theorem isIso_second_of_factorIsomorphisms : IsIso D.envelope.second := by
  exact inferInstanceAs (IsIso (E.secondProjectionIso F hG₂ hi₂ hroots).hom)

end Second

variable (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (hi₁ : IsMaximalTorus i₁) (hi₂ : IsMaximalTorus i₂)
    (hroots : roots i₁ = roots i₂)
    [IsIso F.positiveFirst.hom] [IsIso F.negativeFirst.hom]
    [IsIso F.positiveSecond.hom] [IsIso F.negativeSecond.hom]

/-- The resulting actual ambient comparison once the four factor maps are invertible. -/
def comparisonIso : G₁ ≅ G₂ := by
  let : IsIso D.envelope.first := E.isIso_first_of_factorIsomorphisms F hG₁ hi₁
  let : IsIso D.envelope.second := E.isIso_second_of_factorIsomorphisms F hG₂ hi₂ hroots
  exact D.envelope.comparisonIso

/-- The comparison obtained from the factor maps respects the supplied torus. -/
theorem torus_comparisonIso :
    i₁ ≫ (E.comparisonIso F hG₁ hG₂ hi₁ hi₂ hroots).hom = i₂ := by
  let : IsIso D.envelope.first := E.isIso_first_of_factorIsomorphisms F hG₁ hi₁
  let : IsIso D.envelope.second := E.isIso_second_of_factorIsomorphisms F hG₂ hi₂ hroots
  exact D.envelope.torus_comparisonIso

end GraphDynamicFactors

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
