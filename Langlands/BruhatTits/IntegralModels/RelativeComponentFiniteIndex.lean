import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.GroupScheme.IdentityComponentRationalQuotient
import Langlands.GroupScheme.RelativeIdentityComponentFiberComparison
import Langlands.GroupScheme.FiniteEtaleImage

/-! # Neutral integral sections have finite index over a local base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelData

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (D : RelativeComponentModelData R K G)

/-- The closed point of the actual base spectrum. -/
abbrev closedBasePoint (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (CommRingCat.of R) :=
  IsLocalRing.closedPoint R

/-- An integral section whose closed point lands in the open image of the
neutral model factors through the neutral model. -/
theorem mem_neutralSections_of_closedPoint (z : D.full.integralSections)
    (hz : z.left (closedBasePoint R) ∈ Set.range D.inclusion.hom.hom.hom.left) :
    z ∈ D.neutralSections := by
  have : IsOpenImmersion D.inclusion.hom.hom.hom.left :=
    D.isRelativeComponent.isOpenImmersion
  have hrange : Set.range z.left ⊆ Set.range D.inclusion.hom.hom.hom.left := by
    rintro _ ⟨p, rfl⟩
    have hsp : p ⤳ closedBasePoint R :=
      IsLocalRing.specializes_closedPoint (R := R) p
    exact (hsp.map z.left.continuous).mem_open
      D.inclusion.hom.hom.hom.left.isOpenEmbedding.isOpen_range hz
  exact ⟨FiniteEtaleImage.liftOver D.inclusion.hom.hom.hom z hrange,
    FiniteEtaleImage.liftOver_fac _ _ _⟩

/-- The actual full residue fibre at the closed point of the base. -/
abbrev closedResidueFibre :
    GroupScheme (Spec ((Spec (CommRingCat.of R)).residueField (closedBasePoint R))) :=
  RelativeIdentityComponent.residueFiber D.full.group (closedBasePoint R)

/-- Restriction of integral sections to the closed residue fibre. -/
def closedReduction :
    D.full.integralSections →*
      (Over.mk (𝟙 (Spec ((Spec (CommRingCat.of R)).residueField (closedBasePoint R)))) ⟶
        D.closedResidueFibre.X) :=
  baseChangeSectionHom ((Spec (CommRingCat.of R)).fromSpecResidueField (closedBasePoint R))
    D.full.group

/-- The fibre inclusion carries the residue point of a reduced section to the
closed-point value of the section. -/
theorem fiberι_closedReduction (z : D.full.integralSections)
    (p : Spec ((Spec (CommRingCat.of R)).residueField (closedBasePoint R))) :
    D.full.group.X.hom.fiberι (closedBasePoint R) ((D.closedReduction z).left p) =
      z.left (closedBasePoint R) := by
  have h := baseChangeSectionHom_fst
    ((Spec (CommRingCat.of R)).fromSpecResidueField (closedBasePoint R)) D.full.group z
  have h' := congrArg (fun f => f p) h
  have hp : (Spec (CommRingCat.of R)).fromSpecResidueField (closedBasePoint R) p =
      closedBasePoint R :=
    Scheme.fromSpecResidueField_apply _ _
  simp only [Scheme.Hom.comp_apply] at h'
  exact h'.trans (congrArg (fun q => z.left q) hp)

instance closedResidueFibre_smooth : Smooth D.closedResidueFibre.X.hom := by
  have : Smooth D.full.group.X.hom := D.full_smooth
  exact inferInstanceAs (Smooth (pullback.snd D.full.group.X.hom
    ((Spec (CommRingCat.of R)).fromSpecResidueField (closedBasePoint R))))

instance closedResidueFibre_isAffineHom : IsAffineHom D.closedResidueFibre.X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd D.full.group.X.hom
    ((Spec (CommRingCat.of R)).fromSpecResidueField (closedBasePoint R))))

/-- Integral sections whose closed residue section lies in the rational identity
component subgroup of the closed fibre. -/
def closedComponentKernel : Subgroup D.full.integralSections :=
  (IdentityComponent.rationalIdentitySubgroup D.closedResidueFibre).comap D.closedReduction

theorem closedComponentKernel_le_neutralSections :
    D.closedComponentKernel ≤ D.neutralSections := by
  intro z hz
  have hz' : D.closedReduction z ∈
      IdentityComponent.rationalIdentitySubgroup D.closedResidueFibre := hz
  obtain ⟨y, hy⟩ := (IdentityComponent.mem_rationalIdentitySubgroup _ _).mp hz'
  apply D.mem_neutralSections_of_closedPoint z
  have hmem : (D.closedReduction z).left (IdentityComponent.basePoint _) ∈
      IdentityComponent.identitySet D.closedResidueFibre := by
    rw [IdentityComponent.identitySet, ← IdentityComponent.range_identityComponentι]
    refine ⟨y.left (IdentityComponent.basePoint _), ?_⟩
    rw [← hy]
    rfl
  have key := RelativeIdentityComponent.preimage_range_inclusion_eq_identitySet
    D.full.group D.inclusion.hom D.isRelativeComponent (closedBasePoint R)
  have hpre := (Set.ext_iff.mp key _).mpr hmem
  rw [Set.mem_preimage, D.fiberι_closedReduction z] at hpre
  exact hpre

instance closedComponentKernel_finiteIndex : D.closedComponentKernel.FiniteIndex := by
  have hfin : (IdentityComponent.rationalIdentitySubgroup D.closedResidueFibre).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (IdentityComponent.finite_rationalComponentQuotient D.closedResidueFibre)
  unfold closedComponentKernel
  infer_instance

/-- **Finite index.** The neutral integral sections have finite index in all
integral sections of a smooth full model over a local domain. -/
instance neutralSections_finiteIndex : D.neutralSections.FiniteIndex :=
  Subgroup.finiteIndex_of_le D.closedComponentKernel_le_neutralSections

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelData
