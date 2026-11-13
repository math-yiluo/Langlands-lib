import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceStep
import Langlands.AlgebraicGeometry.Deformation.ArtinianQuotients
import Langlands.CategoryTheory.Sites.PseudofunctorPointedTransport

/-! # Minimality of the actual Picard source successor -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceMinimality

open Langlands.AlgebraicGeometry.Deformation Langlands.CategoryTheory
open ArtinianTest ArtinianTest.ElementaryKernel ArtinianPicardSourceStep

section Inverse

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]

/-- The inverse test arrow of a test arrow with bijective algebra map. -/
def invOfBijective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Bijective (toAlgHom q)) : B ⟶ A :=
  homMk (AlgEquiv.ofBijective (toAlgHom q) hq).symm.toAlgHom (by
    ext x
    conv_rhs => rw [← (AlgEquiv.ofBijective (toAlgHom q) hq).apply_symm_apply x]
    exact (DFunLike.congr_fun (augmentation_comp q)
      ((AlgEquiv.ofBijective (toAlgHom q) hq).symm x)).symm)

lemma invOfBijective_comp {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Bijective (toAlgHom q)) : invOfBijective q hq ≫ q = 𝟙 B :=
  ArtinianTest.hom_ext (by
    ext x
    exact (AlgEquiv.ofBijective (toAlgHom q) hq).apply_symm_apply x)

lemma comp_invOfBijective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Bijective (toAlgHom q)) : q ≫ invOfBijective q hq = 𝟙 A :=
  ArtinianTest.hom_ext (by
    ext x
    exact (AlgEquiv.ofBijective (toAlgHom q) hq).symm_apply_apply x)

end Inverse

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s : Stage ε f M)

lemma pointedMap_comp {A B C : ArtinianTest k K} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (hc : a ≫ b = c) : pointedMap b ≫ pointedMap a = pointedMap c := by
  subst hc
  apply Under.UnderMorphism.ext
  exact baseMap_comp a b

/- The elementary and residue-module structures on the canonical source reduction are the
instances of `ArtinianPicardSourceStep`, so that statements here agree syntactically with
`Stage.quotient_lift_iff`. -/
attribute [local instance] Stage.instFactIsElementarySurjectionSourceReduction
  Stage.instModuleSubtypeCarrierAlgebraSourceTestMemIdealKernelSourceReduction

section Factor

variable {C' : ArtinianTest k K} (τ : s.sourceTest ε hε f M ⟶ C') (ρ : C' ⟶ s.test)
  (hρ : τ ≫ ρ = s.sourceReduction ε hε f M)

omit [Flat f] [IsProper f] in
include hρ in
lemma toAlgHom_sourceReduction_eq_zero (a : (s.sourceTest ε hε f M).algebra)
    (ha : toAlgHom τ a = 0) : toAlgHom (s.sourceReduction ε hε f M) a = 0 := by
  rw [← hρ, toAlgHom_comp, AlgHom.comp_apply, ha, map_zero]

/-- The kernel subspace of a map from the canonical source extension. -/
def kernelSubspace : Submodule K (Kernel (s.sourceReduction ε hε f M)) where
  carrier := {x | toAlgHom τ x.val = 0}
  add_mem' := by
    intro x y hx hy
    change toAlgHom τ (x.val + y.val) = 0
    rw [map_add, hx, hy, add_zero]
  zero_mem' := map_zero _
  smul_mem' := by
    intro c x hx
    obtain ⟨a, rfl⟩ := (s.sourceTest ε hε f M).augmentation_surjective c
    change toAlgHom τ ((s.sourceTest ε hε f M).augmentation a • x).val = 0
    rw [augmentation_smul (s.sourceReduction ε hε f M) Fact.out a x]
    change toAlgHom τ (a * x.val) = 0
    rw [map_mul]
    rw [hx, mul_zero]

omit [Flat f] [IsProper f] in
include hρ in
lemma subspaceIdeal_kernelSubspace :
    ElementaryKernelSubspaceQuotient.subspaceIdeal (s.sourceReduction ε hε f M)
        (kernelSubspace ε hε f M s τ) = RingHom.ker (toAlgHom τ).toRingHom := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨⟨a, toAlgHom_sourceReduction_eq_zero ε hε f M s τ ρ hρ a ha⟩, ha, rfl⟩

/-- The induced map from the kernel quotient test. -/
def kernelLift : ElementaryKernelSubspaceQuotient.test (s.sourceReduction ε hε f M)
    (kernelSubspace ε hε f M s τ) ⟶ C' :=
  quotientLift τ _ (ElementaryKernelSubspaceQuotient.subspaceIdeal_le_augmentation _ _)
    (subspaceIdeal_kernelSubspace ε hε f M s τ ρ hρ).le

omit [Flat f] [IsProper f] in
lemma kernelLift_bijective (hτ : Function.Surjective (toAlgHom τ)) :
    Function.Bijective (toAlgHom (kernelLift ε hε f M s τ ρ hρ)) :=
  ⟨quotientLift_injective τ _ _ _ (subspaceIdeal_kernelSubspace ε hε f M s τ ρ hρ).symm,
    quotientLift_surjective τ _ _ _ hτ⟩

omit [Flat f] [IsProper f] in
lemma projection_kernelLift :
    ElementaryKernelSubspaceQuotient.projection (s.sourceReduction ε hε f M)
        (kernelSubspace ε hε f M s τ) ≫ kernelLift ε hε f M s τ ρ hρ = τ :=
  quotientMap_lift τ _ _ _

omit [Flat f] [IsProper f] in
lemma kernelLift_comp :
    kernelLift ε hε f M s τ ρ hρ ≫ ρ = ElementaryKernelSubspaceQuotient.reduction
      (s.sourceReduction ε hε f M) (kernelSubspace ε hε f M s τ) := by
  apply ArtinianTest.hom_ext
  apply Ideal.Quotient.algHom_ext
  change (toAlgHom ρ).comp (toAlgHom τ) = toAlgHom (s.sourceReduction ε hε f M)
  rw [← toAlgHom_comp, hρ]

include hρ in
/-- Minimality of the successor stage: if the obstruction subspace of the old stage lies
in the kernel subspace of a map from the canonical source extension (equivalently, by
`Stage.quotient_lift_iff`, the old family has a pointed lift over the kernel quotient
test), then that map factors through the successor test. -/
theorem exists_next_factor
    (hle : s.obstructionSubspace ε hε f M ≤ kernelSubspace ε hε f M s τ) :
    ∃ ψ : (s.next ε hε f M).test ⟶ C',
      (toAlgHom ψ).comp (s.next ε hε f M).cover =
        (toAlgHom τ).comp (s.sourceProjection ε hε f M) ∧
      ψ ≫ ρ = s.reduction ε hε f M := by
  have hIJ : ElementaryKernelSubspaceQuotient.subspaceIdeal (s.sourceReduction ε hε f M)
        (s.obstructionSubspace ε hε f M) ≤
      ElementaryKernelSubspaceQuotient.subspaceIdeal (s.sourceReduction ε hε f M)
        (kernelSubspace ε hε f M s τ) := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x, hle hx, rfl⟩
  let φ := quotientFactor (s.sourceTest ε hε f M)
    (ElementaryKernelSubspaceQuotient.subspaceIdeal_le_augmentation _
      (s.obstructionSubspace ε hε f M))
    (ElementaryKernelSubspaceQuotient.subspaceIdeal_le_augmentation _
      (kernelSubspace ε hε f M s τ)) hIJ
  refine ⟨φ ≫ kernelLift ε hε f M s τ ρ hρ, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    rfl
  · rw [Category.assoc, kernelLift_comp]
    apply ArtinianTest.hom_ext
    apply Ideal.Quotient.algHom_ext
    rfl

omit [Flat f] [IsProper f] in
include hρ in
/-- Over the kernel quotient test of a surjective `τ`, a pointed family over `C'` restricting
along `ρ` to the old family gives a pointed family restricting to the old family. -/
theorem exists_kernelQuotient_lift (hτ : Function.Surjective (toAlgHom τ))
    (Z : ArtinianTestDeformations.Deformations f M C')
    (e : (ArtinianTestDeformations.restrict f M ρ).obj Z ≅ s.family) :
    ∃ N : ArtinianTestDeformations.Deformations f M
      (ElementaryKernelSubspaceQuotient.test (s.sourceReduction ε hε f M)
        (kernelSubspace ε hε f M s τ)),
      Nonempty ((ArtinianTestDeformations.restrict f M
        (ElementaryKernelSubspaceQuotient.reduction (s.sourceReduction ε hε f M)
          (kernelSubspace ε hε f M s τ))).obj N ≅ s.family) := by
  let κinv := invOfBijective (kernelLift ε hε f M s τ ρ hρ)
    (kernelLift_bijective ε hε f M s τ ρ hρ hτ)
  have hκ : κinv ≫ ElementaryKernelSubspaceQuotient.reduction (s.sourceReduction ε hε f M)
      (kernelSubspace ε hε f M s τ) = ρ := by
    rw [← kernelLift_comp ε hε f M s τ ρ hρ, ← Category.assoc, invOfBijective_comp,
      Category.id_comp]
  exact PseudofunctorPointedTransport.exists_restrict_of_comp (relative f)
    (T₀ := ArtinianTest.residueBase k K) (Core.mk M) _ _ _
    (pointedMap_comp κinv _ ρ hκ) Z s.family e

include hρ in
/-- Minimality of the successor stage in terms of pointed families: if `τ` is surjective
and some pointed family over `C'` restricts along `ρ` to the old family, then `τ` factors
through the successor test. -/
theorem exists_next_factor_of_extension (hτ : Function.Surjective (toAlgHom τ))
    (Z : ArtinianTestDeformations.Deformations f M C')
    (e : (ArtinianTestDeformations.restrict f M ρ).obj Z ≅ s.family) :
    ∃ ψ : (s.next ε hε f M).test ⟶ C',
      (toAlgHom ψ).comp (s.next ε hε f M).cover =
        (toAlgHom τ).comp (s.sourceProjection ε hε f M) ∧
      ψ ≫ ρ = s.reduction ε hε f M :=
  exists_next_factor ε hε f M s τ ρ hρ ((s.quotient_lift_iff ε hε f M _).mp
    (exists_kernelQuotient_lift ε hε f M s τ ρ hρ hτ Z e))

end Factor

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceMinimality
