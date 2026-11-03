import Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement
import Mathlib.LinearAlgebra.Projection

/-! # Reduction of the rational root complement to split-center restriction -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.LinearAlgebra

/-- If `f ∘ g` is bijective, the kernel of `f` complements the range of `g`. -/
theorem isCompl_ker_range_of_bijective_comp
    {R M N P : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (g : N →ₗ[R] M)
    (h : Function.Bijective (f.comp g)) : IsCompl f.ker g.range := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    change f (g y) = 0 at hx
    have hy : y = 0 := h.1 (by simpa using hx)
    simp [hy]
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro x
    obtain ⟨y, hy⟩ := h.2 (f x)
    change f (g y) = f x at hy
    refine ⟨x - g y, g y, ?_, LinearMap.mem_range_self g y, sub_add_cancel _ _⟩
    change f (x - g y) = 0
    rw [map_sub, hy, sub_self]

/-- Decompose `M` as `ker f × N` when `f ∘ g` is bijective.
The forward map sends `(x, y)` to `x + g y`. -/
def kerProdEquivOfBijectiveComp
    {R M N P : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (g : N →ₗ[R] M)
    (h : Function.Bijective (f.comp g)) : (f.ker × N) ≃ₗ[R] M :=
  ((LinearEquiv.refl R f.ker).prodCongr
    (LinearEquiv.ofInjective g (fun _ _ hxy => h.1 (congrArg f hxy)))).trans
      (Submodule.prodEquivOfIsCompl f.ker g.range
        (isCompl_ker_range_of_bijective_comp f g h))

@[simp]
theorem kerProdEquivOfBijectiveComp_apply
    {R M N P : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (g : N →ₗ[R] M)
    (h : Function.Bijective (f.comp g)) (x : f.ker) (y : N) :
    kerProdEquivOfBijectiveComp f g h (x, y) = x + g y := rfl

end Langlands.LinearAlgebra

universe u

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- Rationalized character restriction respects composition contravariantly. -/
theorem rationalCharacterRestrictRat_comp (g : K ⟶ H) (f : H ⟶ G) :
    rationalCharacterRestrictRat (g ≫ f) =
      (rationalCharacterRestrictRat g).comp (rationalCharacterRestrictRat f) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q χ
  change q ⊗ₜ[ℤ] characterRestrict (g ≫ f) χ =
    q ⊗ₜ[ℤ] characterRestrict g (characterRestrict f χ)
  rw [characterRestrict_comp, AddMonoidHom.comp_apply]

variable {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- The root complement follows from the split-center kernel comparison and
bijectivity of rational character restriction to that center. -/
theorem relativeRootSpan_isCompl_of_centralKernel
    (i : T.toGrp ⟶ G) (a : A.toGrp ⟶ G) (f : A ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ i = a)
    (hker : (rationalCharacterRestrictRat (CommGroupScheme.groupHom f)).ker =
      relativeRootSpan i)
    (ha : Function.Bijective (rationalCharacterRestrictRat a)) :
    IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range := by
  rw [← hker]
  apply Langlands.LinearAlgebra.isCompl_ker_range_of_bijective_comp
  rw [← rationalCharacterRestrictRat_comp, hf]
  exact ha

end Langlands.GroupScheme
