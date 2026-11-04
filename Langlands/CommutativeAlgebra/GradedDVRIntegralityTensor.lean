import Langlands.CommutativeAlgebra.GradedDVRIntegrality
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Integrality of contracting points tested after extending the scalars

This is `GradedDVRIntegrality.integral_of_contracting` with the test set `M` taken inside
`Ω ⊗[k] B` for a `k`-vector space `Ω`, typically an algebraic closure of `k`. The integrality of
the values on `M` is measured in `Ω ⊗[k] A`, and the kernel condition uses the base-changed
points `Ω ⊗ a`. The proof reduces to `integral_of_contracting` through the coordinates with
respect to a `k`-basis of `Ω`.
-/

noncomputable section

universe u

open IsLocalRing TensorProduct

namespace Langlands.CommutativeAlgebra

namespace GradedDVRIntegrality

section Coordinates

variable {k : Type*} [Field k] {Ω : Type*} [AddCommGroup Ω] [Module k Ω] {ι : Type*}
  (ℬ : Module.Basis ι k Ω) {N P : Type*} [AddCommGroup N] [Module k N] [AddCommGroup P]
  [Module k P]

/-- The coordinates of an element of `Ω ⊗[k] N` with respect to a basis of `Ω` are natural
in `N`. -/
theorem equivFinsuppOfBasisLeft_lTensor [DecidableEq ι] (f : N →ₗ[k] P) (x : Ω ⊗[k] N)
    (i : ι) :
    equivFinsuppOfBasisLeft ℬ (f.lTensor Ω x) i = f (equivFinsuppOfBasisLeft ℬ x i) := by
  induction x with
  | tmul ω n => simp
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add,
      Finsupp.add_apply, map_add]

end Coordinates

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
  {c : B →+* LaurentPolynomial B}

/-- The weight-`n` component `b ↦ (c b).coeff n`, as a `k`-linear map. -/
def weightPart (hc : IsGrading k c) (n : ℤ) : B →ₗ[k] B where
  toFun b := (c b).coeff n
  map_add' b b' := by rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' r b := by
    rw [Algebra.smul_def, map_mul, hc.map_algebraMap, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.coeff_single_zero_mul, RingHom.id_apply, Algebra.smul_def]

theorem weightPart_apply (hc : IsGrading k c) (n : ℤ) (b : B) :
    weightPart hc n b = (c b).coeff n :=
  rfl

/-- **Integrality of a contracting point, tested after extending the scalars.** Let `B` be a
finitely generated `k`-algebra graded by `c`, with counit `ε`, and let `Ω` be a `k`-vector space.
Let `M ⊆ Ω ⊗[k] B` be stable under the base-changed weight components, such that the only
contracting `k`-point `a` with `Ω ⊗ a = Ω ⊗ ε` on `M` is `ε`. Let `A` be a DVR over `k` with
geometrically reduced residue field, and assume that every nonzero finitely generated
geometrically reduced `k`-algebra in `Type u` has a `k`-point. Then a contracting point
`ξ : B → Frac A` such that `Ω ⊗ ξ` maps `M` into the image of `Ω ⊗[k] A` satisfies
`ξ(B) ⊆ A`. -/
theorem integral_of_contracting_tensor {Ω : Type*} [AddCommGroup Ω] [Module k Ω]
    [Algebra.FiniteType k B] (hc : IsGrading k c)
    (ε : B →ₐ[k] k) (hε : ∀ b n, ε ((c b).coeff n) = if n = 0 then ε b else 0)
    (M : Set (Ω ⊗[k] B)) (hM : ∀ m ∈ M, ∀ n, (weightPart hc n).lTensor Ω m ∈ M)
    (hker : ∀ a : B →ₐ[k] k, IsContracting c ε a →
      (∀ m ∈ M, a.toLinearMap.lTensor Ω m = ε.toLinearMap.lTensor Ω m) → a = ε)
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra k A]
    (hF : Algebra.IsGeometricallyReduced k (ResidueField A))
    (hrat : ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] [Nontrivial R]
      [Algebra.IsGeometricallyReduced k R], Nonempty (R →ₐ[k] k))
    (ξ : B →ₐ[k] FractionRing A) (hξ : IsContracting c ε ξ)
    (hint : ∀ m ∈ M, ξ.toLinearMap.lTensor Ω m ∈
      LinearMap.range ((IsScalarTower.toAlgHom k A (FractionRing A)).toLinearMap.lTensor Ω)) :
    ∀ b, ξ b ∈ (algebraMap A (FractionRing A)).range := by
  classical
  let ℬ := Module.Free.chooseBasis k Ω
  let Mk : Set B := {y | ∃ m ∈ M, ∃ i, equivFinsuppOfBasisLeft ℬ m i = y}
  refine integral_of_contracting hc ε hε Mk ?_ ?_ hF hrat ξ hξ ?_
  · rintro _ ⟨m, hm, i, rfl⟩ n
    exact ⟨_, hM m hm n, i, equivFinsuppOfBasisLeft_lTensor ℬ _ m i⟩
  · intro a ha haM
    refine hker a ha fun m hm => (equivFinsuppOfBasisLeft ℬ).injective (Finsupp.ext fun i => ?_)
    rw [equivFinsuppOfBasisLeft_lTensor, equivFinsuppOfBasisLeft_lTensor]
    exact haM _ ⟨m, hm, i, rfl⟩
  · rintro _ ⟨m, hm, i, rfl⟩
    obtain ⟨z, hz⟩ := hint m hm
    refine ⟨equivFinsuppOfBasisLeft ℬ z i, ?_⟩
    have := congrArg (fun t => equivFinsuppOfBasisLeft ℬ t i) hz
    simp only [equivFinsuppOfBasisLeft_lTensor] at this
    exact this

end GradedDVRIntegrality

end Langlands.CommutativeAlgebra
