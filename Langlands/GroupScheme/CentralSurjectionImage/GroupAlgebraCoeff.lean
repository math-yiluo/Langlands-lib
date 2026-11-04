import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Coefficients of group algebras over `Λ × Λ`

Coefficient formulas for the images of `S[Λ]` in `S[Λ × Λ]` along the diagonal and the two
inclusions, and for convolutions of algebra maps into `S[Λ]` pushed into the two factors.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

variable {k : Type u} [CommRing k] {S : Type u} [CommRing S] [Algebra k S]
  {Λ : Type u} [AddCommGroup Λ]

/-- The diagonal `γ ↦ (γ, γ)`. -/
abbrev diagonal (Λ : Type u) [AddCommGroup Λ] : Λ →+ Λ × Λ :=
  (AddMonoidHom.id Λ).prod (AddMonoidHom.id Λ)

/-- The `(γ, δ)`-coefficient of the diagonal image of `x`. -/
theorem coeff_mapDomain_diag [DecidableEq Λ] (x : AddMonoidAlgebra S Λ) (γ δ : Λ) :
    (AddMonoidAlgebra.mapDomain (diagonal Λ) x).coeff (γ, δ) =
      if γ = δ then x.coeff γ else 0 := by
  change (Finsupp.mapDomain (diagonal Λ) x.coeff) (γ, δ) = _
  split_ifs with hγδ
  · subst hγδ
    exact Finsupp.mapDomain_apply_of_injective
      (show Function.Injective (diagonal Λ) from fun a a' h => congrArg Prod.fst h) _ γ
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    apply hγδ
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    simp only [AddMonoidHom.prod_apply, AddMonoidHom.id_apply] at h1 h2
    rw [← h1, ← h2]

/-- Separated monomials: the `(γ, δ)`-coefficient of `x(X) y(Y)` in `S[Λ × Λ]`. -/
theorem coeff_mapDomain_inl_mul_inr (x y : AddMonoidAlgebra S Λ) (γ δ : Λ) :
    (AddMonoidAlgebra.mapDomain (AddMonoidHom.inl Λ Λ) x *
        AddMonoidAlgebra.mapDomain (AddMonoidHom.inr Λ Λ) y).coeff (γ, δ) =
      x.coeff γ * y.coeff δ := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [AddMonoidAlgebra.mapDomain_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx,
      hx', AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
  | single a r =>
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' =>
      rw [AddMonoidAlgebra.mapDomain_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        hy, hy', AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
    | single c t =>
      rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single]
      simp only [AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero,
        zero_add, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Prod.mk.injEq]
      split_ifs <;> simp_all


variable (k) in
/-- The `γ`-coefficient of the group algebra, as a `k`-linear map. -/
def coeffL (γ : Λ) : AddMonoidAlgebra S Λ →ₗ[k] S where
  toFun x := x.coeff γ
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The `(γ, δ)`-coefficient of the convolution of an algebra map `c` pushed into the two factors
of `S[Λ × Λ]` is the convolution of its coefficient functionals. -/
theorem coeff_productMap_inl_inr' {B : Type u} [CommRing B] [Algebra k B]
    (c : B →ₐ[k] AddMonoidAlgebra S Λ) (γ δ : Λ) (t : B ⊗[k] B) :
    ((Algebra.TensorProduct.productMap
        ((AddMonoidAlgebra.mapDomainAlgHom k S (AddMonoidHom.inl Λ Λ)).comp c)
        ((AddMonoidAlgebra.mapDomainAlgHom k S (AddMonoidHom.inr Λ Λ)).comp c))
          t).coeff (γ, δ) =
      LinearMap.mul' k S (TensorProduct.map (coeffL k γ ∘ₗ c.toLinearMap)
        (coeffL k δ ∘ₗ c.toLinearMap) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact coeff_mapDomain_inl_mul_inr _ _ γ δ
  | add x y hx hy => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, map_add,
      map_add]

end Langlands.GroupScheme.CentralSurjectionImage
