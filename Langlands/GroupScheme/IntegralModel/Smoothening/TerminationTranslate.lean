import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationGamma
import Langlands.GroupScheme.IntegralModel.Smoothening.Hopf
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Reducedness of Hopf algebras by translation

Let `H` be a finitely generated commutative Hopf algebra over an algebraically closed field `k`.
Suppose that every element of square zero lies in every power of the augmentation ideal. Then `H`
is reduced.

The proof translates the hypothesis at the identity to every point. If `f ^ 2 = 0` and `f ≠ 0`,
the annihilator of `f` lies in a maximal ideal, which is the kernel of a `k`-point `g`
(Nullstellensatz). The right translate `T_g f` again has square zero, so it lies in every power of
the augmentation ideal. The Krull intersection theorem gives `r` in the augmentation ideal with
`(1 - r) T_g f = 0`. Translating back by `g⁻¹ = g ∘ S` gives an element of the annihilator of
`f` with value `1` at `g`, a contradiction. -/

noncomputable section

universe u

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

/-- The convolution of two points. -/
def conv (φ ψ : H →ₐ[k] k) : H →ₐ[k] k :=
  (Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _)).comp (comulAlgHom k H)

theorem conv_apply (φ ψ : H →ₐ[k] k) (c : H) :
    conv φ ψ c = Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _) (comul c) := rfl

/-- The value of a point on a right translate is a convolution. -/
theorem apply_rtrans (φ ψ : H →ₐ[k] k) (c : H) : ψ (rtrans φ c) = conv ψ φ c := by
  have key : ∀ w : H ⊗[k] H, ψ (Algebra.TensorProduct.rid k k H
      (Algebra.TensorProduct.map (AlgHom.id k H) φ w)) =
      Algebra.TensorProduct.lift ψ φ (fun _ _ => .all _ _) w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q => simp [mul_comm]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  rw [rtrans_apply, key, conv_apply]

/-- Right translations compose by convolution. -/
theorem rtrans_rtrans (φ ψ : H →ₐ[k] k) (c : H) :
    rtrans ψ (rtrans φ c) = rtrans (conv ψ φ) c := by
  let Θ : (H ⊗[k] H) ⊗[k] H →ₗ[k] H := (TensorProduct.rid k H).toLinearMap ∘ₗ
    TensorProduct.map ((TensorProduct.rid k H).toLinearMap ∘ₗ
      TensorProduct.map LinearMap.id ψ.toLinearMap) φ.toLinearMap
  let Θ' : H ⊗[k] (H ⊗[k] H) →ₗ[k] H := (TensorProduct.rid k H).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (Algebra.TensorProduct.lift ψ φ (fun _ _ => .all _ _)).toLinearMap
  have hA : ∀ w : H ⊗[k] H, rtrans ψ (Algebra.TensorProduct.rid k k H
      (Algebra.TensorProduct.map (AlgHom.id k H) φ w)) = Θ ((comul (R := k) (A := H)).rTensor H w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
        map_smul, LinearMap.rTensor_tmul, rtrans_apply]
      induction (comul p : H ⊗[k] H) using TensorProduct.inductionOn with
      | tmul a b => simp [Θ, smul_smul]
      | add v w hv hw => rw [map_add, map_add, smul_add, hv, hw, TensorProduct.add_tmul, map_add]
    | add v w hv hw => rw [map_add, map_add, map_add, hv, hw, map_add, map_add]
  have hB : ∀ w : H ⊗[k] H, Algebra.TensorProduct.rid k k H
      (Algebra.TensorProduct.map (AlgHom.id k H) (conv ψ φ) w) =
      Θ' ((comul (R := k) (A := H)).lTensor H w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul p q => simp [Θ', conv_apply]
    | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]
  have hC : ∀ z, Θ' (TensorProduct.assoc k H H H z) = Θ z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul ab q =>
      induction ab using TensorProduct.inductionOn with
      | tmul a b => simp [Θ, Θ', smul_smul, mul_comm]
      | add u v hu hv => rw [TensorProduct.add_tmul, map_add, map_add, hu, hv, map_add]
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  rw [rtrans_apply φ, hA, rtrans_apply (conv ψ φ), hB, ← Coalgebra.coassoc_apply, hC]

/-- The inverse of a point is its composition with the antipode. -/
theorem conv_comp_antipode (g : H →ₐ[k] k) :
    conv g (g.comp (antipodeAlgHom k H)) = counitAlgHom k H := by
  have h : Algebra.TensorProduct.lift g (g.comp (antipodeAlgHom k H)) (fun _ _ => .all _ _) =
      g.comp (Algebra.TensorProduct.lift (.id k H) (antipodeAlgHom k H) fun _ _ => .all _ _) := by
    ext <;> simp
  rw [conv, h, AlgHom.comp_assoc, lift_id_antipodeAlgHom_comp_comul, ← AlgHom.comp_assoc]
  ext c
  simp

theorem conv_antipode_comp (g : H →ₐ[k] k) :
    conv (g.comp (antipodeAlgHom k H)) g = counitAlgHom k H := by
  have h : Algebra.TensorProduct.lift (g.comp (antipodeAlgHom k H)) g (fun _ _ => .all _ _) =
      g.comp (Algebra.TensorProduct.lift (antipodeAlgHom k H) (.id k H) fun _ _ => .all _ _) := by
    ext <;> simp
  rw [conv, h, AlgHom.comp_assoc, lift_antipodeAlgHom_comp_comul, ← AlgHom.comp_assoc]
  ext c
  simp

/-- **Nullstellensatz.** Every proper ideal of a finitely generated algebra over an algebraically
closed field lies in the kernel of a point. -/
theorem exists_algHom_of_ne_top [IsAlgClosed k] [Algebra.FiniteType k H] {A : Ideal H}
    (hA : A ≠ ⊤) : ∃ g : H →ₐ[k] k, ∀ u ∈ A, g u = 0 := by
  obtain ⟨M, hM, hAM⟩ := Ideal.exists_le_maximal A hA
  let := Ideal.Quotient.field M
  have : Algebra.FiniteType k (H ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k M) (Ideal.Quotient.mkₐ_surjective k M)
  have : Module.Finite k (H ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (H ⧸ M)
  refine ⟨(IsAlgClosed.lift : H ⧸ M →ₐ[k] k).comp (Ideal.Quotient.mkₐ k M), fun u hu => ?_⟩
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (hAM hu),
    map_zero]

/-- **Reducedness by translation.** -/
theorem isReduced_of_forall_sq_eq_zero [IsAlgClosed k] [Algebra.FiniteType k H]
    (h : ∀ f : H, f ^ 2 = 0 → ∀ j : ℕ, f ∈ RingHom.ker (counitAlgHom k H) ^ j) :
    IsReduced H := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro f hf
  by_contra hf0
  set A : Ideal H := (Submodule.span H {f}).annihilator
  have hA : A ≠ ⊤ := by
    intro htop
    have h1 : (1 : H) ∈ A := htop ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hf0 h1
  obtain ⟨g, hg⟩ := exists_algHom_of_ne_top (k := k) hA
  set a := g.comp (antipodeAlgHom k H)
  set m := RingHom.ker (counitAlgHom k H)
  have hsq : rtrans g f ^ 2 = 0 := by rw [← map_pow, hf, map_zero]
  have hmem : rtrans g f ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule H H) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [smul_eq_mul, Ideal.mul_top]
    exact h _ hsq i
  obtain ⟨⟨r, hr⟩, hrf⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m (rtrans g f)).mp hmem
  have h0 : (1 - r) * rtrans g f = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hrf.symm
  have hback : rtrans a (rtrans g f) = f := by
    rw [rtrans_rtrans, conv_antipode_comp, rtrans_counit]
  have hu : rtrans a (1 - r) ∈ A := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    have := congrArg (rtrans a) h0
    rwa [map_mul, hback, map_zero] at this
  have hgu := hg _ hu
  rw [apply_rtrans, conv_comp_antipode, map_sub, map_one] at hgu
  have hr0 : counitAlgHom k H r = 0 := hr
  rw [hr0, sub_zero] at hgu
  exact one_ne_zero hgu

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
