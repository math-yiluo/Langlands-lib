import Langlands.Algebra.PTorsionHopf.Verschiebung
import Langlands.GroupScheme.Chevalley.RegularSubspace
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # The augmentation ideal of the convolution dual and conilpotence -/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace Langlands.Algebra.PTorsionHopf

open Langlands.GroupScheme.AffineLinearEmbedding Langlands.GroupScheme.Chevalley

/-- An ideal consisting of elements nilpotent modulo an ideal of finite codimension has a
power inside that ideal. -/
theorem exists_pow_le_of_finite_quotient {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    (K I : Ideal R) [Module.Finite k (R ⧸ K)] (hI : ∀ x ∈ I, ∃ n : ℕ, x ^ n ∈ K) :
    ∃ N : ℕ, I ^ N ≤ K := by
  have : IsNoetherianRing (R ⧸ K) :=
    isNoetherian_of_tower k (inferInstance : IsNoetherian k (R ⧸ K))
  have hfg : (I.map (Ideal.Quotient.mk K)).FG := IsNoetherian.noetherian _
  have hnil : I.map (Ideal.Quotient.mk K) ≤ nilradical (R ⧸ K) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    obtain ⟨n, hn⟩ := hI y hy
    exact ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hn]; exact Ideal.zero_mem _⟩
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hnil
  refine ⟨N, fun θ hθ => ?_⟩
  have hmem : Ideal.Quotient.mk K θ ∈ I.map (Ideal.Quotient.mk K) ^ N := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hθ
  rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hmem

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A]

/-- Evaluation at `1` on the convolution dual is a ring homomorphism. -/
def evalOne : WithConv (A →ₗ[k] k) →+* k where
  toFun ξ := ξ 1
  map_one' := convOne_apply_one
  map_mul' ξ η := by
    change (ξ * η) 1 = ξ 1 * η 1
    rw [LinearMap.convMul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalOne_apply (ξ : WithConv (A →ₗ[k] k)) : evalOne ξ = ξ 1 := rfl

/-- The augmentation ideal of the convolution dual: functionals vanishing at `1`. -/
def augIdeal : Ideal (WithConv (A →ₗ[k] k)) := RingHom.ker evalOne

theorem mem_augIdeal {ξ : WithConv (A →ₗ[k] k)} : ξ ∈ augIdeal (k := k) (A := A) ↔ ξ 1 = 0 :=
  RingHom.mem_ker

/-- Convolution is evaluation of the first factor at a right translate. -/
theorem convMul_apply_eq_rightAct (θ η : WithConv (A →ₗ[k] k)) (b : A) :
    (θ * η) b = θ (rightAct η.ofConv b) := by
  rw [rightAct_apply, LinearMap.convMul_apply]
  generalize (comul (R := k) b : A ⊗[k] A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]

variable [IsCocomm k A]

/-- Functionals vanishing on a right-translation stable subspace form an ideal. -/
def annIdeal (W : Submodule k A) (hW : ∀ (f : Module.Dual k A) (w : A), w ∈ W → rightAct f w ∈ W) :
    Ideal (WithConv (A →ₗ[k] k)) where
  carrier := {θ | ∀ w ∈ W, θ w = 0}
  add_mem' {θ η} hθ hη w hw := by
    change (θ.ofConv + η.ofConv) w = 0
    rw [LinearMap.add_apply]
    change θ w + η w = 0
    rw [hθ w hw, hη w hw, add_zero]
  zero_mem' w _ := rfl
  smul_mem' c θ hθ w hw := by
    rw [smul_eq_mul, mul_comm, convMul_apply_eq_rightAct]
    exact hθ _ (hW _ _ hw)

theorem mem_annIdeal {W : Submodule k A} {hW} {θ : WithConv (A →ₗ[k] k)} :
    θ ∈ annIdeal W hW ↔ ∀ w ∈ W, θ w = 0 := Iff.rfl

/-- Restriction of functionals to a subspace. -/
def restrictDual (W : Submodule k A) : WithConv (A →ₗ[k] k) →ₗ[k] Module.Dual k W :=
  W.subtype.dualMap ∘ₗ (WithConv.linearEquiv k (A →ₗ[k] k)).toLinearMap

omit [IsCocomm k A] in
theorem restrictDual_apply (W : Submodule k A) (θ : WithConv (A →ₗ[k] k)) (w : W) :
    restrictDual W θ w = θ w := rfl

/-- The quotient of the dual by the annihilator of a finite-dimensional stable subspace is
finite-dimensional. -/
theorem finite_quotient_annIdeal (W : Submodule k A) [FiniteDimensional k W] (hW) :
    Module.Finite k (WithConv (A →ₗ[k] k) ⧸ annIdeal W hW) := by
  let K := (annIdeal W hW).restrictScalars k
  have hK : K ≤ LinearMap.ker (restrictDual W) := fun θ hθ => by
    rw [LinearMap.mem_ker]
    ext w
    exact hθ w w.2
  have hinj : Function.Injective (K.liftQ (restrictDual W) hK) := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun θ hθ w hw => ?_
    rw [LinearMap.mem_ker] at hθ
    exact LinearMap.congr_fun hθ ⟨w, hw⟩
  have : Module.Finite k (WithConv (A →ₗ[k] k) ⧸ K) := Module.Finite.of_injective _ hinj
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv k (annIdeal W hW))

variable (p : ℕ)

/-- **Conilpotence.** If every functional vanishing at `1` has vanishing `p`-th convolution
power, every element is killed by some power of the augmentation ideal. -/
theorem exists_pow_augIdeal_apply_eq_zero
    (hV : ∀ ξ ∈ augIdeal (k := k) (A := A), ξ ^ p = 0) (a : A) :
    ∃ N : ℕ, ∀ θ ∈ augIdeal (k := k) (A := A) ^ N, θ a = 0 := by
  classical
  have hW : ∀ (f : Module.Dual k A) (w : A), w ∈ regularSpan (K := k) ({a, 1} : Finset A) →
      rightAct f w ∈ regularSpan (K := k) ({a, 1} : Finset A) :=
    fun f w hw => rightAct_mem_regularSpan _ f hw
  have : Module.Finite k (WithConv (A →ₗ[k] k) ⧸ annIdeal _ hW) :=
    finite_quotient_annIdeal _ hW
  obtain ⟨N, hN⟩ := exists_pow_le_of_finite_quotient (k := k) (annIdeal _ hW) augIdeal
    fun ξ hξ => ⟨p, by rw [hV ξ hξ]; exact Ideal.zero_mem _⟩
  exact ⟨N, fun θ hθ => hN hθ a (subset_regularSpan _ (by simp))⟩

end Langlands.Algebra.PTorsionHopf
