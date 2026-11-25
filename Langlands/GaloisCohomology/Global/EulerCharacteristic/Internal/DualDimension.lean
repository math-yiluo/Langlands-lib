import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Invariants of a representation and of its dual, and homomorphisms to and from a line

Let `G` be a finite group whose order is invertible in the field `k`, and `V` a finite-dimensional
representation of `G`. The averaging projection of the dual `V*` is the transpose of the averaging
projection of `V`, so the invariants of `V` and of `V*` have the same dimension
(`finrank_invariants_dual`).

For a representation `T` of dimension one and any representation `A` of an arbitrary group, the
composition `Hom(A, T) × Hom(T, A) → End(T) = k` is a perfect invariant pairing
(`homLineDualEquiv`); with the first part, `Hom_G(A, T)` and `Hom_G(T, A)` have the same dimension
when `G` is finite of invertible order (`finrank_invariants_linHom_line`). In the global Euler
characteristic this compares `H⁰(G, M') = Hom_G(M, μ_ℓ)` with `Hom_G(μ_ℓ, M)`.
-/

namespace Langlands.GaloisCohomology

open Representation Module

universe u v w

noncomputable section

section Dual

variable {k : Type u} [Field k] {G : Type v} [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- The averaging projection of the dual representation is the transpose of the averaging
projection. -/
theorem averageMap_dual (ρ : Representation k G V) :
    averageMap (dual ρ) = (averageMap ρ).dualMap := by
  ext f v
  simp only [averageMap, LinearMap.dualMap_apply, GroupAlgebra.average, map_smul, map_sum,
    asAlgebraHom_of, LinearMap.smul_apply, LinearMap.sum_apply, dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, smul_eq_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl

/-- **Invariants of the dual.** For `#G` invertible in `k`, `dim (V*)^G = dim V^G`. -/
theorem finrank_invariants_dual (ρ : Representation k G V) :
    finrank k (dual ρ).invariants = finrank k ρ.invariants := by
  rw [← (isProj_averageMap (dual ρ)).range, ← (isProj_averageMap ρ).range, averageMap_dual,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

end Dual

section Line

variable {k : Type u} [Field k] {G : Type v} [Group G] {T : Type w} [AddCommGroup T] [Module k T]
  {A : Type w} [AddCommGroup A] [Module k A] (ρT : Representation k G T) (ρA : Representation k G A)
  (t : T) (c : T →ₗ[k] k) (hc : c t = 1) (hT : ∀ y : T, y = c y • t)

/-- The pairing `Hom(A, T) → Hom(T, A)*`, `f ↦ (n ↦ c(f(n(t))))`. -/
def homLinePairing : (A →ₗ[k] T) →ₗ[k] Module.Dual k (T →ₗ[k] A) :=
  LinearMap.mk₂ k (fun f n => c (f (n t))) (fun f f' n => by simp) (fun a f n => by simp)
    (fun f n n' => by simp) (fun a f n => by simp)

theorem homLinePairing_apply (f : A →ₗ[k] T) (n : T →ₗ[k] A) :
    homLinePairing t c f n = c (f (n t)) :=
  rfl

include hc hT in
theorem homLinePairing_injective : Function.Injective (homLinePairing (A := A) t c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext a
  have h1 := LinearMap.congr_fun hf (c.smulRight a)
  rw [homLinePairing_apply, LinearMap.smulRight_apply, hc, one_smul, LinearMap.zero_apply] at h1
  rw [LinearMap.zero_apply, hT (f a), h1, zero_smul]

include hc hT in
/-- The pairing is invariant: it intertwines `Hom(A, T)` with the dual of `Hom(T, A)`. -/
theorem homLinePairing_comm (g : G) (f : A →ₗ[k] T) :
    homLinePairing t c ((linHom ρA ρT) g f) = (dual (linHom ρT ρA)) g (homLinePairing t c f) := by
  ext n
  rw [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, homLinePairing_apply,
    homLinePairing_apply, linHom_apply, linHom_apply]
  simp only [LinearMap.comp_apply, inv_inv]
  -- `g` acts on `T` by the scalar `χ = c (g t)`
  have hg : ∀ y : T, ρT g y = c (ρT g t) • y := fun y => by
    calc ρT g y = ρT g (c y • t) := by rw [← hT y]
      _ = c y • ρT g t := map_smul _ _ _
      _ = c y • (c (ρT g t) • t) := by rw [← hT (ρT g t)]
      _ = c (ρT g t) • (c y • t) := smul_comm _ _ _
      _ = c (ρT g t) • y := by rw [← hT y]
  rw [hg (f _), map_smul, smul_eq_mul, hg t]
  simp only [map_smul, smul_eq_mul, hc, mul_one]

/-- Invariants correspond under an equivariant linear equivalence. -/
theorem finrank_invariants_eq_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W)
    (e : V ≃ₗ[k] W) (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    finrank k ρ.invariants = finrank k σ.invariants := by
  have hmap : σ.invariants = ρ.invariants.map e.toLinearMap := by
    ext w
    constructor
    · intro hw
      refine ⟨e.symm w, fun g => ?_, e.apply_symm_apply w⟩
      apply e.injective
      rw [he, e.apply_symm_apply, hw g]
    · rintro ⟨v, hv, rfl⟩ g
      change σ g (e v) = e v
      rw [← he, hv g]
  rw [hmap, LinearEquiv.finrank_map_eq]

variable [Fintype G] [Invertible (Fintype.card G : k)] [FiniteDimensional k A]
  [FiniteDimensional k T]

/-- **Homomorphisms to and from a line.** For a finite group `G` of order invertible in `k`, a
representation `T` of dimension one and a finite-dimensional representation `A`:
`dim Hom_G(A, T) = dim Hom_G(T, A)`. -/
theorem finrank_invariants_linHom_line (hT1 : finrank k T = 1) :
    finrank k (linHom ρA ρT).invariants = finrank k (linHom ρT ρA).invariants := by
  let b := Module.finBasisOfFinrankEq k T hT1
  have hc : b.coord 0 (b 0) = 1 := by simp
  have hT : ∀ y : T, y = b.coord 0 y • b 0 := fun y => by
    conv_lhs => rw [← b.sum_repr y]
    simp
  have hinj := homLinePairing_injective (A := A) (b 0) (b.coord 0) hc hT
  have hdim : finrank k (A →ₗ[k] T) = finrank k (Module.Dual k (T →ₗ[k] A)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap, Module.finrank_linearMap, hT1]
    ring
  let e : (A →ₗ[k] T) ≃ₗ[k] Module.Dual k (T →ₗ[k] A) :=
    LinearMap.linearEquivOfInjective (homLinePairing (b 0) (b.coord 0)) hinj hdim
  rw [finrank_invariants_eq_of_linearEquiv (linHom ρA ρT) (dual (linHom ρT ρA)) e
    (fun g f => homLinePairing_comm ρT ρA (b 0) (b.coord 0) hc hT g f), finrank_invariants_dual]

end Line

end

end Langlands.GaloisCohomology
