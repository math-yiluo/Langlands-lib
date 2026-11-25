/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# The geometric Frobenius is not the absolute `q`-power Frobenius

Blueprint `prose-10-19` defines the semilinear automorphism
`g_Y = id_{Y₀} × Spec(γ)` of `Y = Y₀ ×_{k₀} k̄`, `γ = φ_q⁻¹` the geometric Frobenius of `k̄`, and
observes that it is distinct from the absolute `q`-power morphism of `Y`. For `Y₀ = Spec k₀`,
`Y = Spec k̄`, this is the statement that `Spec γ` is not the absolute `q`-power Frobenius
`Spec (z ↦ z ^ q)` of `Spec k̄`: otherwise `γ = φ_q`, so `φ_q² = id`, i.e. every `z ∈ k̄`
satisfies `z ^ (q²) = z`, which is impossible as `k̄` is infinite.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open FiniteField

variable (k : Type u) [Field k] [Finite k]

/-- Blueprint `prose-10-19`: Arithmetic and geometric Frobenius.

The geometric Frobenius `σ = Spec γ` of `Spec k̄` (`AlgebraicGeometry.specGeometricFrobenius`),
that is the geometric Galois Frobenius `g_Y` for `Y₀ = Spec k₀`, is distinct from the absolute
`q`-power Frobenius `Fr^{(q)}` of `Spec k̄` (`AlgebraicGeometry.Scheme.qPowerFrobenius`), where
`q = p ^ a = #k₀`. -/
theorem specGeometricFrobenius_hom_ne_qPowerFrobenius {p : ℕ} (hp : p.Prime) (a : ℕ)
    (hq : Nat.card k = p ^ a)
    (hX : (Spec (.of (AlgebraicClosure k))).IsOfCharacteristic p) :
    (specGeometricFrobenius k).asIso.hom ≠
      (Spec (.of (AlgebraicClosure k))).qPowerFrobenius hp hX a := by
  intro h
  let := Fintype.ofFinite k
  have hA : ((p : ℕ) : AlgebraicClosure k) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).hom.hom]
    exact (congrArg _ hX).trans (map_zero _)
  have h' := h.trans
    (Scheme.iterateFrobenius_Spec hp (CommRingCat.of (AlgebraicClosure k)) hA hX a)
  rw [specGeometricFrobenius_hom] at h'
  have h'' := Spec.map_injective h'
  have hz (z : AlgebraicClosure k) :
      geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) z = z ^ p ^ a :=
    congrArg (fun f : CommRingCat.of (AlgebraicClosure k) ⟶ CommRingCat.of (AlgebraicClosure k) ↦
      f.hom z) h''
  have hcard : Fintype.card k = p ^ a := by rw [← hq, Nat.card_eq_fintype_card]
  have hroot (z : AlgebraicClosure k) : z ^ (p ^ a * p ^ a) = z := by
    have := hz (frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) z)
    rw [geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply, frobeniusAlgEquivOfAlgebraic_apply, hcard] at this
    rw [pow_mul]
    exact this.symm
  have hq2 : 1 < p ^ a * p ^ a := by
    have : 1 < p ^ a := hcard ▸ Fintype.one_lt_card
    nlinarith
  have hP : (Polynomial.X ^ (p ^ a * p ^ a) - Polynomial.X : Polynomial (AlgebraicClosure k)) =
      0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    convert Set.infinite_univ (α := AlgebraicClosure k)
    ext z
    simp [hroot z]
  have := congrArg (fun P : Polynomial (AlgebraicClosure k) ↦ P.coeff 1) hP
  simp [Polynomial.coeff_X_pow, hq2.ne] at this

end AlgebraicGeometry
