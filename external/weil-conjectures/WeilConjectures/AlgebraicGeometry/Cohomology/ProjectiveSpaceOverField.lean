/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceSerrePairing

/-!
# The cohomology of the twisting sheaves on projective space over a field

Let `k` be a field and `ℙᵈ_k = ℙ(n; Spec k)` with `d + 1` homogeneous coordinates. This file
gives the canonical `k`-linear isomorphisms of Serre's computation of the cohomology of the
twisting sheaves `𝒪(m)`, for the `k`-vector space structure
`AlgebraicGeometry.Scheme.Modules.moduleHOfField` on sheaf cohomology:

* `H⁰(ℙᵈ_k, 𝒪(m)) ≅ k[x₀, …, x_d]_m` for `m ≥ 0`, sending a class to the homogeneous polynomial
  whose section it is;
* `Hᵈ(ℙᵈ_k, 𝒪(m)) ≅ (k[x₀, …, x_d]_{-m-d-1})^∨` for `m ≤ -d - 1`, induced by the Serre pairing
  and the trace `Hᵈ(ℙᵈ_k, 𝒪(-d-1)) ≅ k`.

They are the specialisations to `A = k` of the isomorphisms over a commutative ring `A` of
`WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceSerrePairing`. The existence
statements of `lemma-coherent-base-change-invertible-sheaves--1` follow.

## Main definitions and statements

- `AlgebraicGeometry.ProjectiveSpace.twistHZeroLinearEquivOfField`: `H⁰(ℙᵈ_k, 𝒪(m)) ≅ k[x]_m`.
- `AlgebraicGeometry.ProjectiveSpace.twistHTopLinearEquivDualOfField`:
  `Hᵈ(ℙᵈ_k, 𝒪(m)) ≅ (k[x]_{-m-d-1})^∨`, described by the Serre pairing in
  `AlgebraicGeometry.ProjectiveSpace.twistHTopLinearEquivDualOfField_apply`.
- `AlgebraicGeometry.ProjectiveSpace.nonempty_H_zero_twist_equiv` and
  `AlgebraicGeometry.ProjectiveSpace.nonempty_H_twist_top_equiv_dual`: the existence statements.
  The vanishing statements are `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne`
  and `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_top`.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable (n : Type u) (k : Type u) [Field k]

/-- **`H⁰` of the twisting sheaves on `ℙᵈ_k`, canonically.** For `m ≥ 0`,
`H⁰(ℙ(n; Spec k), 𝒪(m)) ≅ Sᵐ(V)`, `V = k^{d+1}`, realised as the degree-`m` homogeneous
polynomials in the homogeneous coordinates: a class of `H⁰` is a global section of `𝒪(m)`, which
is the section of a unique homogeneous polynomial (`twistHZeroLinearEquiv_symm_apply`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`lem-pc-projective-space-twist-cohomology` (i)) -/
def twistHZeroLinearEquivOfField [Fintype n] [Nonempty n] (m : ℕ) :
    (twist n (Spec (.of k)) m).H 0 ≃ₗ[k] MvPolynomial.homogeneousSubmodule n k m :=
  twistHZeroLinearEquiv k m

/-- The inverse of `twistHZeroLinearEquivOfField` sends a homogeneous polynomial to the class in
`H⁰` of the global section of `𝒪(m)` it defines. -/
lemma twistHZeroLinearEquivOfField_symm_apply [Fintype n] [Nonempty n] (m : ℕ)
    (f : MvPolynomial.homogeneousSubmodule n k m) :
    (twistHZeroLinearEquivOfField n k m).symm f =
      (H.zeroLinearEquiv (twist n (Spec (.of k)) m)).symm (homogeneousSubmoduleToTwist k m f) :=
  rfl

/-- **The top cohomology of the twisting sheaves on `ℙᵈ_k`, canonically.** For `m ≤ -d - 1`,
`Hᵈ(ℙ(n; Spec k), 𝒪(m)) ≅ S^{-m-d-1}(V)^∨`: the canonical Leray isomorphism with the top
homology of the monomial Čech complex, followed by the monomial duality there. For `d ≥ 1` it is
the isomorphism induced by the Serre pairing `H⁰(𝒪(-m-d-1)) × Hᵈ(𝒪(m)) → Hᵈ(𝒪(-d-1)) ≅ k`
(`twistHTopLinearEquivDualOfField_apply`); for `d = 0` both sides are `k`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`lem-pc-projective-space-twist-cohomology` (ii),
`theorem-riemann-roch-coherent-serre-duality--2`) -/
def twistHTopLinearEquivDualOfField [Fintype n] {d : ℕ} (hn : Fintype.card n = d + 1) {m : ℤ}
    (hm : m ≤ -(d : ℤ) - 1) :
    (twist n (Spec (.of k)) m).H d ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule n k (-m - d - 1).toNat) :=
  twistHLinearEquivMonomialCechHomology k m d ≪≫ₗ
    monomialCechComplexHomologyTopLinearEquivDual n k m hn hm

/-- **`twistHTopLinearEquivDualOfField` is the Serre pairing.** For `d ≥ 1`, the isomorphism
`Hᵈ(ℙᵈ_k, 𝒪(m)) ≅ (k[x]_{-m-d-1})^∨` sends a class `x` to `f ↦ tr (f · x)`, where `f · x` is the
image of `x` under multiplication by the section `f` of `𝒪(-m-d-1)` and
`tr : Hᵈ(ℙᵈ_k, 𝒪(-d-1)) ≅ k` is the trace `twistTopTrace`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem twistHTopLinearEquivDualOfField_apply [Fintype n] {p : ℕ}
    (hn : Fintype.card n = p + 1 + 1) {m : ℤ} (hm : m ≤ -((p + 1 : ℕ) : ℤ) - 1)
    (x : (twist n (Spec (.of k)) m).H (p + 1))
    (f : MvPolynomial.homogeneousSubmodule n k (-m - ((p + 1 : ℕ) : ℤ) - 1).toNat) :
    twistHTopLinearEquivDualOfField n k hn hm x f = twistTopTrace k hn
      (twistMulPairing k (monomialCechPairing_aux hm) (p + 1)
        (homogeneousSubmoduleToTwist k _ f) x) :=
  twistHTopLinearEquivDual_apply hn hm x f

/-- **`H⁰` of the twisting sheaves on `ℙᵈ_k`.** With `X = ℙᵈ_k` presented as `ℙ(n; Spec k)`
for an index type `n` of homogeneous coordinates with `Nat.card n = d + 1`, and `Sᵐ(V)` for
`V = k^{d+1}` the degree-`m` homogeneous part of the polynomial ring in those coordinates,
`H⁰(X, 𝒪(m)) = Sᵐ(V)` for `m ≥ 0`. The isomorphism is `twistHZeroLinearEquivOfField`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`lem-pc-projective-space-twist-cohomology` (i)) -/
theorem nonempty_H_zero_twist_equiv [Finite n] (d : ℕ) (hn : Nat.card n = d + 1) (m : ℕ) :
    Nonempty ((twist n (Spec (.of k)) m).H 0 ≃ₗ[k] MvPolynomial.homogeneousSubmodule n k m) := by
  have := Fintype.ofFinite n
  have : Nonempty n := (Nat.card_pos_iff.1 (by omega)).1
  exact ⟨twistHZeroLinearEquivOfField n k m⟩

/-- **The top cohomology of the twisting sheaves.**
`H^d(ℙᵈ_k, 𝒪(m)) = S^{-m-d-1}(V)^∨` for `m ≤ -d-1`. Taking `m = -d-1` exhibits `𝒪(-d-1)` as
the dualising sheaf of `ℙᵈ_k`. The isomorphism is `twistHTopLinearEquivDualOfField`, induced by
the Serre pairing (`twistHTopLinearEquivDualOfField_apply`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`,
`lem-pc-projective-space-twist-cohomology` (ii),
`theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem nonempty_H_twist_top_equiv_dual [Finite n] (d : ℕ) (hn : Nat.card n = d + 1) (m : ℤ)
    (hm : m ≤ -(d : ℤ) - 1) :
    Nonempty ((twist n (Spec (.of k)) m).H d ≃ₗ[k]
      Module.Dual k (MvPolynomial.homogeneousSubmodule n k (-m - d - 1).toNat)) := by
  have := Fintype.ofFinite n
  exact ⟨twistHTopLinearEquivDualOfField n k (by rwa [← Nat.card_eq_fintype_card]) hm⟩

end AlgebraicGeometry.ProjectiveSpace
