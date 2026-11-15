# The commutator of two simple root groups of type A₂ (and A₁ × A₁)

This module computes exactly the commutator of the root groups of two simple roots of
type `A₂`. The base ring is an arbitrary commutative ring, which may have nilpotents.
Two simple roots `a`, `c` are of type `A₂` when `⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1`. The
constants come out as `-1` in the ring itself, not merely modulo nilpotents. The module
imports `Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator`.

## Root-datum part (namespace `Langlands.LinearAlgebra`)

`P : RootDatum J (I → ℤ) (I → ℤ)` has a finite index type with decidable equality.
`b` is a base, and `a ≠ c` are simple roots of `b`.

- `sum_pair_eq` and `sum_pair_sub_eq`: the combinations `p • a + q • c` and
  `p • a + q • c - j`, for a third simple root `j`, written as sums over the base with
  explicit coefficient functions.
- `sign_of_root_eq_pair`: if a root equals `p • a + q • c`, then `p` and `q` are both
  `≥ 0` or both `≤ 0`. This is Mathlib's `pos_or_neg_of_sum_smul_root_mem`.
- `height_of_root_eq_pair`: such a root has height `p + q`.
- `exists_pred_of_root_eq_pair`: let a root equal `p • a + q • c` with `p, q ≥ 0` and
  `p + q ≥ 2`. Then `(p - 1) • a + q • c` (with `p ≥ 1`) or `p • a + (q - 1) • c`
  (with `q ≥ 1`) is a root.
- `a2_coeffs_of_nonneg` and `a2_coeffs`: suppose `P` is reduced and
  `⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1` (`P.pairingIn ℤ`). Then a root of the form
  `p • a + q • c` with `p, q ∈ ℤ` has `(p, q)` among `±(1, 0)`, `±(0, 1)` and
  `±(1, 1)`.
- `a1a1_coeffs_of_nonneg` and `a1a1_coeffs`: suppose `P` is reduced and
  `⟨c, a^∨⟩ = 0`. Then a root of the form `p • a + q • c` with `p, q ∈ ℤ` has `(p, q)`
  among `±(1, 0)` and `±(0, 1)`.

## Group part (namespace `Langlands.GroupScheme.LocalSplitCell`)

- `a2_group_identity`: an identity in an abstract group. Let `X`, `Y`, `B`, `W` be
  additive maps from a commutative ring into a group, and let `C`, `D` be ring
  elements. Assume
  `(X x · B y)⁻¹ (B y · X x) = W (C x y)`, `(Y x · W y)⁻¹ (W y · Y x) = B (D x y)`, that
  `Y` commutes with `B` and `B` with `W`, and that `W t = N · B t · N⁻¹` with
  `N = Y(-1) X(1) Y(-1)`. Then `B (1 - D C) = W (1 + C)`.
- `root_reflectionPerm_eq_add`: if `⟨c, a^∨⟩ = -1`, then `s_a c = a + c`.
- `a2_constants`: the setting is a reductive `G` over `Spec R` with affine structure
  morphism, a fibrewise maximal coordinate split torus `i`, and a fibrewise root datum
  `P`. Let `v` be root parametrizations of `i` for all roots, and `b` a base with simple
  roots `a ≠ c` such that `⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1`. Suppose that
  `n = weylPoint (v a) (v (-a)) = v_{-a}(-1) v_a(1) v_{-a}(-1)` is a Weyl point of `i`
  acting by `s_a` (`IsWeylPoint`). Here `-a` is `P.reflectionPerm a a`. Put
  `w = v c ≫ Ad(n)`. Then for every `s : Spec B → Spec R` and all `x, y ∈ B`:
  - `(v_a(x) v_c(y))⁻¹ (v_c(y) v_a(x)) = w(-x y)`;
  - `(v_{-a}(x) w(y))⁻¹ (w(y) v_{-a}(x)) = v_c(-x y)`.

  Elements of `B` are global functions through the inverse of `Scheme.ΓSpecIso`.
- `a1a1_commute`: in the same setting, let `a ≠ c` be simple roots of a base with
  `⟨c, a^∨⟩ = 0`. Let `β` be a root with `β = ±a` and `ε` a root with `ε = ±c`. Then
  `v_β(x) v_ε(y) = v_ε(y) v_β(x)` over every ring over `R`.

## Statement

`LocalSplitTypeA2CommutatorStatement.{u}` quantifies over the setting of `a2_constants`:
a commutative ring `R`, a finite type `I` with decidable equality and a type `J` (all in
universe `u`), a reductive `G` with affine structure morphism, the torus `i`, the
fibrewise root datum `P`, the family `v`, the base `b`, the simple roots `a`, `c` with
the two pairings `-1`, and the Weyl point hypothesis. Its conclusion is the conjunction
of the two identities above. The module proves it at full universe as
`localSplitTypeA2Commutator`.

## Proof

**Roots.** `exists_pred_of_root_eq_pair` takes a simple root `j` with
`0 < ⟨j, α^∨⟩`, from Mathlib's `IsPos.exists_mem_support_pos_pairingIn`. Then
`0 < ⟨α, j^∨⟩` by `zero_lt_pairingIn_iff'`, and `α - j` is a root by
`root_sub_root_mem_of_pairingIn_pos`. Here `α ≠ j` because `α` has height `≥ 2`. If
`j` were neither `a` nor `c`, the coefficients of `α - j` would have mixed signs.
`a2_coeffs_of_nonneg` is a strong induction on `p + q`. (`a1a1_coeffs_of_nonneg` is the
same induction; there `a + c` is excluded at height `2` because the `a`-string through
`c` has top coefficient `-⟨c, a^∨⟩ = 0`, and no root has height `≥ 2`.) Height `0` gives the zero
vector, which is not a root. At height `2`, `2 a` and `2 c` are not roots, by Mathlib's
`nsmul_notMem_range_root` for reduced `P`. At height `3`, the predecessor must be
`a + c`, which leaves `c + 2 a` or `a + 2 c`. These are excluded by Mathlib's
`root_add_nsmul_mem_range_iff_le_chainTopCoeff` and `Base.chainTopCoeff_eq_of_ne`: the
`a`-string through `c` has top coefficient `-⟨c, a^∨⟩ = 1`. Above height `3`, the
predecessor would again have height `≥ 3`. `a2_coeffs` reduces negative coefficients to
this case through `-α`.

**The abstract identity.** From the first hypothesis at `(x, y) = (-1, 1)`,
`X(1) B(1) X(-1) = B(1) W(-C)`. From the second at `(1, -C)`,
`Y(-1) W(-C) Y(1) = W(-C) B(-D C)`. Then `N⁻¹ = Y(1) X(-1) Y(1)`, and
`W(1) = N B(1) N⁻¹` reduces as follows:
`Y(-1) X(1) Y(-1) B(1) Y(1) X(-1) Y(1) = Y(-1) X(1) B(1) X(-1) Y(1)
= Y(-1) B(1) W(-C) Y(1) = B(1) W(-C) B(-D C) = B(1 - D C) W(-C)`.
Multiplying by `W(C)` gives `B(1 - D C) = W(1 + C)`.

**The constants.** Put `d = s_a c`, the root `a + c`. Then `w` is a root
parametrization for `d`, by the imported `IsRootParametrization.comp_innerIso`.
Replace `v d` by `w` (`Function.update`). The root facts give four cone conditions.
(1) A root `dS • a + dT • c` with `dS, dT ≥ 1` has `dS = dT = 1`. (2) The same holds
for `dS • (-a) + dT • d`, whose only such root is `c`. (3) No `dS • (-a) + dT • c` is
a root. (4) No `dS • c + dT • d` is a root. The imported
`exists_rootPoint_comm_single` gives constants `C` for `(a, c)` and `D` for `(-a, d)`.
The imported `rootPoint_commute_of_forall_ne` gives the commutations `(-a, c)` and
`(c, d)`. The conjugation formula `w(t) = N v_c(t) N⁻¹` is the imported
`rootPoint_comp` with `GroupScheme.comp_innerIso_hom` and `constantPoint_weylPoint`.

For `a1a1_commute`, write `β = σ a` and `ε = τ c` with `σ, τ = ±1`. A root
`dS • β + dT • ε` with `dS, dT ≥ 1` would have both coefficients nonzero, which
`a1a1_coeffs` excludes, and `β ≠ -ε` by linear independence of `a`, `c`. The imported
`rootPoint_commute_of_forall_ne` applies.

Evaluate over `R` itself, with `s = 𝟙` (Mathlib's `Spec.preimage_id`). The abstract
identity gives `v_c(1 - D C) = w(1 + C)`. In the big cell of `b` for the updated family
(imported `exists_cell_of_base`), both sides are ordered products with a single nonzero
coordinate (imported `orderedProduct_eq_rootPoint_of_eq_zero`). These coordinates sit
at the distinct positions of `c` and `d`. Uniqueness of coordinates (imported
`orderedProduct_pos_injective`) gives `1 - D C = 0` and `1 + C = 0` in `R`. So
`C = D = -1`, and the two identities follow from the constants over every ring.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The structure constants of the rank-two pinned groups are computed in SGA 3,
Exp. XXIII, 3.2 (type `A₂`), and the corresponding step of the Isomorphism Theorem is
Conrad, *Reductive group schemes* (2014), Lemma 6.2.8. Both arguments conjugate the
commutation relations by the Weyl elements. The mechanism here is the same: expand
`Ad(n_a)` on `U_c` and compare coordinates. It is carried out directly in the group of
points with the universal commutator constants of the imported modules. The sign
conventions are those of this module: commutators `(g h)⁻¹ (h g)` and
`n_a = v_{-a}(-1) v_a(1) v_{-a}(-1)`. The module does not treat the types `B₂` and
`G₂`, does not compare the Weyl conjugation units of two groups, and does not prove the
local split Isomorphism Theorem.
