# The commutators of two simple root groups of type B₂

This module computes exactly the commutators of the root groups of two simple roots of
type `B₂`. The base ring is an arbitrary commutative local ring, which may have
nilpotents. Two simple roots `a`, `c` are of type `B₂`, with `a` short, when
`⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -2`. The constants are pinned in the ring itself, as in
SGA 3, Exp. XXIII, Proposition 3.3.1. Some rank-one identities enter as hypotheses. The
module imports `Langlands.GroupScheme.Reductive.LocalSplitTypeA2`, which provides the
rank-two root lemmas and, through it, `Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator`.
It also imports `Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity`.

## Root-datum part (namespace `Langlands.LinearAlgebra`)

`P : RootDatum J (I → ℤ) (I → ℤ)` is reduced, with finite index type and decidable
equality. `b` is a base and `a ≠ c` are simple roots with `⟨a, c^∨⟩ = -1` and
`⟨c, a^∨⟩ = -2` (`P.pairingIn ℤ`).

- `b2_coeffs_of_nonneg`: a root `p • a + q • c` with `p, q ≥ 0` has `(p, q)` among
  `(1, 0)`, `(0, 1)`, `(1, 1)` and `(2, 1)`.
- `b2_coeffs`: a root `p • a + q • c` with `p, q ∈ ℤ` has `(p, q)` among these four pairs
  and their negatives.

## Group part (namespace `Langlands.GroupScheme.LocalSplitCell`)

- `b2_group_identities`: an identity in an abstract group. Let `Pa`, `Pb`, `Pab`, `P2`,
  `Pna`, `Pnb` be maps from a commutative ring into a group, with `Pa`, `P2`, `Pnb`
  additive. They play the root groups of `a`, `c`, `a + c`, `2 a + c`, `-a`, `-c`. Let
  `Na = Pna(-1) Pa(1) Pna(-1)` and `Nb = Pnb(-1) Pb(1) Pnb(-1)`. Assume the
  commutation formulas
  `Pb y · Pa x = Pa x · Pb y · Pab(A x y) · P2(B x² y)` and
  `Pab y · Pa x = Pa x · Pab y · P2(C x y)`.
  Assume the conjugation rules by `Nb`: `Pb y ↦ Pnb(-y)`, `Pa x ↦ Pab x`,
  `Pab t ↦ Pa(-t)`, `P2 t ↦ P2 t`. Assume the conjugation rules by `Na`:
  `Pb y ↦ P2 y`, `Pa x ↦ Pna(-x)`, `Pab t ↦ Pab(k t)`, `P2 t ↦ Pb t`. Assume finally that
  `Pna` commutes with `Pb`, `Pnb` with `Pa` and `P2`, and `Pb` with `Pab` and `P2`.
  Then `Pa 1 · Pab A · P2 B = Pa A · Pab 1 · P2 (C A - B)` and
  `Pb 1 · Pab(-A) · P2 B = P2 1 · Pab(k A) · Pb B`.
- `solve_mul_three`: for additive maps `X`, `Y`, `Z` into a group with `Y` and `Z`
  commuting, `X x₁ Y y₁ Z z₁ = X x₂ Y y₂ Z z₂` implies
  `X (x₁ - x₂) = Y (y₂ - y₁) Z (z₂ - z₁)`.
- `b2_constants`: the setting is a commutative local ring `R`, a reductive `G` over
  `Spec R` with affine structure morphism, a fibrewise maximal coordinate split torus
  `i`, and a fibrewise root datum `P`. Let `v` be root parametrizations of `i` for all
  roots, and `a`, `c` simple roots of a base as above. Let
  `N_a = weylPoint (v a) (v (-a))` and `N_c = weylPoint (v c) (v (-c))` be Weyl points
  of `i` acting by `s_a` and `s_c`. Over every `s : Spec B → Spec R`, assume four
  rank-one identities, writing `N` for the pulled-back points:
  `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)`, `N_c v_c(x) N_c⁻¹ = v_{-c}(-x)`,
  `N_a² v_c(x) N_a⁻² = v_c(x)` and `N_c² v_a(x) N_c⁻² = v_a(-x)`. Put
  `p₁ = v a ≫ Ad(N_c)` and `p₂ = v c ≫ Ad(N_a)`. Then over every ring over `R`:
  - `(v_a(x) v_c(y))⁻¹ (v_c(y) v_a(x)) = p₁(x y) p₂(x² y)`;
  - `(v_a(x) p₁(y))⁻¹ (p₁(y) v_a(x)) = p₂(2 x y)`;
  - `N_a p₁(x) N_a⁻¹ = p₁(-x)`.

  Elements of `B` are global functions through the inverse of `Scheme.ΓSpecIso`.

## Statement

`LocalSplitTypeB2CommutatorStatement.{u}` quantifies over the setting of `b2_constants`.
That is: a commutative local ring `R`, a finite type `I` with decidable equality and a
type `J` (all in universe `u`), a reductive `G` with affine structure morphism, the
torus `i`, the fibrewise root datum `P`, the family `v`, the base `b`, the simple roots
`a ≠ c` with pairings `-1` and `-2`, the two Weyl point hypotheses and the four rank-one
identities. Its conclusion is the conjunction of the three identities above. The module
proves it at full universe as `localSplitTypeB2Commutator`.

## Proof

**Roots.** `b2_coeffs_of_nonneg` is a strong induction on `p + q` with the imported
predecessor lemma `exists_pred_of_root_eq_pair`. Height `0` is impossible, and `2 a`,
`2 c` are excluded by Mathlib's `nsmul_notMem_range_root`. At height `3`, the
predecessor is `a + c`. Then `a + 2 c` is excluded because the `c`-string through `a`
has top coefficient `-⟨a, c^∨⟩ = 1`, by Mathlib's
`root_add_nsmul_mem_range_iff_le_chainTopCoeff` and `Base.chainTopCoeff_eq_of_ne`. At
height `4`, the predecessor is `2 a + c`. Then `c + 3 a` is excluded by the same lemmas,
the `a`-string through `c` having top coefficient `2`. And `2 a + 2 c` is excluded
because it is twice the root `a + c` (index `s_c a`). `b2_coeffs` reduces negative
coefficients to this case through `-α`, with the imported `sign_of_root_eq_pair`.

**The abstract identities** follow SGA 3, Exp. XXIII, 3.3.3–3.3.5.

- Conjugating the first formula by `Nb` gives the rule (5) for `Pnb` and `Pab`.
  Expanding `Nb Pa(1) Nb⁻¹ = Pab 1`, with `Pnb` commuting with `Pa`, gives
  `Pb(1) Pa(1) Pb(1)⁻¹ = Pnb(1) Pab(1) Pnb(1)⁻¹`.
- The left side is `Pa 1 · Pab A · P2 B` by the first formula. The right side is
  `Pab 1 · Pa A · P2(-B)` by (5). The second formula reorders it to
  `Pa A · Pab 1 · P2 (C A - B)`.
- Conjugating the first formula by `Na` gives the rule (3) for `P2` and `Pna`. Expanding
  `Na Pb(1) Na⁻¹ = P2 1` gives the second identity, again with the first formula on the
  left side.

The rearrangements are checked by Mathlib's `group` tactic.

**The constants.**

- *Setup.* Put `d₁ = s_c a`, the root `a + c`, and `d₂ = s_a c`, the root `2 a + c`.
  Then `p₁` and `p₂` are root parametrizations for `d₁` and `d₂`, by the imported
  `IsRootParametrization.comp_innerIso`. Replace `v` at `d₁` and `d₂` by them
  (`Function.update`).
- *Root combinatorics.* Every root involved is written as `p • a + q • c`. Distinct
  coefficient pairs give distinct indices, by linear independence of `a` and `c`.
  `b2_coeffs` then decides every cone condition by `omega`.
- *Commutator constants.* The imported `exists_rootPoint_comm_two` gives constants `A`
  and `B` for `(a, c)`, with cone `{a + c, 2 a + c}`. The imported
  `exists_rootPoint_comm_single` gives a constant `C` for `(a, a + c)`, with cone
  `{2 a + c}`.
- *Commutations.* The imported `rootPoint_commute_of_forall_ne` gives the commutations
  `(-a, c)`, `(-c, a)`, `(c, a + c)`, `(c, 2 a + c)`, `(-c, 2 a + c)` and
  `(a + c, 2 a + c)`.
- *The unit `k`.* The conjugate `p₁ ≫ Ad(N_a)` is a root parametrization for
  `s_a(a + c) = a + c`, because `⟨a + c, a^∨⟩ = 0`. The imported
  `IsRootParametrization.comparisonUnit` gives a unit `κ` with
  `p₁ ≫ Ad(N_a) = scaleHom κ ≫ p₁`, and the imported `rootPoint_scaleHom` turns this
  into the rule `Pab t ↦ Pab(κ t)`.
- *The other conjugation rules.* The rules for `p₁` and `p₂` under `N_c` and `N_a` follow
  from their definitions (imported `rootPoint_comp`, `GroupScheme.comp_innerIso_hom` and
  `constantPoint_weylPoint`) and the rank-one hypotheses.
- *Evaluation.* Evaluate over `R` itself, with `s = 𝟙` (Mathlib's `Spec.preimage_id`),
  and apply `b2_group_identities`. Then `solve_mul_three` gives
  `v_a(1 - A) = p₁(1 - A) p₂(C A - 2 B)` and `v_c(1 - B) = p₁(κ A + A) p₂(1 - B)`.
- *Uniqueness.* The imported `coord_zero_of_eq_mul`, applied in the big cell of `b`,
  makes all these coordinates zero. So `A = B = 1`, `C = 2` and `κ = -1` in `R`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The statement and the computation follow SGA 3, Exp. XXIII, Proposition 3.3.1 and
its proof 3.3.2–3.3.6; the role of these constants is explained in Conrad, *Reductive
group schemes* (2014), Lemma 6.2.8. Here the computation is carried out with the
universal commutator constants of the imported modules and uniqueness of big-cell
coordinates, in this module's conventions: commutators `(g h)⁻¹ (h g)` and
`N_a = v_{-a}(-1) v_a(1) v_{-a}(-1)`. The rank-one identities are hypotheses here; they
are not proved in this module. The module does not compute the torus element
`(N_a N_c)⁴`, does not treat type `G₂`, does not compare Weyl conjugation units of two
groups, and does not prove the local split Isomorphism Theorem.
