# The commutators of two simple root groups of type G₂

This module computes the commutators among the positive root groups of type `G₂`, for the
root groups attached to two simple roots and their Weyl points. The base ring is an
arbitrary commutative ring, which may have nilpotents. Two simple roots `a`, `c` are of type
`G₂`, with `a` short, when `⟨a, c^∨⟩ = -1` and `⟨c, a^∨⟩ = -3`. The constants are pinned in
the ring itself, as in SGA 3, Exp. XXIII, Proposition 3.4.1. Some rank-one identities
enter as hypotheses. The module imports `Langlands.GroupScheme.Reductive.LocalSplitTypeA2`
for the rank-two root lemmas, and `Langlands.GroupScheme.Reductive.LocalSplitConeCommutator`
for commutators along an ordered cone of roots.

Notation: `rootPoint u Z x` is the point of `G` over `Z` given by `u : 𝔾ₐ ⟶ G` at the global
function `x`. `weylPoint u u' = u'(-1) u(1) u'(-1)` is a global point. `G.constantPoint g Z`
pulls a global point `g` back to `Z`, and `G.innerIso g` is conjugation by `g`. The
commutator is written `[g, h] = (g h)⁻¹ (h g)`.

## Root-datum part (namespace `Langlands.LinearAlgebra`)

`P : RootDatum J (I → ℤ) (I → ℤ)` is reduced, with finite index type and decidable
equality. `b` is a base and `a ≠ c` are simple roots with `⟨a, c^∨⟩ = -1` and
`⟨c, a^∨⟩ = -3` (`P.pairingIn ℤ`).

- `g2_coeffs_of_nonneg`: a root `p • a + q • c` with `p, q ≥ 0` has `(p, q)` among
  `(1, 0)`, `(0, 1)`, `(1, 1)`, `(2, 1)`, `(3, 1)` and `(3, 2)`.
- `g2_coeffs`: a root `p • a + q • c` with `p, q ∈ ℤ` has `(p, q)` among these six pairs
  and their negatives.

## Group identities (namespace `Langlands.GroupScheme.LocalSplitCell`)

The identities `g2_identity_I`–`g2_identity_IV` hold in an abstract group `M`. The maps
`Pa`, `Pb`, `P1`, `P2`, `P3`, `P4`, `Pna`, `Pnb` go from a commutative ring `Γ` to `M`. They
play the root groups of `a`, `c`, `a + c`, `2 a + c`, `3 a + c`, `3 a + 2 c`, `-a` and
`-c`. Each identity assumes those of the following commutation formulas it uses, with
constants `A, …, H, J ∈ Γ`:

- (1) `Pb y · Pa x = Pa x · Pb y · P1(A x y) · P2(B x² y) · P3(C x³ y) · P4(D x³ y²)`;
- (2) `P1 y · Pa x = Pa x · P1 y · P2(E x y) · P3(F x² y) · P4(G x y²)`;
- (3) `P2 y · Pa x = Pa x · P2 y · P3(H x y)`;
- (4) `P3 y · Pb x = Pb x · P3 y · P4(J x y)`;
- (6) `P2 y · P1 x = P1 x · P2 y · P4(H x y)`.

The labels match the hypothesis names `h1`, `h2`, `h3`, `h4`, `h6` in Lean.

Put `Na = Pna(-1) Pa(1) Pna(-1)` and `Nb = Pnb(-1) Pb(1) Pnb(-1)`. The conjugation rules by
`Nb` are: `Pb y ↦ Pnb(-y)`, `Pa x ↦ P1 x`, `P1 t ↦ Pa(-t)`, `P2 t ↦ P2 t`, `P3 t ↦ P4 t` and
`P4 t ↦ P3(-t)`. The rules by `Na` are: `Pa x ↦ Pna(-x)`, `Pna x ↦ Pa(-x)`, `Pb y ↦ P3(-y)`,
`P1 t ↦ P2 t`, `P2 t ↦ P1(-t)`, `P3 t ↦ Pb t` and `P4 t ↦ P4 t`. Each identity assumes the
additivity of some of the maps, the rules it uses, and some of the following commutations:
`Pnb` with `Pa`, `P2`, `P3`; `Pna` with `Pb`; `Pb` with `P1`, `P2`, `P4`; `P1` with `P3`,
`P4`; `P2` with `P3`, `P4`; `P3` with `P4`. The conclusions are:

- `g2_identity_I` (SGA 3, XXIII, 3.4.5):
  `Pa 1 · P1 A · P2 B · P3 C · P4(D - C J) =
  Pa A · P1 1 · P2(E A - B) · P3(F A² + C J - D) · P4(G A - C)`;
- `g2_identity_II` (3.4.6):
  `Pb 1 · P1(-A) · P2 B · P3(-C) · P4(-D) = Pb C · P1(-B) · P2 A · P3(-1) · P4(D - C J - A B H)`;
- `g2_identity_III` (3.4.7): `P3 1 · P4(-J) = P4 1 · P3(-J)`;
- `g2_identity_IV` (3.4.8): for some `W`,
  `P1 1 · P2(-E) · P3 F · P4(-G) = Pb(F - C H) · P1(B H - E) · P2(1 - A H) · P3 H · P4 W`.

`map_neg_of_add` says that an additive map from a ring to a group sends `-s` to the inverse.

## Scheme part

The setting is a commutative ring `R`, a reductive group scheme `G` over `Spec R` with
affine structure morphism, a coordinate split torus `i : T_I → G` that is maximal on every
residue-field fibre, a fibrewise root datum `P`, root parametrizations `v α` of `i` for
every root `α`, a base `b`, and simple roots `a ≠ c` of type `G₂` as above.

- `eq_of_prod_five` and `eq_of_prod_two`: for five (respectively two) distinct positive
  roots `x₀, …` of `b`, an equality
  `v_{x₀}(a₀) ⋯ v_{x₄}(a₄) = v_{x₀}(c₀) ⋯ v_{x₄}(c₄)` over any ring over `R` gives
  `a_k = c_k` for every `k`.
- `g2_constants`: let `N_a = weylPoint (v a) (v (-a))` and `N_c = weylPoint (v c) (v (-c))`
  be Weyl points of `i` acting by `s_a` and `s_c` (`IsWeylPoint`). Here `-a` is
  `P.reflectionPerm a a`. Assume, over every `s : Spec B → Spec R` and writing `N` for the
  pulled-back points:
  - `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)` and `N_c v_c(x) N_c⁻¹ = v_{-c}(-x)`;
  - for every root `β` and every root parametrization `w` of `i` for `P.root β`,
    `(N_a N_a) w(x) (N_a N_a)⁻¹ = w(σ • x)` with `σ = (⟨β, a^∨⟩).negOnePow`, the sign
    `(-1)^⟨β, a^∨⟩` in `ℤˣ`. The same holds for `N_c` with `⟨β, c^∨⟩`.

  Put `p₁ = v a ≫ Ad(N_c)`, `p₂ = p₁ ≫ Ad(N_a)`, `p₃ = v c ≫ Ad(N_a)` and
  `p₄ = p₃ ≫ Ad(N_c)` (`Ad(N) = (G.innerIso N).hom`). They are root parametrizations for
  `a + c`, `2 a + c`, `3 a + c` and `3 a + 2 c`. Then for every `s : Spec B → Spec R` and
  all `x, y ∈ B`:
  - `[v_a(x), v_c(y)] = p₁(x y) · p₂(x² y) · p₃(-(x³ y)) · p₄(-(x³ y²))`;
  - `[v_a(x), p₁(y)] = p₂(2 x y) · p₃(-(3 x² y)) · p₄(-(3 x y²))`;
  - `[v_a(x), p₂(y)] = p₃(-(3 x y))`;
  - `[v_c(x), p₃(y)] = p₄(-(x y))`;
  - `[p₁(x), p₂(y)] = p₄(-(3 x y))`.

  Elements of `B` are global functions through the inverse of `Scheme.ΓSpecIso`.

## Statement

`LocalSplitTypeG2CommutatorStatement.{u}` quantifies over the setting of `g2_constants`.
That is: a commutative ring `R`, a finite type `I` with decidable equality and a type `J`
(all in universe `u`), a reductive `G` with affine structure morphism, the torus `i`, the
fibrewise root datum `P`, the family `v`, the base `b`, the simple roots `a ≠ c` with
pairings `-1` and `-3`, the two Weyl point hypotheses, the two conjugation identities and
the two square-action hypotheses. Its conclusion is the conjunction of the five commutator
formulas above. The module proves it at full universe as `localSplitTypeG2Commutator`.

## Proof

**Roots.** `g2_coeffs_of_nonneg` is a strong induction on `p + q` with the imported
predecessor lemma `exists_pred_of_root_eq_pair`. Height `0` is impossible, and `2 a`, `2 c`
are excluded by Mathlib's `nsmul_notMem_range_root`. In the induction step, `4 a + c` is
excluded because the `a`-string through `c` has top coefficient `-⟨c, a^∨⟩ = 3`. And
`a + 2 c` is excluded because the `c`-string through `a` has top coefficient `1` (Mathlib's
`root_add_nsmul_mem_range_iff_le_chainTopCoeff` and `Base.chainTopCoeff_eq_of_ne`). The
vectors `2 a + 2 c`, `3 a + 3 c` and `4 a + 2 c` are multiples of the roots `a + c` and
`2 a + c`, so they are not roots. `g2_coeffs` reduces negative coefficients to this case
through `-α`, with the imported `sign_of_root_eq_pair`.

**The identities** follow SGA 3, Exp. XXIII, 3.4.5–3.4.8.

- *Identity I.* Expand `Nb Pa(1) Nb⁻¹ = P1 1`; since `Pnb` commutes with `Pa`, this gives
  `Pb(1) Pa(1) Pb(1)⁻¹ = Pnb(1) P1(1) Pnb(1)⁻¹`. The left side is rewritten with (1) and
  (4). The right side is rewritten with the `Nb`-conjugates of (1) and (4), and then
  reordered with (2).
- *Identity II.* `Na Pb(1) Na⁻¹ = P3(-1)` gives
  `Pa(1) Pb(1) Pa(1)⁻¹ = Pna(-1)⁻¹ P3(-1) Pna(-1)`. The left side uses (1) at `x = -1`.
  The right side uses the `Na`-conjugate of (1), reordered with (4) and (6).
- *Identity III.* `Nb P3(1) Nb⁻¹ = P4 1` is handled the same way with (4) and its
  `Nb`-conjugate.
- *Identity IV.* Conjugating the definition of `Na` by `Na` gives
  `Na = Pa(1) Pna(-1) Pa(1)`. Then `Na P1(1) Na⁻¹ = P2 1` gives
  `Pa(1) P1(1) Pa(1)⁻¹ = Pna(1) (Pa(1)⁻¹ P2(1) Pa(1)) Pna(1)⁻¹`. The left side uses (2) at
  `x = -1` and the inner conjugate uses (3). Conjugation by `Pna(1)` uses the
  `Na`-conjugates of (2) and (1). The resulting product is sorted by a terminating rewriting
  system made from the commutations, from (4) and (6), and from additivity. The coordinate
  at `3 a + 2 c` is left as the existential `W`.

The rearrangements are checked by Mathlib's `group` tactic.

**Uniqueness of coordinates.** `eq_of_prod_five` and `eq_of_prod_two` apply the imported
`listProd_rootPoint_injective` to the lists `[x₀, …, x₄]` and `[x₀, x₁]`.

**The constants.**

- *Setup.* Put `d₁ = s_c a`, `d₂ = s_a d₁`, `d₃ = s_a c` and `d₄ = s_c d₃`. These are the
  roots `a + c`, `2 a + c`, `3 a + c` and `3 a + 2 c`. Then `p₁, …, p₄` are root
  parametrizations for them, by the imported `IsRootParametrization.comp_innerIso`. Replace
  `v` at `d₁, …, d₄` by `p₁, …, p₄` (`Function.update`). Every root involved is written as
  `p • a + q • c`. Distinct coefficient pairs give distinct indices, by linear independence
  of `a` and `c`. `g2_coeffs` then decides every cone condition by `omega`.
- *Commutator constants.* The imported `exists_rootPoint_comm_cone` gives constants for
  `(a, c)`, with cone `[d₁, d₂, d₃, d₄]`, and for `(a, d₁)`, with cone `[d₂, d₃, d₄]`. The
  imported `exists_rootPoint_comm_single` gives constants for `(a, d₂)` (cone `d₃`),
  `(c, d₃)` (cone `d₄`) and `(d₁, d₂)` (cone `d₄`).
- *Commutations.* The imported `rootPoint_commute_of_forall_ne` gives all commutations
  needed by the identities, for pairs with no root in their cone. It also shows that `N_c`
  commutes with `p₂`: the root groups of `±c` commute with that of `2 a + c`. Likewise
  `N_a` commutes with `p₄`, because the root groups of `±a` commute with that of `3 a + 2 c`.
  Both facts use the imported `constantPoint_weylPoint`.
- *Conjugation rules.* The rules for `p₁, …, p₄` under `N_a` and `N_c` follow from their
  definitions (imported `rootPoint_comp` and `GroupScheme.comp_innerIso_hom`), from the
  conjugation hypotheses, and from the square-action hypotheses. The relevant pairings
  are `⟨a, c^∨⟩ = -1`, `⟨c, a^∨⟩ = -3`, `⟨a + c, a^∨⟩ = -1` and `⟨3 a + c, c^∨⟩ = -1` (all
  odd), and `⟨-a, a^∨⟩ = -2` (even). The rule `N_a v_{-a}(x) N_a⁻¹ = v_a(-x)` follows from
  `N_a v_a(x) N_a⁻¹ = v_{-a}(-x)`, because `N_a²` commutes with `v_{-a}`.
- *Evaluation.* Evaluate over `R` itself, with `s = 𝟙` (Mathlib's `Spec.preimage_id`).
  Elements of `R` map to global functions by a ring map `ε` built from
  `Scheme.ΓSpecIso`; `ε` is bijective. Apply the four identities with
  `P3 t = p₃(-t)` and `P4 t = p₄(-t)`. Formula (6) comes from conjugating (3) by `N_c`.
- *Uniqueness.* `eq_of_prod_five` and `eq_of_prod_two`, in the big cell of `b`, give linear
  equations among the images of the constants. In order: from I, `A = 1`. From II,
  `C = 1` and `B = A`. From III, `J = -1`. From I, `E = 2`. From IV, `H = 3` and `F = 3`.
  From I, `D = 1` and `G = 3`. Comparing (6) with the constant for `(d₁, d₂)` pins the
  latter. Injectivity of `ε` brings the constants back to `R`, and the five formulas follow
  over every ring over `R`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. The statement and the computation follow SGA 3, Exp. XXIII, Proposition 3.4.1 and its
proof 3.4.2–3.4.9; the role of these constants in the Isomorphism Theorem is explained in
Conrad, *Reductive group schemes* (2014), Lemma 6.2.8. Here the computation is carried out
with the universal commutator constants of the imported modules and uniqueness of big-cell
coordinates, in this module's conventions: commutators `(g h)⁻¹ (h g)` and
`N_a = v_{-a}(-1) v_a(1) v_{-a}(-1)`. The parametrizations `p₃`, `p₄` here are those of
SGA 3 composed with `x ↦ -x`, which accounts for the signs. The rank-one identities are
hypotheses here; they are not proved in this module. The module does not compute
`(N_a N_c)⁶`, does not compare Weyl conjugation units of two groups, and does not prove
the local split Isomorphism Theorem.
