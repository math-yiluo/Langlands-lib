# Weights of a cocharacter on the actual Lie algebra through a split torus

Worker 303. This module compares two kinds of weight space in the actual Lie
algebra `lieKernel G k`. The first kind belongs to a homomorphism `j : T ⟶ G`
from a split torus. The second belongs to the composite `ν ≫ j` of a
cocharacter `ν : 𝔾_m ⟶ T` with `j`. It then proves the regular-cocharacter
consequences that the clauses of
`Langlands.GroupScheme.RegularCocharacterBorelStatement` need at the
Lie-algebra level. This is helper infrastructure for the proof task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`.

Everything is stated with the published notions:

- `weightSpace` and `roots` from `Torus/Weights`. A weight space consists of the
  vectors whose eigenvalue equation holds on every commutative test algebra.
- `latticePairing` from `Torus/Lattice`.
- `IsRegularCocharacter` from `Absolute/Borel`.

The only structural input is the published split-torus weight decomposition
`isInternal_weightSpace_of_isSplitTorus` from `Torus/WeightDecomposition`. No
reductivity, smoothness, connectedness or maximality hypothesis appears.
The module proves no statement about the dynamic subgroups `P(ν)`, `Z(ν)` or
`U(ν)` themselves. To turn these Lie-algebra identities into facts about
dynamic subgroups, one needs a separate comparison, such as the published,
still unproved `DynamicLieStatement`. Its right-hand sides are exactly the
sums `⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n)` and
`⨆ n : ℕ, weightSpace χ (Gm.powerHom _ (n + 1))` treated here.

## Sources and provenance

The results are derived infrastructure for Milne, *Algebraic Groups* (2017),
source ID `milne-2017-algebraic-groups`, §21.d, printed pp.433–434
(PDF pp.449–450):

- The proof of Proposition 21.29 uses the fact that `𝔾_m` acts on `g_α`
  through `t ↦ t^⟨α,ν⟩`, which is `weightSpace_le_weightSpace_cocharacter`
  below.
- That proof also writes `Lie P(ν)` as the trivial-weight part plus the sum of
  the `g_α` with `⟨α,ν⟩ > 0`. The Lie-algebra side of this description is
  `iSup_nat_weightSpace_cocharacter` together with
  `iSup_nonneg_weightSpace_eq_of_isRegular` and
  `iSup_pos_weightSpace_eq_iSup_roots`.
- The proof of Proposition 21.31 uses the equivalence "same Weyl chamber ⇔
  same positive roots ⇔ same Lie algebras". The Lie-algebra form of this
  equivalence is `iSup_nonneg_weightSpace_eq_iff` and
  `iSup_nat_weightSpace_cocharacter_eq_iff`.

In Milne the trivial-weight part is `t = Lie T`, because Milne already knows
`C_G(T) = T`. Here it is the published weight space `weightSpace j 0`, and
nothing identifies it with `Lie T`. The weight decomposition used is Milne,
Theorem 12.12, printed pp.234–235. The Milne errata page
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for these pages.

## Restriction along a homomorphism of tori

The imported `weightSpace_le_comp` from `Rational.GenericLieWeights` works over an arbitrary affine base
`Spec R`. For `f : T' ⟶ T`, `j : T ⟶ G` and a character `χ` of `T`, it shows
that `weightSpace j χ` lies in `weightSpace (f ≫ j) (f ≫ χ)`. The proof
evaluates the eigenvalue equation for `j` at the image point `f(t)`. It then
applies the published `Lie.characterValue_comp`, which gives
`(f ≫ χ)(t) = χ(f(t))`.

The remaining results work over a field `k`, with `G` affine and locally of
finite type.

- `iSup_weightSpace_le_weightSpace_comp` sums the previous inclusion over
  all `χ` with `f ≫ χ = ψ`.
- `iSup_iSup_weightSpace_eq_top` regroups the weight spaces of a split `T`
  by their restriction `ψ = f ≫ χ` and shows that the grouped family still
  spans `⊤`. The proof swaps the two suprema, collapses the equality index
  (`iSup_iSup_eq_right`), and applies `submodule_iSup_eq_top` to the
  published decomposition.
- `weightSpace_comp_eq_iSup_fiber` applies when both `T` and `T'` are split:
  `weightSpace (f ≫ j) ψ = ⨆ χ, ⨆ (_ : f ≫ χ = ψ), weightSpace j χ`. The
  `T'`-weight spaces of `f ≫ j` are independent, again by the published
  decomposition. The grouped `T`-sums lie pointwise below them, and together
  they span `⊤`. Mathlib's `iSupIndep.le_iff_eq_of_iSup_eq_top`, a
  modular-lattice argument, then makes the inclusion an equality.

## The nonnegative weight span

`nonnegativeWeightSpan j ν` is defined as the sum of the weight spaces
`weightSpace j χ` over the characters `χ` of `T` with `⟨χ, ν⟩ ≥ 0`. It is a
submodule of the actual Lie algebra, defined for any `j : T ⟶ G` and any
cocharacter `ν`, with no splitness or regularity assumption.
`nonnegativeWeightSpan_def` unfolds it. The definition has no counterpart of its
own in Milne. In the proof of Proposition 21.29 it is the Lie-algebra side of
`Lie P(ν)`. The precise comparison with the dynamic subgroup needs a separate
input such as `DynamicLieStatement`.

## Cocharacters

Take `T' = 𝔾_m` (split by the published `isSplitTorus_gm`) and `f = ν`.

- The imported `weightSpace_cocharacter_eq_iSup` from `Rational.CocharacterWeightSums`: the weight space of `t ↦ t^n`
  (`Gm.powerHom _ n`) for `ν ≫ j` is the sum of the `weightSpace j χ` with
  `latticePairing T χ ν = n`. The index condition
  `ν ≫ χ = Gm.powerHom _ n` becomes `⟨χ, ν⟩ = n` through `gmEndEquiv`.
- `weightSpace_le_weightSpace_cocharacter`: every weight vector of `χ` for
  `j` is a weight vector of `t ↦ t^⟨χ,ν⟩` for `ν ≫ j`. The proof needs no
  splitness. It rewrites `ν ≫ χ` as `⟨χ, ν⟩ • 𝟙` (`eq_gmEndEquiv_zsmul`).
- `iSup_nat_weightSpace_cocharacter`: the sum over `n : ℕ` of the weight
  spaces of `t ↦ t^n` for `ν ≫ j` equals the sum of the `weightSpace j χ`
  with `0 ≤ ⟨χ, ν⟩`.
- `iSup_nat_succ_weightSpace_cocharacter`: the sum of the weight spaces of
  `t ↦ t^(n+1)` equals the sum of the `weightSpace j χ` with `0 < ⟨χ, ν⟩`.
  These sums are written exactly as on the right-hand sides of
  `DynamicLieStatement`. Both proofs swap the suprema and compare
  `⨆ (n : ℕ) (_ : ⟨χ,ν⟩ = n)` with `⨆ (_ : 0 ≤ ⟨χ,ν⟩)` (respectively
  `0 < ⟨χ,ν⟩`), using `Int.toNat`.

## Disjointness

For split `T` there are two disjointness results:

- `weightSpace_disjoint`: weight spaces of distinct characters are disjoint.
- `weightSpace_disjoint_iSup`: the weight space of a character outside a set
  of characters is disjoint from the sum of the weight spaces of that set.

Both come from the independence part of the published decomposition. The
second uses `iSupIndep.disjoint_biSup`.

## Regular cocharacters

Let `ν` and `ν'` be regular cocharacters (`IsRegularCocharacter j ν`: no root
pairs to zero with `ν`).

- `weightSpace_cocharacter_zero_of_isRegular`: the weight-zero space of `𝔾_m`
  through `ν ≫ j` equals `weightSpace j 0`. Take a nonzero `χ` with
  `⟨χ, ν⟩ = 0`. If `weightSpace j χ` were nonzero, `χ` would be a root
  paired to zero with `ν`. So its weight space is `⊥`.
- `iSup_nonneg_weightSpace_eq_of_isRegular`: the characters nonnegative on
  `ν` span `weightSpace j 0 ⊔ ⨆ (χ) (_ : 0 < ⟨χ,ν⟩), weightSpace j χ`. This
  needs no splitness.
- `iSup_pos_weightSpace_eq_iSup_roots`: the characters positive on `ν` span
  the same subspace as the roots positive on `ν`. The proof drops zero weight
  spaces and notes that a character with positive pairing is nonzero. This
  needs neither regularity nor splitness.
- `iSup_nonneg_weightSpace_le_of_isRegular`: if every root positive on `ν` is
  positive on `ν'`, the nonnegative span for `ν` lies in that for `ν'`. The
  trivial character pairs to `0` with `ν'`. A nonzero character with a
  nonzero weight space is a root, and it is positive on `ν` by regularity.
- `pos_of_iSup_nonneg_weightSpace_le` assumes `T` split, `ν'` regular, and the
  nonnegative span for `ν` inside that for `ν'`. Then every root `α` positive
  on `ν` is positive on `ν'`. Otherwise `⟨α, ν'⟩ < 0` by regularity, so
  `weightSpace j α` lies in a sum from which it is disjoint
  (`weightSpace_disjoint_iSup`). That forces it to be `⊥`, contradicting
  `α ∈ roots j`.
- `iSup_nonneg_weightSpace_eq_iff` and `iSup_nat_weightSpace_cocharacter_eq_iff`
  assume `T` split and `ν, ν'` regular. The nonnegative spans for `ν` and
  `ν'` agree exactly when `0 < ⟨α, ν⟩ ↔ 0 < ⟨α, ν'⟩` for every root `α`. The
  same holds for the sums `⨆ n : ℕ, weightSpace (ν ≫ j) (Gm.powerHom _ n)`
  and the corresponding sums for `ν'`. The two directions combine the
  previous two lemmas. The second form follows by rewriting with
  `iSup_nat_weightSpace_cocharacter`.

## Statements in terms of `nonnegativeWeightSpan`

- `iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan` (T split): the
  sum over `n : ℕ` of the weight spaces of `t ↦ t^n` for `ν ≫ j` equals
  `nonnegativeWeightSpan j ν`. This is `iSup_nat_weightSpace_cocharacter`.
- `nonnegativeWeightSpan_eq_of_isRegular` (ν regular, no splitness): the
  nonnegative weight span equals
  `weightSpace j 0 ⊔ ⨆ α, ⨆ (_ : α ∈ roots j ∧ 0 < ⟨α, ν⟩), weightSpace j α`.
  The proof combines `iSup_nonneg_weightSpace_eq_of_isRegular` and
  `iSup_pos_weightSpace_eq_iSup_roots`, then merges the two nested suprema into
  one over the conjunction (`iSup_and`).
- `nonnegativeWeightSpan_eq_iff` (T split, ν and ν' regular): the nonnegative
  weight spans of `ν` and `ν'` agree exactly when every root has the same sign
  on `ν` and `ν'`. This is `iSup_nonneg_weightSpace_eq_iff`.
