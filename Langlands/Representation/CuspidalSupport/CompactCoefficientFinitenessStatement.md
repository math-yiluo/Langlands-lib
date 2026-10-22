# Fixed-level finiteness of compact-coefficient classes on `G°`

Author: Worker 277. This statement pair belongs to task
`1ae6ffd0-4e90-4d07-a45d-f9b291d2cf99`, revision 1. It is a proposition
definition. Neither it nor the source reduction explained below is proved in
Lean here.

## The proposition

`Langlands.CuspidalSupport.CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV}`
is the closed proposition

\[
\forall p\ \text{prime},\ \forall F,\ \forall T,\ \forall n>0,\ \forall B,\ \
\forall K\le G^\circ\ \text{open},\ \ K\ \text{compact}\ \Longrightarrow\
\{\,[\omega]\ :\ \omega^K\ne 0\,\}\ \text{is finite}.
\]

In detail, the quantifiers and objects are as follows.

- `p : ℕ` with `[Fact p.Prime]`, an actual `F : PadicField.{uF} p` (a finite
  field extension of `Padic p`), and a compatible local-field realization
  `T : F.TopologicalData`. All topological objects use `letI := T.topology`.
- A total rank `n : ℕ` with the explicit hypothesis `0 < n`, and an ordered
  block shape `B : BlockShape n`: positive block sizes `n₁, …, n_r` with sum
  `n`. The product Levi is `B.Levi F.Carrier`, the product of the groups
  `GL(nᵢ, F)`, with the product of the matrix-unit topologies.
- `G° = determinantUnitSubgroup T B`, the published subgroup of tuples whose
  residue-normalized determinant absolute value equals one in every block,
  with its subspace topology.
- `K : OpenSubgroup (determinantUnitSubgroup T B)`, an actual open subgroup of
  `G°`, together with the hypothesis
  `IsCompact (K : Set (determinantUnitSubgroup T B))`.
- The conclusion is
  `Set.Finite (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup)`.

`CompactCoefficientClass.{uF, uV} G°` is the published quotient, by actual
isomorphism, of irreducible smooth complex representations of `G°` with
carriers in `Type uV` whose coefficients against every smooth algebraic dual
functional have compact support. Its universe is `max uF (uV + 1)`, and the
finiteness is `Set.Finite` at that universe. `fixedStratum K.toSubgroup` is the
set of classes satisfying the published quotient predicate `HasFixedVector`.
By `hasFixedVector_ofRep_iff_exists`, a class satisfies it exactly when a
representative has a nonzero vector fixed by every element of `K`.

The field universe `uF` and the carrier universe `uV` are independent
universe parameters of the declaration. The class universe is the genuine
quotient universe; no resizing, smallness, or choice of representatives occurs.
The proposition does not assume admissibility, finite dimension, a prescribed
central character, unitarity, finite or bounded length, or any finiteness as
data. Every carrier may have arbitrary dimension and carries no topology. The
proposition is genuinely about product Levis, not only a single block.

The exact unapplied declaration was compiled and inspected with the project
Lean service: it is a `def` returning `Prop`, with level parameters `uF, uV`,
and with only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound` in its dependency closure.

## Original source

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F) where F is a non-Archimedean local field*, Russian Mathematical Surveys
**31**:3 (1976), 1–68, English translation.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
  Printed page numbers are cited; the PDF page index is one less.

The target is Theorem 4.14, printed p.41:

> Let G = G_α and let N be a congruence subgroup of G. Then G° has only finitely
> many non-isomorphic finite irreducible representations ω such that
> ω(ε_N) ≠ 0.

Other locators read for this statement:

- §3.1, p.28: the field `F`, its integers `R`, the congruence subgroups
  `N_i = 1 + ϖ^i M(n, R)`, which form a fundamental system of neighbourhoods of
  the identity of `GL(n, F)` by compact open subgroups, and `Γ = GL(n, R)`.
- §§3.3–3.4, pp.29–30: a partition `α = (n₁, …, n_r)` of `n` into consecutive
  segments, `G_α = ∏ G_{nᵢ}` embedded in `G_n`, and the congruence subgroups
  `N_i(α) = N_i ∩ G_α` of `G_α`.
- §3.20, p.34: `G° = ∏ G°_{nᵢ}` with `G°_{nᵢ} = {g : det g ∈ R*}`; properties
  (a) `Γ ⊆ G°` and (b) `G°` is an open normal subgroup of `G`.
- §3.21, pp.34–35: Harish-Chandra's theorem, whose condition (4) is finiteness
  of the restriction to `G°`; this is why the theorem concerns `G°`.
- §2.40, p.26: “finite” representations, defined by compactly supported matrix
  elements; §2.39, p.26, for matrix elements.
- §1.26, p.13, and §2.4, pp.15–16: `ε_Γ` for a compact subgroup `Γ` is the
  normalized Haar measure, and `π(ε_Γ)` is a projection with image `E^Γ`.
- Proof of 4.14 in §4.16, p.41, with Remark 4.13, pp.40–41; and the use in
  Theorem 4.17, pp.41–42.

## Correspondence of conventions

**The group.** A `BlockShape n` is an ordered list of positive block sizes with
sum `n`, which is exactly the data of the source's partition `α` into
consecutive segments, and `B.Levi F.Carrier` is `G_α`. The source writes `F`
for a non-Archimedean local field; here it is an actual finite extension of
`ℚ_p` with its canonical local-field topology, as in the published
`DeterminantUnit` pair. That pair identifies `determinantUnitSubgroup T B` with
the source's `G°`: a determinant has normalized absolute value one exactly
when it is a unit of the valuation ring, imposed block by block.

**“Finite” representations.** The source's “finite irreducible representation”
of `G°` is an irreducible algebraic (smooth) representation all of whose matrix
elements `g ↦ ⟨ξ̃, ω(g⁻¹)ξ⟩`, with `ξ̃` in the smooth contragredient, have
compact support. The published class `CompactCoefficientClass` uses exactly
this condition, with algebraic functionals that are smooth vectors of the dual
action; its own Markdown records the `g` versus `g⁻¹` convention and why the
support conventions agree. The word “finite” does not mean finite dimension.

**The fixed-level condition.** For a compact open subgroup `N`, §1.26 defines
`ε_N` as the normalized Haar measure on `N`, and §2.4 shows that `ω(ε_N)` is a
projection of `V` with image `V^N`. Hence `ω(ε_N) ≠ 0` holds exactly when
`V^N ≠ 0`, that is, when `ω` has a nonzero `N`-fixed vector. This is the
predicate `HasFixedVector` used here. It is a reformulation of the source's
condition, not an extra hypothesis, and the averaging operator is not
constructed in Lean.

**Isomorphism classes.** “Finitely many non-isomorphic representations” is
finiteness of the corresponding set of isomorphism classes, which is the set
`fixedStratum`. For each fixed `uV`, the proposition concerns representations
with carriers in `Type uV`. Every irreducible smooth representation of `G°` has
countable dimension, by the argument in the proof of §2.11 (p.18) using that
`G°` is countable at infinity, so each universe level already contains
representatives of all such classes. This remark explains why a fixed carrier
universe loses nothing; the proposition neither uses nor proves it.

## The derived compact-open formulation

The source quantifies over congruence subgroups `N` of `G = G_α`. This
proposition instead quantifies over all compact open subgroups `K` of `G°`. The
two formulations are related as follows, in the source's setting.

1. Each congruence subgroup `N_i(α)` is a compact open subgroup of `G` that lies
   in `Γ_α = ∏ GL(nᵢ, R)`, hence in `G°` by §3.20(a). It is therefore a compact
   open subgroup of `G°`, so the present proposition contains the source's
   assertion.
2. Conversely, let `K` be a compact open subgroup of `G°`. Since `G°` is open
   in `G` (§3.20(b)), `K` is an open neighbourhood of the identity in `G`. The
   congruence subgroups form a fundamental system of neighbourhoods of the
   identity (§3.1, transported to `G_α` by §3.4), so some congruence subgroup
   `N` satisfies `N ⊆ K`. Every `K`-fixed vector is `N`-fixed, so the `K`-fixed
   stratum is contained in the `N`-fixed stratum, which is finite by Theorem
   4.14. A subset of a finite set is finite.

This reduction is a source-to-statement explanation only; it is not formalized
in this unit, and the congruence subgroups are not constructed here. Step 2
uses only that `K` is open. The compactness hypothesis is retained because the
formulation is over compact open level subgroups.

**Scope restrictions.** The source allows any non-Archimedean local field
(§3.1), including fields of positive characteristic. This proposition covers
only finite extensions of `ℚ_p`, the fields of the published `G°`
construction. The total rank is required to be positive, as the source treats
`GL(n)` with `n ≥ 1`; the rank-zero product, the trivial group, is not covered.
The topology on `G°` is the subspace topology from `letI := T.topology`; no
other topology is used.

## What is not assumed

The proof in §4.16 bounds the dimensions of irreducible modules over the
Hecke corner algebra `ℋ_N(G°)` of §2.10 (Remark 4.13, with 4.7–4.8), proves
that this algebra is finitely generated (the method of 4.9), embeds its
`s`-dimensional representations into tuples of matrices, uses trace
polynomials of the isotypic elements `ε_N^ω` of §2.42, and applies the Hilbert
basis theorem. None of these results, nor the Harish-Chandra theorem of §3.21,
is assumed or supplied as data by the proposition. Its later use, the
pointwise-finite sum of isotypic projectors in Theorem 4.17, is also not
stated here.

## Provenance and dependencies

The provenance is the source Theorem 4.14 in a derived form: the source's
congruence-subgroup assertion and `ω(ε_N) ≠ 0` condition are replaced by all
compact open subgroups of `G°` and nonzero fixed vectors, for the reasons
above. Only the following published modules are imported, by Lean name and
unchanged:

- `Langlands.Representation.CompactCoefficient.Classes`, for
  `CompactCoefficientClass`, `HasFixedVector`, and `fixedStratum`;
- `Langlands.Representation.CuspidalSupport.DeterminantUnit`, for
  `determinantUnitSubgroup`.

Mathlib supplies `OpenSubgroup`, `IsCompact`, and `Set.Finite`. The
environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
