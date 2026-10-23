# Finite-index restriction preserves and reflects semisimplicity (proof)

Author: Worker 252.

The theorem `Langlands.Weil.representationFiniteIndexRestrictionSemisimplicity`
proves the published proposition
`Langlands.Weil.RepresentationFiniteIndexRestrictionSemisimplicity.{uG, uV}`
from [`InductionFinitenessStatements`](InductionFinitenessStatements.md).
Import `Langlands.Weil.Representation.FiniteIndexRestrictionSemisimplicityProof`
to use it.

## Closing theorem

`Langlands.Weil.representationFiniteIndexRestrictionSemisimplicity :
RepresentationFiniteIndexRestrictionSemisimplicity.{uG, uV}`.

Its complete unapplied type is exactly the published proposition, with the two
independent universes `uG` and `uV`, and it takes no further arguments. So it
quantifies over exactly the data of the statement: a group `G : Type uG`, a
subgroup `H` with `[H.FiniteIndex]`, a finite-dimensional complex vector space
`V : Type uV`, and `σ : Representation ℂ G V`. It concludes
`Representation.IsSemisimpleRepresentation (σ.comp H.subtype) ↔
Representation.IsSemisimpleRepresentation σ`. The restricted representation is
the actual composite `σ.comp H.subtype`; there is no separate representation of
`H` as input. `H` need not be normal. There is no hypothesis of topology,
continuity, finite image, irreducibility or positive dimension, so the
zero-dimensional carrier is included. Semisimplicity is Mathlib's predicate:
the lattice of subrepresentations is complemented.

## Published inputs

The proof uses two published theorems by their Lean names:

- `Langlands.finiteDimensionalNormalRestrictionSemisimplicity`
  (module `Langlands.Representation.Category.NormalRestrictionSemisimplicity`):
  over any field, a semisimple finite-dimensional representation stays
  semisimple on restriction to a normal subgroup.
- `Langlands.finiteIndexSemisimplicityAscent`
  (module `Langlands.Representation.Category.FiniteIndexSemisimplicity`):
  over a field of characteristic zero, a representation whose restriction to a
  normal subgroup of finite index is semisimple is itself semisimple.

Both are applied with coefficient field `ℂ`, which has characteristic zero. The
carrier `V` is finite-dimensional by the target's hypothesis.

## Helper declarations (namespace `Langlands.Weil.FiniteIndexRestrictionSemisimplicity`)

- `subrepresentationOrderIsoOfRangeEq ρ ρ' h`: let `ρ` and `ρ'` be
  representations of two monoids `K` and `K'` on the same `k`-module `V`. If
  `Set.range ρ = Set.range ρ'`, this is an order isomorphism between their
  subrepresentation lattices that keeps the underlying submodule. A submodule
  stable under every `ρ x` is stable under every `ρ' x'`, because
  `ρ' x' = ρ y` for some `y`, and conversely. The two inverse maps are the
  identity on submodules, and the orders are inclusion of submodules.
- `isSemisimpleRepresentation_iff_of_range_eq`: under the same hypothesis, `ρ`
  is semisimple if and only if `ρ'` is. Mathlib's
  `OrderIso.complementedLattice_iff` transfers the complemented-lattice property
  along the isomorphism above.
- `range_comp_subgroupOf_subtype σ hNH`: for subgroups `N ≤ H` of a group `G`
  and `σ : Representation k G V`, the representation
  `(σ.comp H.subtype).comp (N.subgroupOf H).subtype` and `σ.comp N.subtype`
  have the same set of operators. An element of `N.subgroupOf H` is an element
  `x` of `H` whose image in `G` lies in `N`, and it acts by `σ x`. Conversely an
  element `n` of `N` lies in `H` because `N ≤ H`, and so defines an element of
  `N.subgroupOf H` acting by `σ n`.

## Proof of the closing theorem

1. **A normal subgroup inside `H`.** The normal core `H.normalCore` is normal in
   `G` (Mathlib's `Subgroup.normalCore_normal`), has finite index in `G` because
   `H` does (`Subgroup.finiteIndex_normalCore`), and is contained in `H`
   (`Subgroup.normalCore_le`). The proof records only these three properties of
   a subgroup `N`.
2. **Its trace in `H`.** The subgroup `N.subgroupOf H` of `H` is normal in `H`
   (`Subgroup.normal_subgroupOf`, since `N` is normal in `G`) and has finite
   index in `H` (`Subgroup.instFiniteIndex_subgroupOf`, since `N` has finite
   index in `G`). These are found by instance search.
3. **Comparing the two restrictions to `N`.** By
   `range_comp_subgroupOf_subtype` and
   `isSemisimpleRepresentation_iff_of_range_eq`, restricting `σ.comp H.subtype`
   further to `N.subgroupOf H` gives a semisimple representation exactly when
   `σ.comp N.subtype` is semisimple.
4. **Restriction implies the original (`→`).** Suppose `σ.comp H.subtype` is
   semisimple. Normal descent in the group `H`, applied to its normal subgroup
   `N.subgroupOf H`, makes the further restriction semisimple. By step 3,
   `σ.comp N.subtype` is semisimple. Ascent from the normal finite-index
   subgroup `N` of `G` then makes `σ` semisimple.
5. **The original implies restriction (`←`).** Suppose `σ` is semisimple.
   Normal descent from `G` to `N` makes `σ.comp N.subtype` semisimple. By step 3
   the restriction of `σ.comp H.subtype` to `N.subgroupOf H` is semisimple.
   Ascent from the normal finite-index subgroup `N.subgroupOf H` of `H` then
   makes `σ.comp H.subtype` semisimple.

## Provenance and scope

This is a derived proof in generic algebraic representation theory over `ℂ`.
It is not a verbatim theorem of Tate. The statement's source map, in
[`RestrictionInduction`](RestrictionInduction.md) and
[`InductionFinitenessStatements`](InductionFinitenessStatements.md), cites John
Tate, *Number theoretic background*, in *Automorphic Forms, Representations and
L-Functions*, Proc. Sympos. Pure Math. 33, Part II (1979), section 2.1, printed
pages 9–10 (PDF pages 18–19); registered literature ID
`tate-1979-number-theoretic-background`. I read those pages. On page 9
representations are continuous finite-dimensional complex representations, and
restriction maps for Weil groups are introduced. On page 10 Tate defines
restriction and induction between virtual representation groups for a finite
separable extension, by identifying the smaller Weil group with a closed
subgroup of finite index, with the usual Frobenius reciprocity. Tate states no
semisimplicity assertion there; the source map labels this component as derived
general representation theory.

The route through the normal core is the one listed as a proof direction in
`InductionFinitenessStatements.md`. The two descent and ascent steps are the
published theorems above. The proof of the ascent theorem follows the averaging
argument of Bernstein–Zelevinsky, Lemma 2.9(a), and the descent theorem has a
finite-dimensional Clifford/socle proof; see their own Markdown files. The new
content here is the passage through `N.subgroupOf H` and the comparison of
restrictions by equality of operator images.

Only this proof pair is added. The statement pair
`InductionFinitenessStatements.lean`/`.md` and everything it imports are
unchanged. The other three components (induced dimension, induced finite image,
induced semisimplicity), their aggregate, topology, compatibility, actual local
specialization and local Langlands statements are not addressed.

## Checks

The module imports the statement module and the two input modules above. It
compiles in Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or
warnings. Inspecting the closing theorem reports level parameters `uG uV` and
the axioms `propext`, `Classical.choice` and `Quot.sound` only. A private check,
not part of this pair, confirmed that the theorem's complete unapplied type is
syntactically the constant
`Langlands.Weil.RepresentationFiniteIndexRestrictionSemisimplicity.{uG, uV}`.
It also applied the theorem to a group in `Type 2` with the zero-dimensional
carrier `Fin 0 → ℂ`, and to a group in `Type` with a carrier in `Type 3`.
