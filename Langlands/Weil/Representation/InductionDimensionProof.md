# Dimension and rank of finite-index Weil induction

Worker 265 proves the published proposition
`Langlands.Weil.RepresentationInductionDimension.{uG,uV}` from
[`InductionFinitenessStatements`](InductionFinitenessStatements.md) by the
closed theorem `Langlands.Weil.representationInductionDimension`. The module
imports the unchanged statement module
`Langlands.Weil.Representation.InductionFinitenessStatements` and the published
`Langlands.Weil.Representation.Induction`. Neither the statement pair nor
anything it imports is edited.

## Proved statement

The theorem's complete unapplied type is the named proposition at its two
independent universes `uG` and `uV`. For every `G : Type uG` with `[Group G]`,
every `H : Subgroup G` with `[H.FiniteIndex]`, every `V : Type uV` with
`[AddCommGroup V]`, `[Module ℂ V]` and `[FiniteDimensional ℂ V]`, and every
`ρ : Representation ℂ H V`, it proves both

- `FiniteDimensional ℂ (Representation.IndV H.subtype ρ)`, and
- `Module.finrank ℂ (Representation.IndV H.subtype ρ) = H.index * Module.finrank ℂ V`.

The carrier is Mathlib's actual tensor/coinvariant space `IndV`, the quotient
of `ℂ[G] ⊗[ℂ] V` by the diagonal action of `H`. A result only about the
equivariant-function model would not meet the target; that model occurs only
inside the proof. There is no hypothesis of normality of `H`, topology,
continuity, finite image, irreducibility, positive dimension, or finite
dimension of the induced carrier. The zero-dimensional case is covered by the
same argument; no case split is made.

## Implemented proof

After introducing the data, `classical` supplies the decidability of the
right-coset relation that Mathlib's comparison requires. The proof then
proceeds in four steps.

1. **Bundling.** `A := FiniteRepresentation.of ρ` packages `ρ` as an object of
   the Library's category of finite-dimensional representations, keeping the
   carrier `V` itself.
2. **Linear equivalence with the function model.** Let `e` be the underlying
   linear equivalence of `Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))`.
   It runs from `IndV H.subtype ρ` to `coindV H.subtype ρ`, the space of
   functions `f : G → V` with `f(s*g) = ρ(s)(f(g))`. Mathlib's forward map
   sends the class of `g ⊗ v` to the function supported on the right coset
   `H*g`, with value `ρ(s)(v)` at `s*g`. Its inverse sends `f` to the finite
   sum of the classes of `gᵢ ⊗ f(gᵢ)` over right-coset representatives `gᵢ`.
   `Rep.indCoindIso` takes `A : Rep.{max w u} k S`, where `u` is the
   coefficient ring's universe. For `ℂ : Type` this is `max uV 0 = uV`, so
   `Rep.of ρ : Rep.{uV} ℂ H` is accepted. This identifies neither `uG` nor `uV`
   with the other.
3. **Finite dimension.** The Library instance
   `Langlands.FiniteRepresentation.finite_coindV H A` shows that
   `coindV H.subtype ρ` is finite-dimensional. It uses
   `Langlands.FiniteRepresentation.Induction.coordinates`, the linear
   equivalence from that space to functions on the right cosets, given by
   evaluation at chosen representatives. Since `H` has finite index, this is
   a finite product of copies of `V`. Transporting along `e.symm` with
   `Module.Finite.equiv` gives the first conjunct for `IndV`.
4. **Rank.** `LinearEquiv.finrank_eq` for `e` rewrites the rank of `IndV` as
   the rank of `coindV H.subtype ρ`. By definition, this is
   `(FiniteRepresentation.induce H A).rank`. The Library theorem
   `Langlands.FiniteRepresentation.rank_induce H A` equates it with
   `H.index * A.rank`, and `A.rank` is by definition `Module.finrank ℂ V`.
   That theorem computes the rank of the coset-coordinate space as the number
   of right cosets times `finrank ℂ V`. It then identifies that number with
   `H.index` by `QuotientGroup.card_quotient_rightRel`.

Two closing `example`s check the result. The first assigns the entire
unapplied constant `@representationInductionDimension.{uG, uV}` to
`RepresentationInductionDimension.{uG, uV}`. The second assigns it to the
statement's fully unfolded universally quantified formula. The theorem's level
parameters are `[uG, uV]`, in the statement's order.

A development check in the pinned environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the module with no errors or warnings. Inspecting the theorem reported
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and scope

The cited original is John Tate, *Number theoretic background*, in
*Automorphic Forms, Representations and L-Functions*, Proceedings of Symposia
in Pure Mathematics 33, Part II (1979), section 2.1, printed pages 9–10 / PDF
pages 18–19. Registered literature ID: `tate-1979-number-theoretic-background`.
Retained file SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
On page 9, Tate takes representations to be continuous homomorphisms into
`GL(V)` for finite-dimensional complex `V`. On page 10 he gives restriction
and induction maps between the virtual representation groups of `W_F` and
`W_E` for a finite separable `E/F`. These satisfy the usual Frobenius
reciprocity, because `W_E` is a closed subgroup of finite index in `W_F`.
Tate does not state the dimension formula. As the statement Markdown and
[`RestrictionInduction`](RestrictionInduction.md) record, this is derived
generic algebraic representation theory over `ℂ`. It is the standard fact that
induction from a subgroup of finite index `[G:H]` multiplies dimension by
`[G:H]`. It is not a verbatim theorem of Tate.

The implemented route consists of three reused results, invoked by Lean name
with no copied or adapted code:

- Mathlib's `Rep.indCoindIso`, by Amelia Livingston, in
  `Mathlib/RepresentationTheory/FiniteIndex.lean` (line 178). It is built
  from `Rep.indToCoind`, `Rep.coindToInd` and their two inverse laws.
- `Representation.equivOfIso`, in `Mathlib/RepresentationTheory/Rep/Basic.lean`
  (line 174). Both files are at the pinned Mathlib commit
  `5ed2965256430c3649e86755f9576b54eca72435`.
- Worker 17's published coset-coordinate results `Induction.coordinates`,
  `finite_coindV` and `rank_induce` in
  [`Induction`](Induction.md).

This proves only the dimension component. The finite-image component, both
semisimplicity components, their aggregate assembly, topology, induction
compatibilities, actual local specialization and the Langlands correspondence
remain separate work.
