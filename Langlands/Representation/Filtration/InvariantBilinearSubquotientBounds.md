# Bilinear length bounds for subrepresentations and quotients of filtered representations

Author: Worker 745.

This internal algebraic adapter extends the filtration bounds of
`Filtration.InvariantBilinearBounds`. Those bounds concern a filtered
representation itself. This module bounds an actual subrepresentation or an
actual quotient of a filtered representation. The main result is
`length_eq_zero_of_isSubOrQuotient`. Take filtrations `s` of `M` and `t` of
`N` whose graded pieces are zero or irreducible, and suppose that no pair of
graded pieces carries a nonzero `χ`-covariant bilinear form. Then no
subrepresentation-or-quotient `A` of `M` and subrepresentation-or-quotient `C`
of `N` carry a nonzero `χ`-covariant form either.

The coefficient field `k` and the monoid `G` are arbitrary. All carrier
universes are independent. No topology, smoothness or admissibility is used.
"Length" is the published `InvariantBilinear.length ρ σ χ : ℕ∞`, the module
length of the space `InvariantBilinear.forms ρ σ χ` of bilinear forms with
`B(g v, g w) = χ(g) B(v, w)`.

## Declarations

Namespace `Langlands.InvariantBilinear`.

- `ZeroOrIrreducible ρ`: the carrier of `ρ` is zero, or `ρ` is irreducible
  (`Representation.IsIrreducible`).
- `length_eq_zero_of_subsingleton_left`: a zero first carrier admits only the
  zero form.
- `length_le_of_injective_left σ χ f hf hτ`: for an injective intertwiner
  `f : ρ → τ` with `τ` zero or irreducible, `length ρ σ χ ≤ length τ σ χ`. If
  `τ` is irreducible, `f` is surjective or zero (Mathlib's
  `Representation.IsIrreducible.surjective_or_eq_zero`). A surjective `f` is
  an equivalence, and the published `length_congr_left` applies. If `f` is
  zero, injectivity makes the carrier of `ρ` zero.
- `length_le_of_surjective_left σ χ f hf`: for a surjective intertwiner
  `f : ρ → τ`, `length τ σ χ ≤ length ρ σ χ`. Pullback along `f` (the published
  `comapLeft`, injective by `comapLeft_injective`) embeds the forms on `τ`
  into the forms on `ρ`.
- `subrepresentationComap f S`: the preimage of an invariant subspace under an
  intertwining map.
- `filtrationComap f hf t`: the pullback of an actual filtration
  (`ObjectRepFiltration`) of `B` along an injective intertwiner `f : A → B`. It
  is built with the published `ObjectRepFiltration.ofSubrepresentations`.
  Injectivity is used to show that the first step is zero.
- `filtrationComapGradedMap f hf t i` and
  `filtrationComapGradedMap_injective`: the map induced by `f` from each
  graded piece of the pulled-back filtration to the corresponding graded
  piece of `t`, and its injectivity.
- `IsSubOrQuotient A M`: there is an injective intertwiner `A → M` or a
  surjective intertwiner `M → A`.
- `length_le_sum_of_injective_left`: for injective `f : A → M` and a
  filtration `t` of `M` with zero or irreducible pieces, `length A σ χ` is at
  most the sum over `i` of the lengths for the graded pieces of `t`. The proof
  applies the published `length_le_sum_left` to the pulled-back filtration,
  then `length_le_of_injective_left` piece by piece.
- `length_le_sum_of_isSubOrQuotient_left`: the same bound when `A` is a
  subrepresentation or a quotient of `M`. For a quotient it uses
  `length_le_of_surjective_left` and then `length_le_sum_left` for `M`.
- `length_eq_zero_of_isSubOrQuotient`: the main result stated above. It
  applies the previous bound in the first argument and then, through the
  published `length_flip`, in the second argument.

## Provenance

The provenance is internal. The module is linear algebra over the published
`InvariantBilinear` and `ObjectRepFiltration` definitions. It is used in the
proof of Ze80 Proposition 1.11(a) (task
`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`). There it replaces the step "an
irreducible subquotient pairs nontrivially with some Jordan–Hölder factor" in
BZ77 §4.8 (Bernstein and Zelevinsky 1977, `bernstein-zelevinsky-1977-induced-i`,
proof of Lemma 4.7(b), printed p.455) by a length count that needs no
irreducible subrepresentation. No source result is restated here.

## Dependency audit

The only direct import is `Langlands.Representation.Filtration.InvariantBilinearBounds`.
Its transitive `Langlands` closure is `Filtration.Definitions`,
`Filtration.InvariantBilinear`, `Filtration.InvariantBilinearBounds` and
`Filtration.ObjectDefinitions`, at Library commit
`9076dbdeff7e1d9a1bddd23c2f62e11d180814a1`. It contains no derivative,
induction, classification, segment or irreducibility-criterion module. So no
excluded result of task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` is used.
