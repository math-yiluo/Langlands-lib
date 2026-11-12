# Single pieces of finite normalization covers

Author: Worker 185.

This is a helper module for the proof `Langlands.AlgebraicGeometry.LangWeil.finiteNormalizationCover`
of `Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverStatement`. It imports the
statement module unchanged. Its declarations are in the namespace
`Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction`.

Provenance: internal. `Piece` is an auxiliary structure for the proof, derived from one index of
the Library structure `FiniteNormalizationCover`. The results below are elementary lemmas
(topological Krull dimension, Noetherian induction) used to assemble the cover.

## Dimension from a chain of specializations

`le_topologicalKrullDim_of_chain`: in a `T₀` space `T`, a family `x : Fin (n + 1) → T` with
each `x i` specializing to `x (i + 1)` and different from it gives
`n ≤ topologicalKrullDim T` in `WithBot ℕ∞`. The proof takes the closures of the points in
reverse order. These are irreducible closed sets. They increase because each point specializes
to the next. They increase strictly: equal closures would make two consecutive points
specialize to each other, and in a `T₀` space this forces them to be equal. This strictly
increasing series of length `n` bounds the Krull dimension of the irreducible closed subsets
(`Order.LTSeries.length_le_krullDim`).

## The structure `Piece`

`Piece f`, for a morphism `f : X ⟶ S` of schemes, has the fields of one index of
`FiniteNormalizationCover f`:

- an affine scheme `base`, with an immersion `baseMap : base ⟶ S`;
- a scheme `source`, with an immersion `sourceMap : source ⟶ X`;
- a natural number `dimension` and a finite, surjective morphism
  `normalization : source ⟶ AffineSpace (ULift (Fin dimension)) base`;
- `comm`, the same equation as the cover's field `over`:
  `normalization ≫ (A^dimension_base ↘ base) ≫ baseMap = sourceMap ≫ f`.

The cover's field `dimension_le` (a bound on the dimension of the fibre of `f`) is replaced by
`fibreChain`. For every point `t` of `base`, this field gives points `x₀, …, x_dimension` of
`source`, all mapped to `t` by `normalization ≫ (A^dimension_base ↘ base)`, with each `xᵢ`
specializing to `xᵢ₊₁` and different from it. The structure does not use the field name `over`
because it is a token in this import closure; the cover field is written `«over»` below.

- `Piece.dimension_le` derives the cover's bound
  `dimension ≤ topologicalKrullDim (f.fiber (baseMap t))` from `fibreChain`. By `comm`, the
  images `sourceMap xᵢ` lie in `f⁻¹{baseMap t}`. Mathlib's homeomorphism `f.fiberHomeo` between
  `f.fiber s` and the subspace `f⁻¹{s}` carries them into the fibre. Specialization is preserved
  by the continuous map `sourceMap`, by the subspace and by the homeomorphism. Distinctness is
  preserved because the immersion `sourceMap` is injective (`isEmbedding`). The result follows
  from `le_topologicalKrullDim_of_chain`, since scheme fibres are `T₀`.
- `Piece.comp p a b h` transports a piece `p` of `f' : X' ⟶ S'` along immersions
  `a : X' ⟶ X` and `b : S' ⟶ S` with `f' ≫ b = a ≫ f`. Base, source, dimension, normalization
  and fibre chain are unchanged, `baseMap` becomes `p.baseMap ≫ b` and `sourceMap` becomes
  `p.sourceMap ≫ a`. Composites of immersions are immersions, and `comm` follows from `p.comm`
  and `h`. The `simp` lemmas `comp_sourceMap` and `comp_source` record the new fields.

## From pieces to a cover

`nonempty_cover_of_pieces`: if a finite set `s` of pieces of `f` has the property that every
morphism `Spec K ⟶ X`, for a field `K` in universe `u`, factors through `sourceMap` of some
piece in `s`, then `FiniteNormalizationCover f` is inhabited. The proof enumerates `s` by
`Fin (Fintype.card s)` and takes the fields of the cover from the pieces. `«over»` is `comm`,
`covers` is the hypothesis and `dimension_le` is `Piece.dimension_le`.

## Noetherian induction over primes

`exists_finite_cover_of_prime`: let `A` be a Noetherian ring and `cov : ι → Ideal A → Prop` a
relation saying that an index covers a prime. Assume each prime `Q` has some `g ∉ Q` and an index
`i` that covers every prime `P ⊇ Q` with `g ∉ P`. Then a finite set of indices covers every
prime of `A`. The proof shows, by well-founded induction on ideals for `>` (ideals of a
Noetherian ring satisfy the ascending chain condition), that for every ideal `I` a finite set of
indices covers all primes containing `I`. Apply this to `I = ⊥`. In the induction step:

- if `I = ⊤`, no prime contains `I`, and the empty set works;
- if `I` is prime, take `g` and `i` from the hypothesis. A prime `P ⊇ I` either avoids `g`, and
  is covered by `i`, or contains the strictly larger ideal `I + (g)`, and is covered by the
  induction hypothesis;
- otherwise there are `a, b ∉ I` with `ab ∈ I`. A prime `P ⊇ I` contains `a` or `b`, so it
  contains `I + (a)` or `I + (b)`. Both ideals are strictly larger than `I`, and the union of the
  two finite sets from the induction hypothesis works.
