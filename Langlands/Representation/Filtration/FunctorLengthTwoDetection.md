# Detecting length two through a functor

Module `Langlands.Representation.Filtration.FunctorLengthTwoDetection`, namespace
`Langlands.FunctorLengthTwo`.

This is a helper module for the proof of Zelevinsky, *Induced representations of
reductive p-adic groups II* (1980), Proposition 4.6. It contains no p-adic input.
It isolates the lattice-theoretic part of step (3) of the proof of that
proposition, where the highest derivative detects the composition series of a
product of two segment socles. In the source, the derivative is exact and the
derivative of the product has length two. Here the only property of the functor
that is used is strict monotonicity of the images of inclusions of
subrepresentations. The abstract form below is our own (derived) formulation of
that argument. It is not quoted from the source.

## Representations of a monoid

Fix representations `ρ : Representation k G V` and `σ : Representation k G W` of a
monoid `G` over a field `k`. `LengthCriterionProof.quotientRep S T` denotes the
quotient of `T` by the preimage of `S` in `T`.

- `subtypeMap K` is the inclusion of a subrepresentation `K` of `ρ` as an
  intertwining map `K.toRepresentation → ρ`. `subtypeMap_apply` evaluates it.
- `nonempty_quotientBotTop_equiv σ`: the quotient `⊤ / ⊥` is equivalent to `σ`.
  The equivalence is the descent of the inclusion of `⊤`.
- `nonempty_quotientBot_equiv K`: the quotient `K / ⊥` is equivalent to
  `K.toRepresentation`. This is `LengthTwo.nonempty_gradedEquiv` for
  `subtypeMap K`, followed by the previous item.
- `nonempty_equiv_range g hg`: an injective intertwining map `g : ρ → σ` gives an
  equivalence of `ρ` with `g.range.toRepresentation`.
- `ne_bot_of_isIrreducible`: an irreducible subrepresentation is not `⊥`.
- `eq_bot_or_eq_of_le_of_isIrreducible`: if `K` is irreducible and `L ≤ K`, then
  `L = ⊥` or `L = K`. The proof pulls `L` back along `subtypeMap K`.
- `inf_covBy_of_covBy_sup`: if `a ⋖ a ⊔ b`, then `a ⊓ b ⋖ b`. The lattice of
  subrepresentations is order isomorphic to a lattice of submodules
  (`Subrepresentation.subrepresentationSubmoduleOrderIso`), which is modular.
- `eq_bot_or_eq_or_eq_top s hs huniq M`: let `s` be a two-step filtration of
  `Rep.of ρ` with simple factors whose middle step `S = s.subrepresentation 1` is
  the only irreducible subrepresentation of `ρ`. Then every subrepresentation `M`
  is `⊥`, `S` or `⊤`. If `M ⊓ S = ⊥` and `M ≠ ⊥`, then `S ⊔ M = ⊤`, and the
  previous item makes `M` irreducible. So `M = S`, a contradiction. If
  `M ⊓ S = S`, then `S ≤ M`, and `S ⋖ ⊤` gives `M = S` or `M = ⊤`.
- `comap_bot_of_injective`, `comap_top`, `comap_comap_symm`: preimages of `⊥` and
  `⊤`, and preimage along an equivalence followed by its inverse.
- `exists_middle_of_equiv φ s hs huniq θ hne`: transport of the previous lattice
  description along an equivalence `φ : ρ ≃ σ`. The data are a two-step
  filtration `s` of `Rep.of σ` with simple factors and a unique irreducible
  subrepresentation `s.subrepresentation 1`, an equivalence `θ : τ ≃ υ`, and the
  hypothesis that the bottom factor of `s` is not equivalent to `υ`. Then `ρ` has
  a subrepresentation `S` with `S ≠ ⊥` and `S ≠ ⊤`, every subrepresentation of
  `ρ` is `⊥`, `S` or `⊤`, and `S` is not equivalent to `τ`. The witness is the
  preimage of `s.subrepresentation 1` under `φ`.

## Counting in a three-element lattice

For a bounded partial order, `threeCount M` is `0` if `M = ⊥`, `2` if `M = ⊤`
and `M ≠ ⊥`, and `1` otherwise. `threeCount_le_two` bounds it.
`threeCount_eq_one_iff` states that `threeCount M = 1` exactly when `M ≠ ⊥` and
`M ≠ ⊤`. `threeCount_strictMono`: if every element is `⊥`, `S` or `⊤`, with `S`
different from `⊥` and `⊤`, then `threeCount` is strictly monotone.

## The detection theorem

Let `D : SmoothRep k G ⥤ SmoothRep k G'` be a functor between categories of
smooth representations of topological groups over the same field.
`SmoothRep.subtype X K` is the inclusion of the smooth subrepresentation of `X`
on `K`, and `SmoothRep.hom` is the underlying intertwining map of a morphism.

`lengthTwo_of_strictMono X Y f hf hY hmono S hS0 hS2 hS hDY hne` assumes:

- `f : X → Y` is a nonzero intertwining map and `Y` is irreducible;
- `hmono`: for subrepresentations `K₁ < K₂` of `X`, the range of
  `D.map (SmoothRep.subtype X K₁)` is strictly smaller than the range of
  `D.map (SmoothRep.subtype X K₂)`;
- `S` is a subrepresentation of `D X` different from `⊥` and `⊤`, and every
  subrepresentation of `D X` is `⊥`, `S` or `⊤`;
- `D Y` is irreducible, and `S` is not equivalent to `D Y`.

It concludes that `X` has a two-step filtration `s` with simple factors, the top
factor `s.gradedRepresentation 1` is equivalent to `Y`, the bottom factor
`s.gradedRepresentation 0` is not equivalent to `Y`, and every irreducible
subrepresentation of `X` equals `s.subrepresentation 1`.

Proof. Let `Φ K` be the range of `D.map (SmoothRep.subtype X K)`. By `hmono`,
`Φ` is strictly monotone, so `μ = threeCount ∘ Φ` is strictly monotone with
values at most `2`. Hence every `K` with `K ≠ ⊥` and `K ≠ ⊤` has `μ K = 1` and
`Φ K = S`.

Key step: no such `K` is equivalent to `Y`. An equivalence `K ≃ Y` gives an
isomorphism `D (K) ≅ D Y` (`SmoothRep.mkIso` and `D.mapIso`). So `D (K)` is
irreducible and the map `D.map (SmoothRep.subtype X K)` is injective or zero. If
it is injective, its source is equivalent to its range `S`, and `S` is equivalent
to `D Y`, against `hne`. If it is zero, its range `S` is `⊥`, against `hS0`.

Let `K₀` be the kernel of `f`. It is not `⊤` because `f ≠ 0`. Its range is
`⊤` because `Y` is irreducible, so `f` is surjective. It is not `⊥`: otherwise
`f` is bijective, `X ≅ Y`, `D X` is irreducible, and `S` is `⊥` or `⊤`. The
counts give `μ K₀ = 1`, and `LengthTwo.covBy_of_count` gives `⊥ ⋖ K₀ ⋖ ⊤`. The
filtration is `s = LengthTwo.twoStep K₀`. It has simple factors by
`LengthTwo.twoStep_hasSimpleFactors`. Its top factor `X / K₀` is equivalent to
`Y` through the descent of `f`. Its bottom factor is equivalent to `K₀`, and the
key step shows that it is not equivalent to `Y`.

Uniqueness. Let `K` be an irreducible subrepresentation. If `K ≤ K₀`, then
`K = K₀` because `⊥ ⋖ K₀` and `K ≠ ⊥`. Otherwise `K ⊓ K₀ = ⊥` because `K` is
irreducible, so `K ≠ ⊤` and `f` restricted to `K` is injective. By Schur's lemma
(`Representation.IsIrreducible.bijective_or_eq_zero`), this restriction is
bijective or zero. If it is bijective, `K` is equivalent to `Y`, against the
key step. If it is zero, injectivity forces `K = ⊥`, which is impossible.
