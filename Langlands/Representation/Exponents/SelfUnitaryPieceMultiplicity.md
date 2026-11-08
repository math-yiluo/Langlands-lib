# Multiplicity of the self-intersection unitary geometric pieces

Author: Worker 1597. This is internal derived support for the generic
irreducibility argument of Waldspurger, *La formule de Plancherel pour les
groupes p-adiques d'après Harish-Chandra*, 2003, III.7.3 (printed p.276). That
argument counts the nonzero maps from the pieces of the geometric lemma
(III.3.3, printed p.268) into a regular square-integrable representation `σ`.
This file treats one piece of the geometric lemma whose two parabolic triples
are the same triple `(p, l, r)`, the case of a Jacquet module of an induction
from the same parabolic. It shows that the zero-real-part selected part of such
a piece has a space of maps into `σ` of length at most one. When that space is
nonzero and `σ` is regular, the double-coset representative `z` is a point of
the Levi `M`, and hence of the parabolic `P`.

## Generic Schur bound

`rank_intertwiningMap_le_one_of_injective` concerns complex representations
`ρ`, `σ'` and `σ` of one group, with `σ'` and `σ` irreducible and `σ`
admissible. Given an injective intertwiner `j : ρ → σ'`, the space of
intertwiners `ρ → σ` has rank at most one. If some map `f : ρ → σ` is nonzero,
then `j` is nonzero. Irreducibility of `σ'` makes `j` surjective, so `j` is an
equivalence `J`. Then `f ∘ J⁻¹ : σ' → σ` is nonzero, hence an equivalence `E`
by irreducibility of both. The published `admissibleSchur_homEquiv` identifies
the endomorphisms of `σ` with `ℂ`. Precomposition with the surjection
`J⁻¹ ∘ E⁻¹ : σ → ρ` (the published `HomSpace.comap_injective`) embeds the
intertwiners `ρ → σ` into these endomorphisms. If every map is zero, the space
has rank zero.

## Normalizer regularity forces the trivial double coset

`FullPieceConjugacy.mem_pointImage_of_isNormalizerRegular` takes a published
`FullPieceConjugacy` of `σ` with itself for the same parabolic and Levi. This
consists of an isomorphism `ψ` of `M` with
`ψ ≫ l ≫ p = l ≫ p ≫ Int(z⁻¹)` and a linear equivalence of `σ` with itself
intertwining `σ(m)` with `σ(ψ m)`. The lemma also assumes that the pullback of
`σ` to the literal Levi point image `M(F) ⊆ G(F)` is regular in the sense of
the published `IsNormalizerRegular`. Its conclusion is that `z` lies in the
point image of `l ≫ p`.

The proof reads the conjugacy on rational points as
`(l ≫ p)(ψ m) = z⁻¹ · (l ≫ p)(m) · z`, using the published
`rationalPoints_map_innerIso`. The inverse of `ψ` gives the reverse inclusion,
so `z` normalizes `M(F)`. If `z` were not in `M(F)`, then regularity would rule
out an equivalence between the `z`-conjugate of the pulled-back `σ` and itself.
But the inverse of the supplied linear equivalence is such an equivalence,
since conjugation by `z` on `M(F)` corresponds to `ψ` on `M`.

## Self-intersection pieces

The remaining results concern a published `GeometricLemmaIntersectionDatum D`
for the double coset of `z`, with both triples equal to `(p, l, r)`. They also
take a split component `a'` of the intermediate Levi `D.M'` and a smooth
representation `σ` of `M(F)`.

`unitaryPieceHom_rank_le_one_of_isIso` assumes that `D.p'` is an isomorphism,
that `σ` is irreducible and that `σ` is admissible. It proves that the
intertwiners from the published unitary piece `D.unitaryPieceRep a' σ` into
`σ` have rank at most one. The published `isIso_q'_of_isIso_p'` of
`SelfIntersectionLevi` makes the second intersection parabolic `D.q'` an
isomorphism as well. The published `unitaryFullPieceEmbedding` then embeds the
unitary piece injectively into `σ` transported by `D.fullLeviPointsEquiv`,
which is irreducible by `isIrreducible_comp_continuousMulEquiv_iff`. The generic
Schur bound finishes the proof.

The next three results take these further inputs:

- `σ` is tempered for normalized exponents (`hσtemp`);
- a Haar measure on `M(F) ⧸ Z(M(F))`, for which `σ` is square-integrable
  modulo the center (`hσsquare`);
- the published statement `TemperedSquareIntegrableUnitaryPartStatement`
  (Renard VII.2.4) as an explicit hypothesis (`hcriterion`);
- `σ` is irreducible.

`unitaryPieceHom_rank_le_one_of_squareIntegrable` proves the same rank bound
without assuming that `D.p'` is an isomorphism. If some map is nonzero, the
published `NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable` makes `D.p'`
an isomorphism and the previous result applies. Admissibility of `σ` is the
first component of square-integrability modulo the center. Otherwise the rank
is zero.

`selfUnitaryPieceConjugacyOfNonzeroMap` is a definition. From a nonzero map
`F : D.NonzeroUnitaryPieceMap a' σ σ` it constructs the `FullPieceConjugacy`
of `σ` with itself. It obtains fullness of `D.p'` as above and of `D.q'` from
`isIso_q'_of_isIso_p'`. It then applies the published
`unitaryFullPieceConjugacyOfNonzeroMap`.

`mem_pointImage_of_unitaryPieceHom_ne_zero` adds the regularity hypothesis on
the pullback of `σ` to `M(F)`. Under it, such a nonzero map places `z` in the
point image of `l ≫ p`.

## Selected parts

The last section also takes these inputs:

- `[Smooth G.X.hom]`;
- the published statement `ArbitraryParabolicQuotientCompactStatement` as an
  explicit hypothesis;
- a split component `a` of `M` with a published `ParabolicRootPresentation`
  of `(p, l, a)`;
- admissibility of the normalized Jacquet module of `σ` along the published
  intersection parabolic of `D` (`hJac`).

The selected part is the published `selectedWeightPart` of
`(D.pieceFunctor.obj σ).ρ`, for the split-component points of `a`, at the
characters of normalized real part zero. This is the selected part bounded in
`LeviUnitaryGluedHomBound` when both triples coincide. The published
`nonempty_selectedWeightPart_pieceFunctor_equiv` (Renard VII.2.5) identifies it
with the unitary piece `D.unitaryPieceRep a' σ`. Its Hom length is transported
by `HomSpace.length_congr_left`.

- `selectedPieceHomLength_le_one`: the selected part has Hom length at most one
  into `σ`. The proof rewrites length as `(Module.rank).toENat` with Mathlib's
  `Module.length_eq_rank`, then uses
  `unitaryPieceHom_rank_le_one_of_squareIntegrable`.
- `mem_pointImage_of_selectedPieceHomLength_ne_zero`: under the regularity
  hypothesis, a nonzero Hom length places `z` in the point image of `l ≫ p`.
  Nonzero length means the Hom space is nontrivial (`Module.length_eq_zero_iff`),
  which provides a nonzero map from the unitary piece.
- `mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero`: the same
  conclusion in the point image of `p`, by the published `pointImage_comp_le`.

## Scope

The field universe `u` and the carrier universe `v` of `σ` are independent.
The square-integrability criterion, the compactness statement, temperedness of
`σ`, Jacquet admissibility and normalizer regularity are explicit inputs. This
file does not prove them, nor the geometric lemma that supplies the data `D`.
It treats only pieces whose two parabolic triples coincide. It does not bound
pieces of a Jacquet module along a different parabolic.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
