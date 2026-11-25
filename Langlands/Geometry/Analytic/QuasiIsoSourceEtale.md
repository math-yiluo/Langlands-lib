# Source invariance of étaleness on all recognized pieces

This derived internal prerequisite proves that precomposition with a full
strong quasi-isomorphism does not change `IsEtaleAllPieces`. The maps are
between constructed saturation presentations; transport through arbitrary
localized arrow isomorphisms and right cancellation by an arbitrary étale
map remain separate obligations.

Work over a complete ultrametric normed field `K : Type u`, with
independent space and original atlas-index universes `v` and `w`. Let
`f : StrongHom A.saturatedPresentation B.saturatedPresentation`,
`g : StrongHom B.saturatedPresentation C.saturatedPresentation`, and assume
`hf : f.IsQuasiIso`. No separation or compactness hypothesis is imposed.

## Actual image comparisons

`BoundedAlgEquiv.isFiniteBanach` obtains controlled lifts from the bounded
inverse of an algebra equivalence and applies the existing finite Banach
lifting criterion. This auxiliary lemma does not require completeness of
`K`.

`IsQuasiIso.fullRecognitionImage` uses the original compatible restriction
of `f` and the existing recognized-image construction. Its locus is exactly
`f.baseMap '' V.locus`, and `fullRecognitionImage_admissible` records the
actual chart-range containment. The selected definition,
`fullRecognitionImageEquiv`, applies the preceding helper's actual
`fullRecognitionPairEquiv` to this full-image pair. Its forward bounded
map is precisely `f.fullRecognitionPairs.pullback` by the following
`toBoundedAlgHom` theorem.

`image_inter_comp_preimage` records the elementary set identity carrying
`V ∩ (g ∘ f)⁻¹(U)` to `f(V) ∩ g⁻¹(U)`. It does not require injectivity.

## Finite pieces and pointwise conditions

`IsFiniteOver.of_precomp_quasiIso` starts with finiteness of the composite
over `V, U`. Each recognized target subset `Z` has a recognized inverse
image `P` in `V`. Choose its recognized image `Y` under `f`; the elementary
set identity gives the required locus for `g` over `f(V), U`.
The pair-system composition equation identifies the composite pullback
with the pullback of `g` followed by the bounded comparison from `Y` to
`P`. Composing with the inverse comparison recovers exactly the actual
pullback of `g`, so finiteness follows by composition of finite Banach
maps.

`HasAllPiecesAt.of_precomp_quasiIso` applies to a pointwise property `Q` of
bounded affinoid maps which composes along maps of finite type and holds
for bounded algebra equivalences. It transports the source neighborhood
by the homeomorphism underlying `hf`, hence preserves openness. For any
recognized piece demanded by the definition, equality of its locus with
the image `Y` identifies the actual recognized subset. The inverse spectrum
homeomorphism of the bounded comparison lifts the prescribed spectrum
point to `P`. The chart equation and ambient injectivity of `f` identify
its ambient point with the original one. The given condition on the
composite therefore holds at this lift. Composing it with the inverse
bounded equivalence proves `Q` for the actual pullback of `g` at the
prescribed point. The finite Banach maps supply the needed finite-type
hypotheses.

`IsFlatAtAllPieces.of_precomp_quasiIso` and
`IsUnramifiedAtAllPieces.of_precomp_quasiIso` specialize this argument using
the Library's pointwise composition laws. Bounded algebra equivalences are
algebraically finite étale by bijectivity, so both pointwise conditions
hold for them. `IsEtaleAtAllPieces.of_precomp_quasiIso` transports the open
étale neighborhood and applies those two specializations throughout it.

Finally, `isEtaleAllPieces_precomp_quasiIso_iff` asserts precisely that
`f.saturatedComp g` is étale over all pieces if and only if `g` is. The
forward implication uses surjectivity of `f` and pointwise descent; the
reverse implication composes `g` with the already established all-pieces
étaleness of the quasi-isomorphism `f`.

## Provenance and scope

All constructions and proofs are internal consequences of the existing
full-recognition pair systems and quasi-isomorphism image constructions,
together with the preceding `QuasiIsoFiniteEtale` and
`QuasiIsoEtaleTransport` helpers. They do not assert an external theorem
translation or use an unproved geometric premise. The unchanged
`QuasiIsoFiniteEtale` prerequisite pair is included in this submission to
make the source dependencies complete while its earlier independently
accepted candidate awaits integration.
