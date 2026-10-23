# Tensor products of locally free rank-one sheaves

This module constructs the tensor bifunctor on the existing category
`LineBundle X` of locally free rank-one module sheaves, for every scheme `X`.
The underlying tensor is the published sheafification of the sectionwise
module tensor.

The construction takes the explicit published premise
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`, asserting
that the canonical pullback tensor comparison is invertible for every
scheme morphism in the given universe. This module proves local rank-one
closure under that premise; it does not prove the premise.

## Local construction and proof

`pullbackTrivializationOfLE h M e` restricts a given trivialization on an
open `V` to the pullback of `M` along the inclusion of a smaller open `U`.
The construction uses the equality of the composite inclusion with the
inclusion of `U`, pullback composition, the natural identification of
restriction with pullback, the supplied trivialization, and the canonical
pullback isomorphism for the structure sheaf. It does not require tensor
comparison invertibility.

`IsLocallyFreeRankOne.tensor` proves local rank-one closure. At a point
`x`, choose trivializing neighborhoods `U` and `V` for the two sheaves
and set `W = U ∩ V`. The helper supplies trivializations of both pullbacks
to `W`. The restriction of their tensor is identified with the tensor of
these pullbacks using the canonical comparison and the explicit premise.
Tensoring the two trivializations and applying the explicit left unitor
then trivializes the result on `W`, which contains `x`.

`LineBundle.tensor preservation L M` is the actual tensor sheaf equipped
with this proved rank-one property. `LineBundle.tensorFunctor preservation X`
lifts the published sheaf tensor bifunctor to the full subcategory. Its
morphisms are exactly the tensor products of the underlying module maps,
and its functor laws are inherited from the published tensor functor.
`tensorFunctor_obj` identifies its object part with `tensor`.
`tensorForgetIso` is the identity natural isomorphism showing that forgetting
the rank-one property recovers the sheaf tensor bifunctor.

## Provenance and scope

Stacks Project, Section 17.14, Definition 17.14.1(3), defines finite local
freeness of rank one by local trivializations. The registered original is
`stacks-local-freeness-invertibility-sections-2026-10-21`, content SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`;
the retained file is `01C5.html`. The proof here is derived directly from
this definition and the published pullback and tensor constructions, using
an intersection of trivializing opens. It does not use the comparison
with tensor-invertibility from Stacks Lemma 17.25.4.

The construction requires no affineness, noetherian, quasi-compactness or
coherence hypothesis on `X`. It supplies neither tensor inverses nor a
monoidal coherence proof or Picard group law. The independent
tensor-invertibility comparison remains a separate result.
