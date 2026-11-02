# Affine representation of actual coherent-family isomorphisms

`ProperIsomRepresentabilityStatement.{u}` is a proposition without a proof
in this module. For every proper, locally finitely presented morphism
`f : X → S` of actual schemes, every scheme `T` over `S`, and every pair
of published coherent-family objects over `T`, it asserts the existence
of an actual scheme `I` over `T.left`. The scheme's lifted functor of
points must be naturally isomorphic to `FamilyGroupoid.isomPresheaf f M N`.
Its structure map is affine and locally of finite presentation.

The presheaf is tested on every scheme over `T.left` and on every
morphism between them. Its points are actual isomorphisms between
ordinary pullbacks of module sheaves, with the explicit morphism-universe
lift used by the coherent-stack atlas target. The natural isomorphism
in the statement requires full presheaf representability; representation
on geometric points alone does not suffice.

The conjunction of affineness and local finite presentation expresses
affine finite presentation: an affine morphism is quasi-compact and
separated, hence quasi-separated. No noetherian condition is imposed on
`S`, `T`, or the test schemes.

## Source derivation

This is a derived scheme specialization of Proposition 99.4.3 in the
original Stacks Project Section 99.4, Tag 08K7. The retained original
is `08K7.html` in registered source
`stacks-isom-functor-08k7-2026-11-02`, folder SHA-256
`a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`.
The definition of Isom preceding Lemma 99.4.1 retains actual module
isomorphisms, just as the imported presheaf does.

Apply the source proposition to the actual projection `T ×_S X → T`
and the two underlying module families. Properness and local finite
presentation survive base change. Properness supplies quasi-compactness
and separatedness, so the ambient projection is of finite presentation,
as required in the source. Both modules are finitely presented and flat
over `T` by the published family conditions. The published
`FamilyGroupoid.hasProperSupport` and `properSupportExists` supply proper
scheme-theoretic support from properness of `f`. Thus every hypothesis
of the source proposition is accounted for.

The source gives an algebraic space affine of finite presentation over
`T`. A space affine over a scheme is a scheme, producing the actual
representing object required here. This passage and the representability
theorem remain obligations of a future proof. The retained original has
no comments, and no project errata note was present when this pair was
prepared.

## Scope and proof boundary

The statement retains arbitrary universe `u`, all proper locally
finitely presented ambient morphisms and all actual coherent families.
It does not assume flatness of `f`; relative flatness is required only
of the two families, as in the source. No projectivity, smoothness,
geometric reducedness or connectedness is assumed.

This pair states a missing diagonal-representability prerequisite. It
does not prove its proposition, construct a coherent-stack atlas, or
supply an Artin algebraicity criterion. In the field atlas task, local
finite presentation of `f` must follow from properness over a field.
