# Actual CM images of presented local components

This internal construction combines `PresentedLocalComponent` and
`FiniteLocalCMTransport`. The number field `F : Type uF` is CM, the rank
`n` is any natural number, and coefficients are complex. Local model
carriers `V v : Type uV` have an independent universe and their specified
complex module structures. No topology on these model carriers is needed.

The supplied input is a genuine finite tensor presentation
`P : FiniteTensorPresentation F n ρ E e he S` and ordinary nonzeroness
`hS : S ≠ ⊥`. Its reference vectors are nonzero and integral-fixed outside
the finite exceptional set `E`. The existing `P.localComponent hS v`
uses a chosen nonzero complementary tensor vector, whose existence has
already been proved from the presentation and nonzeroness.

Write `c` for `CMConjugation.fieldConj F` and `cv` for
`AdelicFunctoriality.finitePlaceEquiv c v`. This place map is ideal
pullback. The actual completion-group map
`AdelicGLTransport.localEquiv n c v` goes from the local general linear
group at `cv` to the group at `v`.

`complexConjLocalComponent hS v` is exactly
`(P.localComponent hS v).complexConj`, an actual embedded local form
subspace at `cv`. It pulls back the represented adelic functions by
`CMConjugation.adelicConj F n` and leaves complex values fixed. Its topology
is inherited from forms. Nonzeroness follows from the existing component's
nonzeroness and reflection of zero by the actual CM image.
`complexConjLocalComponent_le` places it inside
`S.complexConj.toLocal F n cv`. The proof uses monotonicity of the actual
image and equality of finite-image local restriction with local CM image.
This whole local restriction retains the entire finite carrier.

`complexConjLocalComponentEquiv` is a genuine representation equivalence
from `(ρ v).comp (AdelicGLTransport.localEquiv n c v).toMonoidHom`
onto the action on this embedded image. Its underlying linear equivalence
first applies `P.localComponentEquiv hS v`, then the continuous linear
CM image equivalence on the original component. The intertwining law
composes the original slice's equivariance with proved CM local covariance.
Its application formula states this composition exactly, and its evaluation
formula is

```text
evaluate (CM image vector of x) a
  = evaluate (original component vector of x) (CMConjugation.adelicConj F n a).
```

No continuity for the equivalence from the abstract model carrier is
asserted. `complexConjLocalFactor_isSmooth` proves smoothness of the
pulled-back factor using its injective intertwiner into actual smooth forms.
`complexConjLocalComponentClass` represents its smooth isomorphism class
in universe `uF`, independently of `uV`.
`complexConjLocalComponentClass_eq` compares presentations with the same
tensor data, possibly into different nonzero finite realizations. Both
transported components are equivalent to the same pulled-back local model,
so their smooth classes are equal.

`complexConjLocalComponent_hasCentralCharacter` inherits the specified
global character condition from `S` and transports it to `χ.complexConj`.
This character is precomposition with arithmetic CM conjugation on idele
classes, with fixed complex values. `complexConjLocalComponent_isCuspidal`
similarly inherits and transports the actual normalized constant-term
condition. It retains the explicit instance
`[CompactSpace (AdeleQuotient F)]`. Both conditions concern the embedded
global functions, with no descent to arbitrary abstract local classes.

For `v ∉ E`, `complexConjLocalComponent_exists_integral_fixed` gives a
nonzero vector in the image component fixed by the actual local integral
subgroup at `cv`. It takes the CM image of the original component's
nonzero integral-fixed vector. Injectivity proves nonzeroness. The actual
completion-group equivalence preserves integrality of matrices and their
inverses, so covariance proves invariance. No scalar character hypothesis
or enlargement of the exceptional set is required; the conclusion is
indexed by source places `v ∉ E` and lies at their pulled-back places `cv`.

Provenance is internal composition of existing actual slice and CM image
constructions. The component, covariance, containment, smoothness,
same-model class comparison and fixed-vector properties are proved rather
than supplied as preservation assumptions. This module makes no new
original-literature identification. It does not construct a global CM
tensor presentation, identify one slice with a whole local restriction,
prove factorization or occurrence for arbitrary classes, or assert Satake,
spectral, weak-association or conjugate-self-duality results.
