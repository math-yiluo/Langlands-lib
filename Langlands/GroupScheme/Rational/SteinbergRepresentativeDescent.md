# Arbitrary-field comparison with canonical Steinberg representatives

This internal consequence of the published actual-product transport and cyclic
torus comparison establishes independence of the quotient-isomorphism property
from the supplied reflection representatives over arbitrary fields. Its inputs
are `SteinbergFieldBaseChange`, `SteinbergCyclicGauge`,
`SteinbergCanonicalRepresentatives`, and the unconditional preservation of
semisimplicity in `SimplyConnected.SemisimpleFieldExtensionProof`. No independent
claim from the literature is made.

For every field `k : Type u`, actual affine group scheme `G`, supplied split
pinning `p`, semisimplicity of `G`, arbitrary ordering `e`, supplied normalized
simple-root family `x`, and supplied representative families `n` and `m`,
`isIso_quotient_iff_representatives_of_semisimple` proves

```text
IsIso (steinbergProduct e x m ≫ ClassFunctions.rho G)
  ↔ IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G).
```

The proof takes `K = AlgebraicClosure k` and the actual pullback group `GK`.
Its structure map is affine by pullback. The published
`isSemisimpleFieldExtension` supplies semisimplicity of `GK` unconditionally.
The algebraically closed comparison then applies to the transported original
order, normalized root maps and both representative families. For each family,
`isIso_steinbergQuotient_baseChange_iff` identifies this property with the
original property over `k`, giving the stated equivalence.

The algebraically closed comparison constructs a rational cyclic torus gauge
over `K`; the proof here descends the isomorphism property of each exact
canonical-quotient composite. It does not assert a rational conjugating torus
point or cyclic gauge over `k`. In particular the argument does not assume
surjectivity of the Coxeter torus map on `k`-points. The scheme-theoretic
isomorphism conclusion holds for finite and imperfect fields and in positive
characteristic, using the published faithfully flat quotient descent.
No simple-connectedness ascent input is used.

`isIso_quotient_iff_canonicalRepresentatives` specializes one family to
`canonicalSimpleReflectionRepresentatives x`. That existing family is
constructed from the unique opposite-root factor pairs at the root point
`x_a(1)` and satisfies `RootGeneratedSimpleReflectionRepresentatives`.
The supplied normalized root maps and the ordering remain the original ones.

`SplitSteinbergCanonicalQuotientStatement.{u}` restricts the existing
`SplitSteinbergQuotientStatement.{u}` to those canonical representatives.
It retains every arbitrary field, actual affine group scheme, supplied split
pinning, existing central-isogeny definition of simple connectedness, arbitrary
rank and ordering, and supplied normalized root family. It asserts no existence
of these supplied data and still concludes an isomorphism of the actual product
followed by the canonical quotient map in `Over (Spec k)`.

`splitSteinbergQuotient_iff_canonical` proves the two propositions equivalent
without any additional premise. One direction specializes the arbitrary
representatives; the other uses the comparison theorem and the semisimplicity
already contained in `IsSimplyConnected G`. This equivalence proves neither
proposition. The protected original statement and its imported pairs are
unchanged, and the unconditional quotient theorem remains an open obligation.
