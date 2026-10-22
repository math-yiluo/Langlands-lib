# Archimedean matrix coordinates and smooth functions

The namespace is `Langlands.Global`. For an actual number field `K : Type u`,
the mixed coordinate ring `NumberField.mixedEmbedding.mixedSpace K` is the
finite product of copies of the real numbers indexed by real infinite places
and copies of the complex numbers indexed by complex infinite places. A
complex coordinate uses Mathlib's existing choice of an embedding representing
the place. The rank is any natural number `n`, including zero.

## Coordinates and topology

The completion ring equivalence is Mathlib's
`InfiniteAdeleRing.ringEquiv_mixedSpace K`. The two
`infiniteAdeleCoordinates_symm_*` identities explicitly describe its inverse at
real and complex places. Forward continuity follows coordinate by coordinate
from the existing isometries of the completions with the real or complex field.
The inverse identities and inverse isometries prove inverse continuity.
These constructions work for a field even before imposing the number-field
assumption. `infiniteAdeleHomeomorph` therefore relates the original product
topology on the completions to the usual mixed-space topology.

`ArchimedeanMatrix K n` is the actual matrix ring over the mixed space, and
`ArchimedeanGL K n` is its group of units. The multiplicative homeomorphism
`archimedeanGLCoordinates` from
`Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)` applies the ring
equivalence to every entry of both a matrix and its inverse. Its inverse and
multiplicative laws are proved, and its continuity in both directions follows
from continuity of the underlying entry maps. The entrywise formula is also
proved.

For a number field the smooth model uses the finite-product supremum norm on
the mixed real/complex space. On matrices the scope `Matrix.Norms.Operator`
selects Mathlib's submultiplicative row-sum norm. This is a complete real
normed algebra. Its group of units has the usual real manifold structure as
an open subset of the matrix algebra. All these norms give the existing
product topologies. In particular, the normalized product of local norms
already called `Norm` on the infinite adele ring is not used as a Banach
algebra norm.

## Smooth functions and translation

In the namespace `ArchimedeanGL`, `smoothFunctions K n` is a complex submodule
of actual functions on the completion-based general linear group. Membership
means that transport through `archimedeanGLCoordinates.symm` is infinitely
differentiable between the real manifolds modeled on `ArchimedeanMatrix K n`
and the complex numbers considered as a real vector space. This is real
smoothness, so it allows dependence on both a complex coordinate and its
conjugate.

Closure under zero, addition and complex scalar multiplication is proved using
the smoothness of these operations. `SmoothFunctions K n` is the carrier of
this submodule; no arbitrary function-space parameter or smoothness axiom is
introduced.

`smoothRightAction K n` is a genuine complex-linear representation on that
space, with the formula

```
(R(g) f)(x) = f(x * g).
```

Right multiplication in the coordinate Lie group is smooth. Composing a
smooth function with that multiplication and using the multiplicativity of
the coordinate map proves preservation of the submodule. Pointwise linearity,
the identity law and the representation multiplication law are proved.
This action is on all smooth functions, before any compact-finiteness
condition is imposed.

The theorem `continuous` proves continuity on the original completion group
by composing the smooth transported function with the coordinate
homeomorphism. `toContinuousMap` is the corresponding linear inclusion into
the actual continuous-function space, and `toContinuousMap_injective` proves
faithfulness. This file assigns no topology to the whole smooth-function
space; in particular it makes no claim about its usual stronger topology
involving derivatives or about joint continuity of the representation.

## Original source and construction provenance

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
in *Automorphic Forms, Representations and L-Functions*, Corvallis (1979),
Part I, section 4.1, printed p.194 (one-based PDF189), use the product of
archimedean local groups and smooth functions on it in the infinite factor of
the adelic theory. Sections 1.1 and 1.3, printed pp.189–190 (PDF184–185),
give the real Lie-group and differentiability setting. Section 4.6, printed
pp.196–197 (PDF191–192), distinguishes the later automorphic module
conditions from the ambient smooth action.

Registered source: `borel-jacquet-1979-automorphic`. The original Part I volume
PDF has SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The coordinate homeomorphisms, submodule closure and translation proofs are
derived construction details implementing that setting. They reuse the
pinned Mathlib completion isometries, matrix units, normed matrix algebra and
`UnitsOfNormedAlgebra` manifold construction.

This is an analytic prerequisite for the automorphic construction. Rational
invariance, finite adelic smoothness, compact-finiteness, enveloping-algebra
finiteness, growth and cuspidality are additional conditions. This file
neither asserts automorphic existence nor identifies a space satisfying those
conditions with an irreducible representation.
