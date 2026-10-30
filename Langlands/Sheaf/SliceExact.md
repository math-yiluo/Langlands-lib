# Exact and conservative restriction to a slice site

This module supplies categorical properties of Mathlib's existing
`GrothendieckTopology.overPullback`. It is an internal construction: the
proofs derive from the definitions and adjunctions of Mathlib's slice site,
not from a new assertion attributed to Harris or Berkovich.

## Parameters and the functor

Let `C : Type uC` have hom universe `vC`, let `J` be a Grothendieck topology
on `C`, let `A : Type uA` have hom universe `vA`, and let `V : C`.
The functor under discussion is

```text
J.overPullback A V : Sheaf J A ⥤ Sheaf (J.over V) A.
```

It restricts a sheaf along `(Over.forget V).op`: on an object `U → V`
it evaluates the original sheaf at `U`. The target is the induced topology
on `Over V`. This module does not construct a new geometric pullback or
identify this slice with some separately presented site.

## Preservation

For the preservation instances, `C` has binary products.

`overPullback_preservesLimitsOfShape` states that restriction preserves
limits of shape `K : Type uK`, with hom universe `vK`, whenever `A` has
limits of that shape. After composing with the slice site's
`sheafToPresheaf`, restriction is definitionally the original
`sheafToPresheaf` followed by precomposition with `(Over.forget V).op`.
These functors preserve the limits in question. The slice
`sheafToPresheaf` reflects limits, so preservation descends to sheaves.

`overPullback_preservesColimitsOfSize` gives preservation of colimits
indexed by categories with object universe `uK` and hom universe `vK`.
The proof uses the sheaf adjunction induced by `Over.forgetAdjStar V`:
the restriction functor is its left adjoint. No assumption that either
sheaf category has all such colimits is needed for this preservation
assertion.

`overPullback_preservesFiniteLimits` packages the first result as
`PreservesFiniteLimits` when `A` has finite limits. Finite-colimit
preservation follows from the colimit-size instance through Mathlib's
usual preservation instances. When `A` and the sheaf categories are
abelian, these facts provide exactness in the finite-limit and
finite-colimit sense.

## Detection of isomorphisms

`overPullbackReflectsIsomorphisms` takes the genuine site condition

```text
J.CoversTop (fun _ : Unit => V)
```

and proves that restriction to `V` reflects isomorphisms. It applies
Mathlib's `Sheaf.isIso_of_coversTop` to the singleton covering family.
This theorem does not require binary products. The covering condition
is an explicit argument, so the theorem is a named certificate to be
installed locally when needed; it is not an unconditional global
instance.

## Dependencies and scope

The implementation uses Mathlib's `CategoryTheory.Sites.Over`,
`Sites.Limits`, `Sites.LocalProperties`, and
`Limits.Preserves.Finite`. In particular, it reuses restriction,
the over-site topology, the induced adjunction, and the covering-family
criterion for sheaf isomorphisms. The paired
`Shimura/Coefficients/EtaleExact` module supplies the covering condition
from an actual surjective étale torsor and uses these results to
construct coefficient-homology comparisons. No derived, compact-support,
global-section, or infinite-limit comparison is proved here.
