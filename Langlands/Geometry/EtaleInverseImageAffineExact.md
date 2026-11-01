# Exactness of constructed etale inverse image over an affine base

This module proves exactness of the existing constructed inverse image
for `f : Z ⟶ X` when the base `X` is affine. It constructs the actual
finite-limit comparison and packages the same functor with its proved
finite-limit and finite-colimit preservation.

Both schemes, the commutative ring `R`, and the module carriers have
universe `u`. The only additional geometric hypothesis is `[IsAffine X]`.
The scheme `Z` and morphism `f` are arbitrary; no etaleness, affineness
of `Z`, finiteness, finite-type, Noetherian, field, coefficient-freeness
or local-constancy hypothesis is imposed.

This is internal categorical infrastructure derived from the actual
affine etale site, geometric base change, filtered module colimits and
the existing inverse-image construction. The natural Kan-extension
evaluation proof adapts Mathlib's `lanEvaluationIsoColim` in
`CategoryTheory/Functor/Flat.lean` to the large object universes, by
the same argument as `EtalePullbackAdjunction.lanEvaluationIso`.
No new external-literature claim is made.

## Finite limits of the affine source site

For affine `X`, `affineSiteTerminal X` is the affine etale object
with structural morphism `X.isoSpec.inv : Spec Γ(X) ⟶ X`.
`affineSiteTerminalIso` identifies its image under
`Scheme.AffineEtale.Spec X` with the identity object in `X.Etale`.
The latter is terminal. Reflection of terminal objects through
the fully faithful `Spec` functor proves
`affineSiteTerminalIsTerminal`.

Consequently the affine etale source has a terminal object and,
together with its existing pullbacks, all finite limits.
`affineSpec_preservesTerminal` proves that `Spec` preserves
the displayed terminal object. Its pullback-preservation instance
is Mathlib's restricted-costructured-arrow instance. These imply
`affineSpec_preservesFiniteLimits`.

The composite `affineSiteMap f`, namely affine `Spec` followed
by actual scheme base change, therefore preserves finite limits.
Since its source now has finite limits, `affineSiteMap_flat`
proves its representable flatness. The affine-base assumption
is used here; it is not inferred from essential smallness.

## Exact comma colimits

The instance `affineComma_hasColimits` obtains colimits for
each category
`CostructuredArrow (affineSiteMap f).op V` in the original
`ModuleCat.{u} R`. It uses essential smallness of these comma
categories, as in the original inverse-image construction.
This colimit-existence instance itself does not require
affineness of `X`.

When `X` is affine, representable flatness makes these opposite
comma categories filtered. `affineComma_hasExactColimits`
passes to their small models in universe `u`, transports
filteredness, applies exactness of small filtered module
colimits, and transports exactness back through the equivalence.
Thus it uses actual essentially-small filtered colimits.
It assumes neither colimits of arbitrary large shape nor
exactness of the desired inverse-image functor.

## Kan extension, sheafification and the existing functor

`affineLanEvaluationIso f R V` identifies evaluation at `V`
of the actual left-Kan-extension functor with comma
precomposition followed by the comma-colimit functor.
Its components use uniqueness of colimit cocones, comparing
the pointwise Kan-extension unit with the chosen colimit.
Naturality follows by testing on each colimit injection and
using naturality of the Kan-extension unit.

`affineLan_preservesFiniteLimits` applies this isomorphism
at each target test object. Comma precomposition preserves
limits and the preceding comma-colimit functor preserves
finite limits. Pointwise detection of limits in a functor
category proves finite-limit preservation of the whole
left-Kan-extension functor.

Source sheaf inclusion, that left Kan extension, and target
sheafification all preserve finite limits. Their actual
composite `affineInverseImage f R` therefore does so.
The inverse affine/small-etale sheaf equivalence also
preserves limits, so `inverseImage_affine_preservesFiniteLimits`
establishes the property for the already constructed
`inverseImage f R` itself.

`inverseImageFiniteLimitIso` is the canonical comparison

```text
inverseImage(f,R)(lim F) ≅ lim (F ⋙ inverseImage(f,R))
```

for any finite small indexing category and its sheaf diagram.
The comparison is obtained from the proved preservation
instance, not from an input comparison.

The actual adjunction `inverseImageAdjunction` already makes
inverse image a left adjoint, hence it preserves colimits.
`inverseImageExactFunctorOfAffine` packages this same functor
as Mathlib's `ExactFunctor`, meaning preservation of finite
limits and finite colimits. Its underlying functor is
definitionally `inverseImage f R`, as the final lemma states.
In these abelian module-sheaf categories this supplies exactness.

This module proves that result only for affine `X`.
Exactness for a nonaffine base still requires a further
local argument. Torsor-coefficient and algebraic-closure
comparisons, equivariant and smooth sheaf adapters, supports,
derived comparisons and Harris specialization also remain
separate obligations.
