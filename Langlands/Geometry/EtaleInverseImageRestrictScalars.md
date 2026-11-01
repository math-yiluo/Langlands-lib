# Coextension and arbitrary inverse image of restricted coefficient scalars

Let `φ : R →+* S` be any homomorphism of commutative rings in `Type u`.
All schemes are `Scheme.{u}` and all module carriers remain in universe
`u`. This internal construction supplies sectionwise coextension on actual
small-etale sheaves, its adjunction with scalar restriction, and a
geometrically coherent comparison of scalar restriction with inverse
image along every scheme morphism. No affine, etale, flatness or finiteness
hypothesis is imposed.

## Actual coextension and its adjunction

`sheafCoextendScalars φ X` postcomposes the presheaf underlying a sheaf with
Mathlib's `ModuleCat.coextendScalars φ`. For a module `M`, its carrier is
the module `Hom_R(S,M)` with the existing Mathlib coextended `S`-action,
where `S` is viewed as an `R`-module using `φ`. Module morphisms act by
postcomposition. The module functor is a right adjoint and therefore
preserves the limits defining the sheaf condition. Thus `sheafCompose`
constructs a genuine sheaf functor, without a new sheafification or any
assumption on the coefficient sheaf.

`sheafRestrictCoextendScalarsAdj φ X` starts with the actual
`ModuleCat.restrictCoextendScalarsAdj`, whose module Hom correspondence
is constructed in pinned Mathlib
`Algebra/Category/ModuleCat/ChangeOfRings.lean`.
It induces the actual presheaf adjunction by `whiskerRight`, then
restricts it through the two fully faithful sheaf inclusions using
`Adjunction.restrictFullyFaithful`. The comparison isomorphisms with the
presheaf functors are identities. Consequently it is an actual adjunction
between the existing `sheafRestrictScalars` and the new sectionwise
coextension, rather than an assumed adjunction field.

The module and coefficient universes are all `u`. In particular
`Hom_R(S,M)` is still in `Type u`; no larger module universe is introduced.

## Exactness and injectives

Scalar restriction has the existing sheafified tensor-extension left
adjoint and the new coextension right adjoint. The module exports
preservation of limits and colimits of shapes with objects and morphisms
in universe `u`, and explicitly obtains preservation of finite limits and
finite colimits in arbitrary finite diagram universes.

`sheafRestrictScalarsExactFunctor φ X` packages that same scalar-restriction
functor using `ExactFunctor.of`. The following `rfl` lemma identifies its
underlying functor definitionally. In these abelian module-sheaf categories
this is ordinary exactness. It does not require flatness of `S` over `R`.

`sheafCoextendScalars_preservesInjectives` applies Mathlib's
injective-preservation theorem to the constructed
restriction/coextension adjunction: scalar restriction preserves
monomorphisms by its finite-limit preservation, so its right adjoint
coextension preserves injective objects. Coextension itself is not claimed
exact.

## Interchange with geometric inverse image

For arbitrary `f : Z ⟶ X`, `directImageCoextendScalarsIso φ f` is the
strict natural isomorphism

```text
directImage f (ModuleCat R) ⋙ sheafCoextendScalars φ X
  ≅ sheafCoextendScalars φ Z ⋙ directImage f (ModuleCat S).
```

Both sides evaluate at actual geometric base change of the test object
and postcompose with the same module coextension functor. Their objects
and maps are definitionally equal, so the isomorphism is `Iso.refl`.

`restrictScalarsInverseImageAdjunction` and
`inverseImageRestrictScalarsAdjunction` compose the actual
restriction/coextension adjunctions and geometric inverse/direct-image
adjunctions in the two orders. Transport through that strict interchange
gives the same actual right adjoint. Uniqueness of left adjoints constructs

```text
inverseImageRestrictScalarsIso φ f :
  sheafRestrictScalars φ X ⋙ inverseImage f R
    ≅ inverseImage f S ⋙ sheafRestrictScalars φ Z.
```

Its unit and counit equations are the corresponding actual
`leftAdjointUniq` equations. The comparison is derived from these
constructed universal properties. No desired scalar-restriction
comparison is an input.

## Geometric identity and composition

The private conjugation helper uses the actual counit equation and
injectivity of the Hom correspondence to compute the conjugate of the
transported left-adjoint-uniqueness comparison. The public
`conjugate_inverseImageRestrictScalarsIso` identifies it with the inverse
of the strict direct-image/coextension interchange.

`inverseImageRestrictScalarsIso_id` proves compatibility with the actual
geometric identity comparison, retaining the two functor unitors.
`inverseImageRestrictScalarsIso_comp` proves compatibility with the actual
geometric composition comparison for arbitrary composable scheme maps,
retaining all functor associators.
The proofs apply conjugation injectivity and Mathlib's proved composition,
whiskering, associator and unitor formulas. The imported geometric
conjugate formulas reduce both equations to the same direct-image maps
postcomposed with coextension; their underlying presheaf maps agree
definitionally. The private inverse-associator helper is obtained by taking
inverses of Mathlib's forward conjugate-isomorphism equation.

`inverseImageRestrictScalarsTwoStepIso` constructs the route using two
successive scalar interchanges and geometric composition.
`inverseImageRestrictScalarsTwoStepIso_eq` identifies it with the route
first composing geometric inverse images and then interchanging once.
This is equality of actual natural isomorphisms, deduced from the proved
natural-transformation composition equation.

Coefficient-ring identity and composition coherence for this restriction
comparison, agreement with the older etale-restriction model, and its
compatibility with the tensor-extension unit are further obligations.
No cohomological coefficient-change, support, smooth-action or Harris
specialization is asserted.
