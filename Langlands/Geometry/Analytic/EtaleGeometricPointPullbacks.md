# Étale pullbacks and finite diagrams of geometric points

This internal categorical reduction proves the refinement and equalization
inputs for geometric points from standard pullback properties of the actual
localized analytic category. It does not prove those geometric properties.

## Exact premises

The ground field `K : Type u` is complete and ultrametric. The space and
atlas-index universe `v` is independent of `u`. The extension field
`L : Type uL` is complete, algebraically closed and ultrametric, with
`NormedAlgebra K L`. There is no Hausdorff or nontrivial valuation assumption.

`LocalizedEtalePullbackStatement K` asks for a pullback square for every
pair `f : A ⟶ X`, `g : B ⟶ X` in
`LocalizedCategory.{u, v, v}` when `f` is étale. If its projections are
`p : P ⟶ A` and `q : P ⟶ B`, the base-changed projection `q` must be
étale. The object `P` remains in the same localized category. This is
existence together with étale base change, not just a commuting square
or an ordinary-point lifting assertion.

`LocalizedEtaleFieldPointPullbackStatement K L` says that the actual
`localizedFieldPointFunctor L` sends every such pullback square to a
pullback square in types. It concerns full field-valued points, including
their compatible evaluations on all containing charts. It requires
preservation both of compatible point pairs and of their uniqueness.

Both declarations are unproved Prop-valued definitions.
`EtaleSite.GeometricPointFiniteDiagramInputsStatement` universally
quantifies over the fields and combines these two properties with the
published `LocalizedEtaleStabilityStatement K`: composition and right
cancellation for the actual localized étale predicate.

Only pullbacks with an étale leg are required. Existence of pullbacks
of arbitrary analytic morphisms is not assumed. In particular, no
universe enlargement or supplied Hausdorff hypothesis is hidden in the
inputs.

## Implemented refinement

`geometricPointRefinement_of_etalePullbacks` pulls back the two étale
structure maps `U ⟶ X` and `V ⟶ X`. The second projection is étale by
the input. Its composite with `V ⟶ X` is étale by composition stability,
so it defines an actual object of `EtaleSite X`. The pullback equation
makes both projections arrows of that site.

Preservation by the field-point functor makes the image square a
pullback of types. Mathlib's `Types.exists_of_isPullback` then supplies
a field point whose two images are exactly the prescribed compatible
field points. This proves `GeometricPointRefinementStatement`.

## Implemented equalization

`geometricPointEqualization_of_etalePullbacks` first forms
`P = V ×[X] V`. Its diagonal `d : V ⟶ P` has composite the identity
with the second, étale projection. Right cancellation therefore proves
that `d` is étale; there is no separate diagonal premise.

For parallel site arrows `f, g : U ⟶ V`, their structure equations
give a map `c : U ⟶ P` with components `f` and `g`. Suppose they agree
on a prescribed field point `p` of `U`. In the field-point pullback of
`P`, the points `F(d)(F(f)(p))` and `F(c)(p)` have equal first and
second components. Mathlib's `Types.ext_of_isPullback` identifies them.

Pull back the étale diagonal `d` along `c`, obtaining projections
`s : E ⟶ V` and `t : E ⟶ U`. The second projection is étale by base
change, and field-point preservation supplies a field point of `E`
mapping to the prescribed `p`. Composition with `U ⟶ X` makes `E`
an object of the site. The pullback equation, followed by each of the
two projections of `P`, gives `t ≫ f = s = t ≫ g` as equality of
localized morphisms. Extensionality for site arrows gives the required
equalizing equation in `EtaleSite X`.

## Consequence and scope

`geometricPointStatement_of_etalePullbacks_and_imageLift` combines
these two theorems with the separately assumed
`GeometricPointImageLiftStatement` and the published
`geometricPointStatement_of_geometry`. Its conclusion is exactly
`GeometricPointStatement.{u, v, uL}` under the explicit finite-diagram
and image-lifting hypotheses.

The provenance is an internal deduction from categorical pullback
universal properties, pullbacks of types, the actual morphism-property
over-category, and the published geometric-point reduction. No
literature theorem is transcribed. Proving localized étale pullback
existence and base change, preservation by the full field-point
functor, localized étale stability, and the unconditional image-lifting
input remains necessary for the unconditional geometric-point theorem.
