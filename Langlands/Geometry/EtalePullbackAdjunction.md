# Exact extension and injective-preserving étale restriction

This module constructs a left adjoint to the published restriction functor for an
étale morphism `f : Y ⟶ X` of Mathlib schemes. Its namespace is
`Langlands.Geometry.EtalePullback`. The schemes, the commutative coefficient ring
`R`, and the underlying modules use universe `u`; the small étale categories
have objects in `Type (u + 1)` and morphisms in `Type u`.

## The final family of lifts

For `U : X.Etale`, `Lift f U` is the small type of scheme morphisms
`s : U.left ⟶ Y` satisfying `s ≫ f = U.hom`. Such an `s` is étale:
`Etale.of_comp` applies since `s ≫ f` and `f` are étale. Thus `liftObject`
defines a genuine object of `Y.Etale`, and the identity on `U.left` gives
`liftArrow : U ⟶ (siteMap f).obj (liftObject f U s)`.

`liftArrows` places these objects in the costructured-arrow category of
`(siteMap f).op` over `op U`. For any object `d` of that category, `arrowLift`
is the composite of its underlying arrow with its target structure map to
`Y`, and `toLift` factors `d` through this lift. `factor_left` shows that every
such factorization has the same underlying scheme arrow; `lift_eq_of_hom`
shows that its lift index is forced. Maps between discrete lift indices have
identity underlying scheme maps (`liftArrows_map_left`). These facts prove
connectedness and nonemptiness of every structured-arrow category, hence the
instance `liftArrows_final`.

The lift type can be empty when there is no lift of `U` to `Y`; then the
costructured-arrow category is also empty. No existence of a global section of
`f`, surjectivity of `f`, or finite number of lifts is assumed.

## Left Kan extension and the adjunction

`liftComma_hasColimits` uses the final small discrete family to construct
colimits of module-valued diagrams on the large comma category.
`liftComma_hasExactColimits` transports exactness of coproducts in the module
category along this final functor. `hasPointwiseLeftKanExtension` records the
resulting pointwise existence explicitly, without requiring all large colimits
in `ModuleCat.{u} R`.

`lanEvaluationIso` identifies evaluation of left Kan extension with the
corresponding comma colimit. Its proof compares the two colimit cocones and
uses the Kan-extension unit's naturality. This is the proof of Mathlib's
`lanEvaluationIsoColim`, adapted to independent site and coefficient universes;
the Mathlib version is stated for small categories with a shared universe.
Exactness of the comma colimits and pointwise computation of presheaf limits
then give `lan_preservesFiniteLimits`.

`extension f R` is the composite of the inclusion of sheaves on `Y`, left Kan
extension along `(siteMap f).op`, and sheafification on `X`:

```text
Sheaf(Y_et, R) → Presheaf(Y_et, R) → Presheaf(X_et, R) → Sheaf(X_et, R).
```

`extensionAdjunction` is the actual adjunction
`extension f R ⊣ restriction f (ModuleCat.{u} R)`, obtained from Mathlib's
continuous-site adjunction. Each factor of `extension` preserves finite
limits, and the adjunction gives preservation of colimits. These are the
instances `extension_preservesFiniteLimits` and `extension_preservesColimits`.
In particular the left adjoint is exact on module sheaves.

## Restriction and injectives

The adjunction gives `restriction_preservesLimits`.
Since its left adjoint preserves monomorphisms,
`restriction_preservesInjectiveObjects` follows from Mathlib's adjunction
criterion. This is the injective-preservation input needed for a subsequent
construction of pullback maps on derived global sections.

This module does not construct a right adjoint to restriction, prove that
restriction preserves colimits, or define maps on cohomology. General scheme
morphisms, analytic étale sites, compact supports and the Harris Shimura/Hecke
specialization remain outside this unit.

## Provenance

This is internal infrastructure built from the published `EtalePullback` and
Mathlib's actual small étale sites, `Etale.of_comp`, final functors, pointwise
Kan extensions, exact coproducts of modules, sheafification and adjunctions.
No literature theorem about Harris cohomology is asserted. The discrete-family
argument follows the pattern of the published
`Langlands.Sheaf.Equivariant.Induction` but proves its own lift/factorization
facts on schemes. The `lanEvaluationIso` proof is adapted from
`Mathlib/CategoryTheory/Functor/Flat.lean` at the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, under its Apache 2.0 license.
