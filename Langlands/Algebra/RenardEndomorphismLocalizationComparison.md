# The explicit localized functor and chosen-arrow comparison

Worker 1581. This is the target and canonical-arrow unit of the chosen
endomorphism-localization construction. All declarations are in
`Langlands.Renard.EndomorphismLocalization.ChosenComparison`.
It imports the actual source construction in
[`RenardEndomorphismLocalizationSource`](RenardEndomorphismLocalizationSource.md).

The parameters are a commutative unital ring `R : Type u` and independent
carrier and enlargement universes `v` and `w`; put κ = max u v w. An input A
is an arbitrary object of `PolynomialEndomorphism.EndomorphismCat.{u,v} R`.
Write a for `endomorphism R A`, M_A for `(toPolynomial R).obj A`, and S for
`powersX R`. The actual carrier of M_A is `Module.AEval' a`. There is no
assumption on a, on an intertwiner, or on the dimension or cardinality of
the module. The zero ring, zero module, and zero or nilpotent operators are
all allowed.

The imported F, U, P, beta, theta and lambda are respectively `chosenFunctor`,
`raisedFunctor`, `polynomialRaisedFunctor`, `sourceComparison`,
`polynomialArrow` and `chosenArrow`. In particular F remains the exact
published `toPolynomial R`, `ModuleLocalization.chosenLocalFunctor S`,
`localFromPolynomial R` composite. J is the published
`invertibleEndomorphismInclusion R`. This file constructs E, alpha and iota
and identifies the two actual canonical arrows.

`liftedLocalizedEquiv` conjugates the published native R-linear
`localizedEquiv a` through `ULift.moduleEquiv`. Its forward and inverse
formulas are

```text
ULift.up z ↦ ULift.up (localizedEnd a z),
ULift.up z ↦ ULift.up (localizedInv a z).
```

The underlying `localizedEquiv` was constructed from the published identities
`localizedEnd_localizedInv` and `localizedInv_localizedEnd`. The two lifted
inverse identities are recorded as `liftedLocalizedEquiv_apply_symm` and
`liftedLocalizedEquiv_symm_apply`. `explicitObject` bundles
`ModuleCat.of R (ULift.{w} (Localized a))` and the forward operator in the
actual invertible full subcategory. It uses the native R-module action of the
published explicit quotient. Its invertibility proof applies
`Module.End.isUnit_iff` to this actual linear equivalence.

For every original intertwiner f from A to B, `localizedPolynomialMap R f`
is exactly

```text
IsLocalizedModule.map S
  (LocalizedModule.mkLinearMap S M_A)
  (LocalizedModule.mkLinearMap S M_B)
  (toPolynomialMap R f).hom.
```

Thus the construction uses the actual localized polynomial-linear map.
`localizedPolynomialMap_mk` specializes Mathlib's `map_LocalizedModules`
formula at every denominator s in S. `explicitLinearMap` restricts this map
to R and conjugates through the two native `ULift.moduleEquiv` maps.
`explicitMap` bundles it as a morphism of actual invertible pairs;
`explicitMap_hom` exposes its underlying linear map. Its intertwining
proof is precisely polynomial linearity for X. `explicitMap_up_mk` gives
the formula on every lifted representative. The identity and composition
proofs descend by `LocalizedModule.induction_on` to those representatives
and use the identity and composite underlying polynomial functions.

`explicitFunctor` is E, with object and morphism definitions just described.
For every x in A and every s in S, `explicitFunctor_map_up_mk` states

```text
E.map f (ULift.up (LocalizedModule.mk (Module.AEval'.of a x) s)) =
  ULift.up (LocalizedModule.mk
    (Module.AEval'.of (endomorphism R B) (f.f x)) s).
```

`explicitFunctor_map_up_frac` specializes this to all natural n:
`ULift.up (frac a x n)` maps to
`ULift.up (frac (endomorphism R B) (f.f x) n)`. No condition such as
injectivity of the original operator or invertibility of f enters these
laws.

`targetLinearEquiv R A` compares F's restricted coefficient action with E's
native R-action on the same localized quotient carrier. Its forward and
inverse functions are both `ULift.up z ↦ ULift.up z`. Its scalar proof first
writes the restricted action as `(C r : R[X]) • z` and then applies the
published `smul_eq_C_smul a r z` in the reverse direction. The proof
explicitly annotates z with the native `Localized a` carrier to select its
native R-module structure. It does not assume the native and restricted
R-actions are definitionally equal. `targetLinearEquiv_intertwines`
identifies the recovered X-action with `localizedEnd a`.

`targetIso` is the resulting isomorphism in the actual invertible full
subcategory. `targetComparison` is alpha, bundled by `NatIso.ofComponents`;
its naturality holds for every original intertwiner by equality of the
underlying localized functions. The hom and inverse component formulas are
`targetComparison_hom_up` and `targetComparison_inv_up`.
`targetComparison_hom_inv` and `targetComparison_inv_hom` give both inverse
identities in the full subcategory. `targetComparison_naturality` records
the naturality equation there explicitly.

`explicitArrowComponent` is the native R-linear map `iota a`, conjugated
through U's and E's actual lifts. It sends `ULift.up x` to
`ULift.up (iota a x)`, and its pair-morphism equation is the published
`iota_intertwines`. `explicitArrow` bundles these components into the natural
transformation iota from U to E followed by J. Naturality is proved by the
denominator formula at s = 1 for every original intertwiner.

`arrow_comparison` states the exact equation

```text
beta_A.hom ≫ theta_A ≫ J.map (alpha.hom.app A) = iota.app A.
```

Its proof uses extensionality of actual pair morphisms and the displayed
component functions; both sides send a lifted x to the same localized
class. `chosenArrow_comparison` rewrites this with lambda as the chosen
arrow, so that `lambda.app A ≫ J.map (alpha.hom.app A) = iota.app A`.
`canonicalArrowComparison` gives the same comparison as an equality of
natural transformations, using the actual right whiskering of alpha by J.

`chosenStructuredArrow R A` and `explicitStructuredArrow R A` are the
actual `StructuredArrow (U.obj A) J` objects formed from lambda and iota.
`structuredArrowComparison` uses `StructuredArrow.isoMk` with target
isomorphism `alpha.app A` and the exact `chosenArrow_comparison` equation.
The forward and inverse target morphisms are identified by
`structuredArrowComparison_hom_right` and
`structuredArrowComparison_inv_right`. Moreover
`structuredArrowComparison_proj` identifies the image under the actual
projection functor with `alpha.app A` as an isomorphism, including both
morphisms. `fieldStructuredArrowComparison` is the exact specialization to
every field k and every input pair over k, with the same independent
universes and arbitrary vector-space dimension.

The motivating source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.III.1, printed251–252 / one-based PDF257–258, introduces the right universal
problem and obtains the endomorphism-localization example 5 from the module
localization example 4 through the polynomial-module equivalence. Worker 1581
reread both pages for this task. The commutative-ring generalization and the
specified lift, functor and arrow comparisons are derived internal
constructions; these formulas are not extra literal statements of the book.
Locality here means invertibility of the actual endomorphism. The stronger
printed scalar-inverse parenthesis in example 4 is not used; see the published
[discrepancy note](../../notes/renard/appendix-a-corrections.md).

This pair constructs the functors, canonical natural map, target natural
isomorphism and structured-arrow comparison, with their intrinsic laws.
Initiality, universal factorization and uniqueness in the structured-arrow
category, an adjunction, chosen-model exactness, and the source B-module
comparison remain separate statement and proof obligations. The existing
scalar-linear universal theorem is an input for those successors, and is
not invoked to assert any such categorical universal property here.
