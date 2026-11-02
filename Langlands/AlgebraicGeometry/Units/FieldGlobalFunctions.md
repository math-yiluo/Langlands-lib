# Relative global units and the actual global-functions algebra

This is an internal consequence of the published proper-field global-functions
comparisons. Fix a field `k : Type u`, a scheme `X : Scheme.{u}` and a proper
morphism `f : X ⟶ Spec k`. Let `A = Γ(X, ⊤)` with its actual algebra structure
`GlobalFunctionsAlgebra.algebra f`, induced by `structureRingHom f`.

`finiteAlgebraPresheafIso f` is the natural isomorphism

```text
RelativeGlobalUnits.presheaf f ≅ FiniteAlgebraUnits.presheaf k A.
```

It is defined on the entire category of schemes over `Spec k`, with the
published `ULift` convention. In particular, test schemes need not be affine,
quasi-compact or noetherian. The source has value `Γ(T ×_k X, O)ˣ` and the
target has value `Γ(T ×_k Spec A, O)ˣ`. No equality `A = k`, nonzero-rank,
reducedness, separability, rational point or flatness of `X` over `A` is assumed.

The result identifies two actual presheaves. It does not assert
representability or smoothness of either, or Picard representability.

## Actual comparison and naturality

`algebraSchemeMap f` is `Spec.map (structureRingHom f)`. Under the stated
algebra structure this is definitionally `FiniteAlgebraUnits.algebraSchemeMap
k A`. The equation `toSpecΓ_over` proves that the actual canonical morphism
`X.toSpecΓ : X ⟶ Spec A` is over `Spec k`.

For every `T : Over (Spec k)`, `schemeMap f T` is the induced morphism

```text
q_T : T ×_k X ⟶ T ×_k Spec A.
```

Its projections are specified by `schemeMap_fst` and `schemeMap_snd`:
it preserves the projection to `T`, and its projection to `Spec A` is the
projection to `X` followed by `X.toSpecΓ`. The theorem
`schemeMap_naturality` compares these morphisms under every slice morphism.
Its proof uses the two projections and uniqueness of maps into a pullback.
These constructions do not require properness.

`unitsMap f T` is exactly `Units.map q_T.appTop.hom.toMonoidHom`.
The equation `unitsMap_val` gives its underlying function on sections, and
`unitsMap_restriction` proves compatibility with the published ordinary
pullback restrictions. `groupComparison` and `presheafComparison` package
this map in the `CommGrpCat` and lifted type-valued conventions respectively.
The latter runs from the finite-algebra units to the relative global units;
`presheafComparison_app` gives its component formula.

## Invertibility from the canonical direct-image sheaf comparison

The general helpers `sectionsMap` and `directImageMap` construct pullback of
functions as morphisms of base modules and structure-module direct images.
They use the actual structure-sheaf morphism `unitToPushforwardUnit` and the
canonical pushforward composition and equality isomorphisms. Their formulas
`sectionsMap_apply` and `directImageMap_top` identify the underlying maps
with ordinary `appTop`.

For compatible maps `j : X ⟶ Z` and `q : Y ⟶ W` over an affine base,
`directImageSheafMap_naturality` proves that these maps commute with the
published canonical `FieldGlobalFunctions.directImageSheafMap` morphisms.
The proof applies the composite tilde/pullback adjunction, uses naturality
of its Hom equivalence, and compares its two global-section maps by
`q ≫ v = g ≫ j` and functoriality of `appTop`.

When the affine base is `Spec k`, both original morphisms are proper, both
squares are Cartesian, and `sectionsMap` is invertible,
`isIso_directImageMap_of_sectionsMap` deduces that `directImageMap` is
invertible. It uses the published
`FieldGlobalFunctions.isIso_directImageSheafMap` for the two squares and
cancels an isomorphism in the naturality equality. This helper explicitly
requires these hypotheses; it does not assert such a conclusion over a
general ring.

For `j = X.toSpecΓ`, `isIso_sectionsMap_toSpecΓ` follows from Mathlib's
formula `Scheme.toSpecΓ_appTop`: this map on sections is the canonical
`Γ(Spec A, O) ≅ A`. The published `FieldGlobalFunctions.finite_algebra`
and the spectrum criterion for finite morphisms prove
`finite_algebraSchemeMap`. Thus `Spec A ⟶ Spec k` is proper as well.
Applying the preceding helper to the two actual fibre products proves
`isIso_directImageMap_schemeMap`. Taking sections on the top open and
using `directImageMap_top` then proves `isIso_schemeMap_appTop` for every
`T`. No flatness hypothesis over `A` enters this argument.

## Unit and presheaf isomorphisms

`unitsEquiv f T` applies `Units.mapEquiv` to the ring isomorphism obtained
from `isIso_schemeMap_appTop`. Its forward map is the original `unitsMap`,
as stated in `unitsEquiv_apply`. The naturality already proved gives
`groupComparisonIso` and `presheafComparisonIso` in the two conventions;
`presheafComparisonIso_hom` identifies the latter's forward map with
`presheafComparison`.

The final `finiteAlgebraPresheafIso` is the inverse of that canonical
comparison isomorphism, under the actual algebra structure on `A`.
The equation `finiteAlgebraPresheafIso_inv` states that its inverse is
precisely `presheafComparison`. Together with `presheafComparison_app`
and `unitsMap_val`, this specifies its inverse on every test scheme as
actual pullback along `q_T`, rather than an unspecified equivalence.
