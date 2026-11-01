# Identity and composition of actual derived global pullback

This module constructs successive derived global-section pullback and proves
identity and composition for the existing actual pullback along arbitrary
scheme morphisms. The coefficient identifications are the constructed
bounded-below derived inverse-image comparisons.

## Parameters and notation

Let `X`, `Z`, and `V` be schemes in `Scheme.{u}`, let `f : Z ⟶ X` and
`g : V ⟶ Z` be arbitrary morphisms, and let `R : Type u` be a commutative
ring. `ModuleSheaf X R` is the actual category of `ModuleCat.{u} R`-valued
sheaves on `X.smallEtaleTopology`. Chosen derived categories for the sheaf
categories have independent localization morphism universes `wX`, `wZ`, and
`wV`; the category of coefficient modules has its own universe `wR`.
Identity uses only `wX` and `wR`. No etaleness, flatness, finiteness,
affineness, or Noetherian hypothesis is imposed on the morphisms or schemes.

Write `L_f = EtaleInverseImage.inverseImage f R`,
`D_f = EtaleDerivedInverseImage.plusFunctor f R`, and
`RΓ_X = EtaleDerivedSectionsPlus.rightDerivedFunctor X R`. The latter is
`(sections X R).rightDerivedFunctorPlus`, the actual right-derived global
section functor on bounded-below derived sheaves. Write `P_f` for the
existing `EtaleDerivedGlobalPullback.derivedPullback f R`. It is constructed
from the actual derived inverse/direct-image adjunction unit and the
canonical comparison between derived global sections of derived direct
image and derived global sections on the source. It is not a new input.

The coefficient identifications are
`i = (EtaleDerivedInverseImage.plusFunctorId R X).hom` and
`c = (EtaleDerivedInverseImage.plusFunctorComp R f g).hom`:

```text
i : D_id ⟶ 𝟭,
c : D_f ⋙ D_g ⟶ D_(g≫f).
```

These are the previously constructed isomorphisms, obtained by actual
localization of the geometric inverse-image comparisons on complexes.

## Identity

`derivedPullback_id_eq` proves the natural-transformation identity

```text
P_id ≫ whiskerRight i RΓ_X ≫ RΓ_X.leftUnitor.hom = 𝟙 RΓ_X.
```

`derivedPullback_id` states its component formula for every
`K : DerivedCategory.Plus (ModuleSheaf X R)`:

```text
P_id.app K ≫ RΓ_X.map (i.app K) = 𝟙 (RΓ_X.obj K).
```

The proof applies `Functor.rightDerived_ext` to the actual right-derived
unit of `sections X R`. Thus equality is checked after the unit on every
bounded-below complex representative; the proof does not cancel that unit
or assume it is invertible. The representative formula for `i` expresses
it as `plusFactors_id.hom` followed by localization of
`inverseImageComplexId.hom`. `derivedPullback_normalization` then identifies
the pullback followed by its localization factor with the localized
section-complex pullback followed by the right-derived unit on the
inverse-image complex. Naturality of that unit moves the localized
coefficient identity across it. Functoriality of localization and
`sectionsComplexPullback_id` finish the argument. The component statement
is obtained by evaluation of the natural-transformation identity.

## Successive pullback and composition

`compositeDerivedPullback R f g` constructs the natural transformation

```text
RΓ_X ⟶ (D_f ⋙ D_g) ⋙ RΓ_V
```

by composing `P_f` with `whiskerLeft D_f P_g` and the inverse functor
associator. `compositeDerivedPullback_eq` proves

```text
compositeDerivedPullback R f g ≫ whiskerRight c RΓ_V = P_(g≫f).
```

`derivedPullback_comp` states the component formula for every bounded-below
derived coefficient object `K`:

```text
P_f.app K ≫ P_g.app (D_f.obj K) ≫ RΓ_V.map (c.app K)
  = P_(g≫f).app K.
```

Composition is proved by `Functor.rightDerived_ext` for `RΓ_X`, again
reducing to every complex representative. The proof postcomposes with
`RΓ_V.map (plusFactors_(g≫f).hom.app K)`, which is invertible because the
localization factor is an isomorphism. The representative formula for `c`
then gives the composite of `D_g.map plusFactors_f.hom`,
`plusFactors_g.hom`, and localization of `inverseImageComplexComp.hom`.
Naturality of `P_g` at `plusFactors_f.hom` permits consecutive uses of
`derivedPullback_normalization` for `f` and `g`; the same normalization
handles the composite. Naturality of the actual right-derived unit on `V`
moves localization of the coefficient-complex comparison across that unit.
Functoriality and `sectionsComplexPullback_comp` identify the two sides.
Evaluating the resulting transformation equality gives the component law.

## Provenance and scope

This is internal categorical infrastructure derived from the existing
actual geometric inverse image, derived adjunction, section comparison,
and complex normalization. The original pinned Mathlib ingredients are
`CategoryTheory/Functor/Derived/RightDerived.lean` (`rightDerived_ext`, the
uniqueness property of the left Kan extension) and
`Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`
(`rightDerivedFunctorPlusUnit` and its `IsRightDerivedFunctor` instance).
The proofs above describe the implemented route. No desired comparison,
identity or composition equation is assumed, and no preservation of
injectives by inverse image is used.

The result concerns ordinary derived global sections on the actual
small-etale site with bounded-below derived coefficients. Transport to the
existing sheaf-singleton and higher-cohomology pullbacks, full coherence
between iterated coefficient comparisons, shift compatibility, agreement
with the older etale-restriction model, coefficient-ring coherence,
compact supports, smooth actions, and the Harris specialization remain
separate obligations. This module does not assert any such transport or
specialization.
