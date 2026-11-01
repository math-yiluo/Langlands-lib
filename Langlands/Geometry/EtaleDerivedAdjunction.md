# The bounded-below geometric derived adjunction

Author: Worker 13.

This internal construction proves that the actual exact inverse image on
bounded-below derived categories is left adjoint to the actual right-derived
geometric direct image. It constructs the adjunction and its coefficient-linear
Hom correspondence, with unit and counit formulas on complex representatives.

## Inputs and provenance

The input is any morphism `f : Z ⟶ X` of schemes in universe `u` and any
commutative coefficient ring `R : Type u`. The two sheaf categories are
`ModuleSheaf X R` and `ModuleSheaf Z R`, on the actual small-etale sites, with
module carriers in universe `u`. The chosen derived categories have independent
localization morphism universes `wX` and `wZ`. There is no etale, affine,
finite-type or Noetherian hypothesis on `f`.

The left functor is precisely `EtaleDerivedInverseImage.plusFunctor f R`.
The right functor is precisely
`EtaleDerivedDirectImage.rightDerivedFunctor f R`.
The former was constructed by localizing the actual exact inverse image and
proving preservation of lower cohomological bounds. The latter is the existing
injective-resolution right-derived functor of the actual geometric direct
image. Neither functor nor their adjunction is supplied as desired input.

This file reuses `Langlands.Cohomology.complexAdjunction` from
`AdditiveAdjunction`, whose unit and counit apply the ordinary adjunction
degreewise. Its other principal dependencies are pinned Mathlib
`CategoryTheory/Adjunction/Restrict.lean`,
`CategoryTheory/Functor/Derived/Adjunction.lean`,
`CategoryTheory/Functor/Derived/PointwiseLeftDerived.lean`,
`CategoryTheory/Localization/DerivabilityStructure/Derives.lean` and
`Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`.
These actual categorical constructions justify internal provenance; no new
Harris or Berkovich source translation is claimed.

## Constructing the derived adjunction

`complexPlusAdjunction` starts with the actual
`EtaleInverseImage.inverseImageAdjunction f R` and applies it termwise to
integer-indexed complexes. Both termwise functors preserve bounded-below
complexes. Restricting this adjunction through the fully faithful complex
inclusions therefore constructs their adjunction on bounded-below complexes.
The commuting isomorphisms are the existing `mapCochainComplexPlusCompι`
isomorphisms.

Write `L` for the exact derived inverse image, `D` for ordinary geometric
direct image, `RD` for its bounded-below right-derived functor, and `Q` for the
bounded-below localization. The actual comparison

```text
α : Q_X ⋙ L ≅ inverseImage.mapCochainComplexPlus ⋙ Q_Z
```

is `EtaleDerivedInverseImage.plusFactors`. Because it is invertible, it
exhibits `L` as a left derived functor. It still does so after postcomposition
with `RD`, by the same invertible comparison and a functor associator.

The actual right-derived unit

```text
β : D.mapCochainComplexPlus ⋙ Q_X ⟶ Q_Z ⋙ RD
```

exhibits `RD` as a right derived functor. The private
`direct_postcomp_isRightDerivedFunctor` proves the extra derived property
after postcomposition with `L`. The injective-complex derivability structure
computes `RD`, and `β` is invertible on its injective complex objects. Applying
`L` preserves these isomorphisms. The derivability criterion consequently
proves the required right-derived universal property for `RD ⋙ L`.
This argument does not require inverse image to preserve injectives.

These are exactly the four derived-functor conditions in Mathlib's
`Adjunction.derived`. Applying that construction defines `adjunction f R`.
Its unit and counit arise from the derived universal properties, and Mathlib
proves their triangle identities. The exported left- and right-adjoint
instances refer to this constructed adjunction.

## Normalization and linear Hom correspondence

`unit_app_Q` proves the equation on every bounded-below complex `K` over `X`:

```text
derivedUnit(Q_X K) ≫ RD(α_K)
  = Q_X(termwiseUnit_K) ≫ β_(inverseImage K).
```

`counit_app_Q` proves the equation on every bounded-below complex `K` over `Z`:

```text
L(β_K) ≫ derivedCounit(Q_Z K)
  = α_(D K) ≫ Q_Z(termwiseCounit_K).
```

They specialize the factorization equations in the actual derived-adjunction
construction. The termwise unit and counit belong to
`complexPlusAdjunction`; their underlying complex maps come from the
degreewise ordinary geometric adjunction.

`direct_additive` obtains additivity of `RD` from the adjunction and the
additive exact left functor. `direct_linear` proves `R`-linearity by applying
the injective inverse Hom correspondence and using the coefficient-linear
left functor and the counit formula.

`homLinearEquiv K L` is the resulting actual equivalence of `R`-modules

```text
Hom(derivedInverseImage K, L) ≃ₗ[R] Hom(K, derivedDirectImage L).
```

Its forward map is composition of the derived unit with derived direct image
of the morphism. Its inverse applies derived inverse image and then composes
with the derived counit. The two final simp theorems state these formulas.

## Scope

The right-derived construction uses the actual enough-injectives structures
on these module-sheaf categories. No exactness of ordinary direct image is
asserted. This file does not yet supply derived geometric composition or
coefficient-change coherence, general cohomological pullback, compact-support
maps, smooth actions, or the Harris tower specialization.
