# Smoothness of morphisms of affine schemes by infinitesimal lifting

This module proves a form of the infinitesimal lifting criterion for smoothness
of a morphism between affine schemes over an affine base `Spec R`, where `R` is
any commutative ring. The test objects are spectra of `R`-algebras, written as
`(algSpec R).obj (op C)` for `C : CommAlgCat R`. Square-zero means `I ^ 2 = ⊥`.

## Algebra form

`AffineLifting.formallySmooth_of_lifting` takes a morphism `φ : B ⟶ A` of
`R`-algebras. Its hypothesis is as follows. Let `C` be an `R`-algebra and `I` an
ideal of `C` with `I ^ 2 = ⊥`. Let `y : B ⟶ C` and `x₀ : A ⟶ C ⧸ I` be maps that
agree on `B`, that is, `φ ≫ x₀ = y ≫ (C → C ⧸ I)`. Then some `x : A ⟶ C` has
`φ ≫ x = y` and reduces to `x₀`. The conclusion is
`RingHom.FormallySmooth φ.hom.toRingHom`, so `A` is formally smooth over `B`
through `φ`.

The proof uses Mathlib's `Algebra.FormallySmooth.of_comp_surjective`, which
reduces formal smoothness of `A` over `B` to lifting `B`-algebra maps
`A → E ⧸ I` for every `B`-algebra `E` and square-zero ideal `I`. Such an `E` is
also an `R`-algebra through `R → B → E`, and the given `B`-algebra map gives an
instance of the hypothesis with `y` the structure map `B → E`. The lift it
returns is an `R`-algebra map that agrees with the structure map on `B`. Hence it
is a `B`-algebra map lifting the given one.

## Scheme form

`AffineLifting.smooth_of_lifting` takes a morphism `f : X ⟶ Y` in
`Over (Spec R)` whose source and target have affine underlying schemes, with
`LocallyOfFinitePresentation f.left`. Its hypothesis is the same lifting property
on test spectra. Let `C` be an `R`-algebra and `I` an ideal with `I ^ 2 = ⊥`. Let
`y : Spec C ⟶ Y` and `x₀ : Spec (C ⧸ I) ⟶ X` be morphisms over `Spec R` with
`x₀ ≫ f` equal to the composite of `Spec (C ⧸ I) ⟶ Spec C` with `y`. Then some
`x : Spec C ⟶ X` has `x ≫ f = y` and restricts to `x₀`. The conclusion is
`Smooth f.left`.

The proof proceeds as follows.

1. Mathlib's `essImage_algSpec` places affine objects of `Over (Spec R)` in the
   essential image of `algSpec R`. This gives `R`-algebras `A`, `B` and
   isomorphisms `eX : Spec A ≅ X`, `eY : Spec B ≅ Y`. Full faithfulness of
   `algSpec R` gives `φ : B ⟶ A` with `Spec φ = eX.hom ≫ f ≫ eY.inv`. Here
   `Spec φ` denotes `(algSpec R).map φ.op`, a morphism in `Over (Spec R)`.
2. Transport along `eX` and `eY` turns a lifting problem for `φ` into one for
   `f`. The scheme hypothesis solves it, and full faithfulness turns the solution
   back into an algebra map. By the algebra form, `φ` is formally smooth.
3. The underlying morphism `(Spec φ).left` equals
   `eX.hom.left ≫ f.left ≫ eY.inv.left`, so it is locally of finite
   presentation.
   `HasRingHomProperty.Spec_iff` makes `φ` a finitely presented ring map.
4. `RingHom.smooth_def` combines the two properties into smoothness of `φ`.
   `HasRingHomProperty.Spec_iff` gives `Smooth (Spec φ).left`. Since
   `f.left = eX.inv.left ≫ (Spec φ).left ≫ eY.hom.left` and isomorphisms are
   smooth, `f.left` is smooth.

## Provenance

This is an internal helper for the proof of
`Langlands.GroupScheme.Diagonalizable.CocycleModelActionRelationSmoothStatement`.
It restates Mathlib's definitions in a usable form: formal smoothness by
square-zero lifting, and smoothness of a ring map as formal smoothness plus
finite presentation. It cites no further literature. Only square-zero lifts are
required, and the test objects are affine.
