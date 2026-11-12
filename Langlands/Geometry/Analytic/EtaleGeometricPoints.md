# Fibre functors of field-valued points on the étale site

Author: Worker 21.

For an `L`-valued point `x` of an analytic space `X` (module
`FieldValuedPoints`), this module defines the fibre functor of `x` on the
étale site `Ét(X)` (module `EtaleSite`). It also gives the point of the site
in Mathlib's sense (`GrothendieckTopology.Point`, the fibre functors of SGA 4
IV 6.3) obtained from it once the point axioms hold. It does not prove the
point axioms. Their assertion for algebraically closed complete `L` is the
separate statement module `EtaleGeometricPointStatement`.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, §4.2,
printed p.87 / PDF p.84. Stalks are defined there by inverse image along
`ℋ(x)_ét → (X, S)_ét`: "The inverse image of a sheaf F with respect to i_x is
denoted by F_x and is called the stalk of F at x. (We identify F_x with the
corresponding discrete G_ℋ(x)-set.)" The proof of Proposition 4.2.2 computes
stalks over étale neighbourhoods: "The set F_x(ℋ(x)) is the inductive limit of
the sets F(Y, T) over all ((Y, T) → (X, S)) ∈ Ét(X, S) with a fixed point
y ∈ T over x such that ℋ(x) ⥲ ℋ(y)."

The underlying set of the discrete `G_ℋ(x)`-set `F_x` is the stalk at a
geometric point over `x`. Here geometric points are `L`-valued points, and the
fibre functor is the functor of `L`-valued points over `x`. This formulation,
the lift of universes and the translation isomorphisms are derived.

## Declarations

`CategoryTheory.Functor.elementsULiftEquivalence F`: for `F : C ⥤ Type w₁`, the
categories of elements of `F` and of `F ⋙ uliftFunctor` are equivalent; the
components of both composites are identities.

In `Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite`, for
`X : LocalizedCategory.{u, v, v}` and a normed field `L` with
`[NormedAlgebra K L]`, writing `P = localizedFieldPointFunctor L`:

- `pointFibre L x : EtaleSite X ⥤ Type (max u v uL)` for `x : P.obj X`. An
  étale `U ⟶ X` goes to `{p : P.obj U.left // P.map U.hom p = x}`. A morphism
  `f` over `X` acts by `P.map f.left`; it preserves the condition by Mathlib's
  `MorphismProperty.Over.w`.
- `PointAxioms L x`: the category of elements of `pointFibre L x` is
  cofiltered, and for every covering sieve `R` of `U` in `etaleTopology X` and
  every `p` in the fibre over `U` there are `f : V ⟶ U` in `R` and `q` in the
  fibre over `V` with `f` sending `q` to `p`.
- `toPoint L x h : (etaleTopology X).Point.{max u (v + 1) uL}` for
  `h : PointAxioms L x`. Its fibre functor is
  `pointFibre L x ⋙ uliftFunctor` (`toPoint_fiber`), lifted to the universe in
  which the objects and morphisms of `Ét(X)` live.
  - Cofilteredness is transported along `elementsULiftEquivalence`.
  - The category of elements is then small in that universe, so Mathlib's
    `initiallySmall_of_essentiallySmall` gives the smallness field. No
    hypothesis is needed for it.
  - Joint surjectivity is the second point axiom.
- `pointFibreTranslate L e x` for `e : X ≅ Y`: an isomorphism
  `(translate e).functor ⋙ pointFibre L (P.map e.hom x) ≅ pointFibre L x`. The
  translate of `U` has structure map `U.hom ≫ e.hom`. Since `P.map e.hom` is
  injective, `P.map (U.hom ≫ e.hom) p = P.map e.hom x` exactly when
  `P.map U.hom p = x`.
- `pointTranslate L e x hx he`: the same isomorphism between the lifted fibre
  functors of the points `toPoint L (P.map e.hom x) he` and `toPoint L x hx`.

## Scope

Not proved here: the point axioms themselves (see
`EtaleGeometricPointStatement`), and any comparison of the stalks of these
points with Berkovich's stalks `F_x`.
