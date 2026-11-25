# Open immersions onto the unit locus of a global function

Module `Langlands.GroupScheme.UnitLocusOpenImmersion`. This is an internal supporting
unit with one theorem. It was written for the open cell of `SL₂ × C` in
`Langlands.GroupScheme.Reductive.SpecialLinearTensorCell`. It is a standard fact of scheme
theory: a monomorphism whose functor of points is the basic open `D(g)` is the open
immersion of `D(g)`. It has no single literature source.

## Statement (namespace `Langlands.GroupScheme.UnitLocus`)

`isOpenImmersion_of_unitLocus (f : X ⟶ Y) [Mono f] (g : Γ(Y.left, ⊤))
  (hunit : IsUnit (f.left.appTop g))
  (hex : ∀ (Z : Over S) (y : Z ⟶ Y), IsUnit (y.left.appTop g) → ∃ x : Z ⟶ X, x ≫ f = y) :
  IsOpenImmersion f.left`

Here `X Y : Over S` are schemes over a base scheme `S`, and `f` is a morphism over `S`.
The theorem has three hypotheses:

- `f` is a monomorphism in `Over S`.
- The global function `g` of `Y` pulls back to a unit on `X`.
- Every `S`-point `y` of `Y` at which `g` pulls back to a unit factors through `f`.

Under these hypotheses `f.left` is an open immersion, and its image is the basic open
subscheme `D(g)` of `Y`.

## The implemented proof

Let `U = D(g) ⊆ Y.left`, and regard `U` as an object `Z` of `Over S` through
`U.ι ≫ Y.hom`. Let `y : Z ⟶ Y` be its inclusion.

1. The function `g` pulls back to a unit on `U`. This is
   `LocalRankOneUnitCell.isUnit_appTop_of_range_subset_basicOpen`, applied with the range
   `U` of `U.ι`. So `hex` gives `x : Z ⟶ X` with `x ≫ f = y`.
2. The preimage of `D(g)` under `f.left` is `D(f.left.appTop g)`
   (`Scheme.preimage_basicOpen_top`). Since `f.left.appTop g` is a unit, this is all of
   `X`. So the range of `f.left` lies in `U`, and `IsOpenImmersion.lift` gives `l : X ⟶ Z`
   over `S` with `l ≫ y = f`.
3. `y` is a monomorphism, because `U.ι` is one. Hence `x ≫ l = 𝟙` (cancel `y`) and
   `l ≫ x = 𝟙` (cancel `f`). So `l` is an isomorphism, and so is `l.left`.
4. `f.left = l.left ≫ U.ι` is an isomorphism followed by an open immersion. So it is an
   open immersion.
