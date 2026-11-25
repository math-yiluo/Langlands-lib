# The theorem of the square for geometrically Picard-zero bundles over a one-point base

This is a helper module for the proof of
`Langlands.AbelianScheme.PicardZeroArtinianLiftingStatement`. Everything in it is proved;
it assumes no unproved statement.

## Main results

Namespace `Langlands.AbelianScheme.OnePointSquare`.

- `onePointSquare`. Let `S` be a scheme with exactly one point (`[Unique S]`), `A` an
  abelian scheme over `S`, and `L` a line bundle on `A` with
  `IsGeometricallyPicardZero A L`. Then `L` satisfies the theorem of the square on
  `P := A ×_S A`. With `p1, p2 : P ⟶ A` the projections and `m := p1 * p2` the group law,
  there is an isomorphism of module sheaves

  ```
  (Scheme.Modules.pullback m.left).obj L.obj ≅
    tensorObj ((Scheme.Modules.pullback p1.left).obj L.obj)
              ((Scheme.Modules.pullback p2.left).obj L.obj)
  ```

  The conclusion is written with the same `let`-bindings as the hypothesis of
  `Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingStatement`.
- `artinianLocalSquare`. The same conclusion for `S = Spec B` with `B` a local Artinian
  ring. The spectrum of such a ring has one point
  (`PrimeSpectrum.unique_of_ringKrullDimLE_zero`), so this is `onePointSquare`.

## Mathematical source

This is the step in the proof of Proposition 6.7 of Mumford–Fogarty–Kirwan, *Geometric
Invariant Theory*, 3rd ed., Chapter 6 (printed pp. 117–118), that shows
`q = m^* − p₁^* − p₂^*` kills `Pic^τ(X/S)` "whenever `S` consists of one point".
The text derives it from the theorem of the square over a field and the rigidity
statement of its Proposition 6.1. Here rigidity is replaced by the Library's local
two-axis triviality. The geometric-fibre hypothesis is expressed by the Library's
`IsGeometricallyPicardZero`: the pullback of `L` to every geometric fibre is
translation-invariant.

## The Lean proof

Line bundles are handled through their isomorphism classes,
`LineBundle.IsoClasses tensorPreservation X`. This is a commutative group under tensor
product. `LineBundle.pullbackHom` is a group homomorphism and is functorial
(`LineBundle.pullbackHom_comp`, `LineBundle.pullbackHom_id`). `tensorPreservation` is the
published `pullbackTensorComparisonIsIso`, restated as a constant of its statement type.
The abbreviations `cls` and `pb` fix this choice.

1. **The square class.** `squareClass A L := pb m [L] / (pb p1 [L] * pb p2 [L])` on
   `A ×_S A`. `pb_squareClass` and `pb_squareClass_lift` compute its pullback along a map
   `a` into the product, or along `prod.lift x y`, as
   `pb (x * y) [L] / (pb x [L] * pb y [L])`. They use `MonObj.comp_mul` to move the
   group law through composition.
2. **The axes.** Over a one-point base, a class pulled back along the identity section
   `Z ⟶ S ⟶ A` is trivial. It factors through `S`, and every line bundle on a one-point
   scheme is trivial (`LineBundle.pullbackHom_eq_one_of_factor`); this is `pb_one_left`.
   Then `squareClass_first_axis` and `squareClass_second_axis` show that the square class
   restricts trivially to `A × {0}` and `{0} × A`, by `MonObj.comp_one` and the group laws.
3. **Algebraically closed fields.** `squareClass_eq_one_of_algClosed` says that over an
   algebraically closed field a translation-invariant bundle has trivial square class. This
   is the first identity of the published
   `algClosedFieldTranslationInvariantPullbackIdentities`.
4. **Geometric points.** `pb_squareClass_geometric`: let `W` be a scheme over `Spec K`,
   with `K` algebraically closed and `s : Spec K ⟶ S`. Every map `Ψ` from `W`, viewed over
   `S`, into `A ×_S A` pulls the square class back to `1`. `Ψ` is a pair of points of `A`.
   By `GroupScheme.baseChangePointsEquiv` (a multiplicative bijection) each point comes from
   a `W`-point of the base change `A_K`. So the pullback equals the pullback of the square
   class of `fibreLineBundle A L s` on `A_K`, which is `1` by step 3 and the hypothesis `hL`.
5. **The fibre.** `fibre_trivial`: let `N` be any line bundle with class the square class.
   For every point `s`, `N` restricts trivially to the scheme-theoretic fibre
   `(A ×_S A)_s`. The fibre is smooth, proper and geometrically connected over the residue
   field `k(s)`, by `product_geometry` and base change. After base change to an algebraic
   closure `K` of `k(s)`, the restriction of `N` is trivial by step 4. So the restriction
   to the fibre is trivial by the published `fieldBaseChangeTrivialityDescent`.
6. **Assembly.** Pick a representative `N` of the square class (`IsoClasses.ind`). By
   steps 2 and 5 (via `nonempty_iso_of_pb_eq_one`), `N` is trivial on both axes and on the
   fibre at the unique point. The published `localTwoAxisTriviality` gives an open
   `U ∋ s` over which `N` is trivial. Since `S` has one point, `U = ⊤`, and `U.ι` is an
   isomorphism (`Scheme.topIso`). So the projection `(A ×_S A) ×_S U ⟶ A ×_S A` is an
   isomorphism, and `nonempty_iso_structureSheaf_of_pullback_isIso` shows that `N` is
   trivial. Hence the square class is `1`, i.e. `pb m [L] = pb p1 [L] * pb p2 [L]`. The
   class of a tensor product is the product of classes, so `LineBundle.isoClass_eq_iff`
   gives an isomorphism of line bundles. Its image under the inclusion functor is the
   stated isomorphism of module sheaves.

## Published results used

- `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`
- `Langlands.AlgebraicGeometry.Picard.LineBundle` isomorphism-class group API
  (`LineBundleIsoClassGroup`)
- `Langlands.AbelianScheme.algClosedFieldTranslationInvariantPullbackIdentities`
- `Langlands.GroupScheme.baseChangePointsEquiv` (`Langlands.AbelianScheme.KernelBaseChange`)
- `Langlands.AlgebraicGeometry.Picard.product_geometry` and
  `Langlands.AlgebraicGeometry.Picard.localTwoAxisTriviality`
- `Langlands.AlgebraicGeometry.Picard.fieldBaseChangeTrivialityDescent` and
  `Langlands.AlgebraicGeometry.Picard.nonempty_iso_structureSheaf_of_pullback_isIso`

The axioms are `propext`, `Classical.choice` and `Quot.sound`.
