# Scalar Laurent reduction of a standard rational cover

Author: Worker 125.

The module
`Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalLaurentReduction`
constructs the actual quotient comparisons used when a standard rational cover
is split by a scalar Laurent function. Its namespace is
`Langlands.Analytic.StrictTestDomain.StandardRationalLaurentReduction`.
It works at every universe `u` over a complete ultrametric normed field
`K : Type u` and a presented strict affinoid algebra `P` over `K`.

Let `f : Fin (n + 1) → P`, and write `hf` for the condition that its entries
have no common zero on `BanachSpectrum P`. The additional inputs for the upper
reduction are

```text
hc : c ≠ 0
hthreshold : ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f j).
```

The threshold is supplied as a hypothesis. The module does not construct it
from `hf`.

## Actual data and the shortened tuple

The definitions are

```text
scalarFunction f c = algebraMap K P c⁻¹ * f (Fin.last n)
upper f c = laurentUpper (scalarFunction f c)
lower f c = laurentLower (scalarFunction f c)
overlap f c = (upper f c).inter (lower f c)
shortened f c j = (upper f c).baseMap (f j.castSucc).
```

Here `j : Fin n`, so `shortened` retains exactly the first `n` entries and
omits only `Fin.last n`. Write `U`, `L` and `O` for these upper, lower and
overlap rational data. All associated algebras and base maps are the published
`RationalData.algebra` and `RationalData.baseMap`. In particular, these are the
actual closed-ideal Tate quotients. The upper input has denominator one and
numerator `scalarFunction f c`; the lower input has denominator
`scalarFunction f c` and numerator one. Their overlap uses the existing
intersection presentation and its two restriction maps.

`scalarFunction_apply` proves
`x (scalarFunction f c) = ‖c‖⁻¹ * x (f (Fin.last n))` using multiplicativity
and the scalar evaluation theorem `BanachSpectrum.algebraMap_apply`.
Consequently `mem_upper_iff`, under `hc`, identifies the upper locus with
`x (f (Fin.last n)) ≤ ‖c‖`. Its proof multiplies the Laurent upper inequality
by the positive number `‖c‖`. Pulling a point of `U.algebra` back along the
actual base map gives `upper_last_le`, the same bound for the mapped last
entry.

For `shortened_threshold`, apply `hthreshold` to that pulled-back point.
The resulting index cannot be the last index, by `upper_last_le`.
`Fin.eq_castSucc_of_ne_last` therefore supplies an index of `Fin n` whose
shortened entry still has value strictly above `‖c‖`.
`shortened_no_common_zero` follows because norms are nonnegative. This
argument includes `n = 0`: it rules out every point of `U.algebra` when the
retained index type is empty, without introducing a positive-length assumption.

`last_pullback_locus_empty` says that

```text
((standardRational f hf (Fin.last n)).pullback U.baseMap).locus = ∅.
```

Membership would put every retained value below the mapped last value. The
strict threshold witness and `upper_last_le` contradict that inequality.
`last_pullback_subsingleton` then applies the published
`subsingleton_algebra_of_locus_empty` to this exact pullback datum. It uses
the existing spectrum nonemptiness theorem for nonzero presented strict
affinoids, rather than a criterion asserting that functions are detected by
their pointwise values.

## Bounded comparisons and restriction squares

`shortStandard f c hc hthreshold j` is the standard rational datum of the
shortened tuple over `U.algebra`. The abbreviation
`upperStandard f c hf i` is the pullback of `standardRational f hf i`
along `U.baseMap`, for every original index `i`.

`shortStandard_locus` proves that
`(upperStandard f c hf j.castSucc).locus` equals
`(shortStandard f c hc hthreshold j).locus`. One implication simply retains
the first `n` inequalities. For the other, all retained inequalities are
already available; the omitted last inequality follows by putting the last
value below `‖c‖`, then below the threshold witness, and finally below the
chosen denominator value. Thus no coordinate presentation is silently
identified or changed.

The module gives reusable local helpers for rational data `d` and `e` over
one presented base. For `h : d.locus = e.locus`, `locusMap h` is the bounded
map `d.algebra → e.algebra` obtained from
`(⟨h.symm.subset⟩ : Inclusion e d).restriction`. Its coefficient square is
`locusMap_comp_baseMap`. The inverse composition identity
`locusMap_symm_comp` follows by applying the rational quotient's `hom_ext`
and reducing both maps to their common base map. `locusEquiv` packages these
two maps into a `BoundedAlgEquiv`. The same extensionality argument proves
`locusMap_restriction`, the naturality square for any two inclusions between
equal-locus pairs. `inter_locus_eq` supplies the corresponding equality for
the existing intersection data.

Specializing these helpers gives the actual maps

```text
toShort j   : (upperStandard ... j.castSucc).algebra → (shortStandard ... j).algebra
fromShort j : (shortStandard ... j).algebra → (upperStandard ... j.castSucc).algebra
shortEquiv j : BoundedAlgEquiv K
  (upperStandard ... j.castSucc).algebra (shortStandard ... j).algebra.
```

The arrows displayed for `toShort` and `fromShort` are `BoundedAlgHom K`.
The suffixes `_comp_baseMap`, `fromShort_comp_toShort` and
`toShort_comp_fromShort` record the two coefficient squares and both
inverse identities.

For each pair of retained indices, `overlapToShort` and `overlapFromShort`
are bounded inverse maps between the intersection of the two pulled-back
standard data and the intersection of the two shortened standard data.
The theorems `overlapToShort_comp_left`,
`overlapToShort_comp_right`, `overlapFromShort_comp_left` and
`overlapFromShort_comp_right` prove the four restriction squares.
`overlapFromShort_comp_overlapToShort` and
`overlapToShort_comp_overlapFromShort` give the inverse identities on these
actual overlap quotients.

`upperComparison` also starts directly at an original standard quotient:
it composes the published base-change `comparison U.baseMap` with
`toShort`. Its base-map square is `upperComparison_comp_baseMap`.
`upperOverlapComparison` similarly composes the published
`intersectionComparison` with `overlapToShort`. The existing comparison
handles the difference between the chosen pullback of an intersection and
the chosen intersection of pullbacks. The theorems
`upperOverlapComparison_comp_left` and
`upperOverlapComparison_comp_right` give its two restriction squares.
Applying this overlap map to a compatibility equality proves
`upperComparison_compatible`: a compatible original scalar family restricts
to a compatible shortened family.

For an arbitrary family `s` in the whole pulled-back upper cover,
`upper_lift_iff` identifies the condition on a fixed `a : U.algebra` that
its image in every original pulled-back quotient is `s i` with the condition
that its image in each shortened quotient is `toShort j (s j.castSucc)`.
The forward implication uses the coefficient squares. The reverse implication
uses injectivity of `shortEquiv` at retained indices and subsingletonness at
the omitted last index. Rewriting this pointwise equivalence proves
`existsUnique_upper_lift_iff`. This transports unique-lift assertions; it
does not supply existence on either side.

## Units and mapped standard covers

`lower_last_isUnit` proves `IsUnit (L.baseMap (f (Fin.last n)))`.
The published rational localization theorem makes the lower denominator
`L.baseMap (scalarFunction f c)` a unit. After expanding this denominator as
a product, `isUnit_of_mul_isUnit_right` makes its last-entry factor a unit.
`overlap_last_isUnit` maps that fact along the actual restriction
`interRight U L` and uses its base-map square. These two unit results need
neither `hc` nor `hthreshold`; degenerate quotients remain allowed.
`mapped_entry_isUnit` records preservation of any previously unit entry under
every rational base map, in particular under those of `L` and `O`.

Finally, `lower_standard_pullback` and `overlap_standard_pullback` identify
each original standard datum pulled back along the respective base map
with the standard datum of the entire mapped tuple, at the same index.
These are equalities of rational data, proved by reflexivity using the
published pullback definitions and `tuple_no_common_zero_pullback`.
Consequently their quotient and restriction interfaces remain those of the
existing rational constructions.

## Source translation and scope

The source motivation is Piotr Achinger, *Introduction to non-Archimedean
Geometry*, November 22, 2020, registered as
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
Definition 7.2.1, printed/PDF p.65, gives the standard rational cover.
The main induction in the proof of Theorem 7.0.1, printed/PDF p.67,
chooses a small nonzero scalar `t^N`, divides the last entry by that scalar,
removes the last upper piece, and observes that the last entry becomes a
unit on the lower piece and overlap. Here the supplied scalar `c` corresponds
to `t^N`; it is distinct from the positive real infimum denoted `c` in the
source. The printed shortened list on p.67 begins at `f₁` despite the
original list beginning at `f₀`. The implementation retains `f₀` through
`fₙ₋₁`, dropping exactly `fₙ`, as required by the threshold argument.
No source-specific errata file was found in the checked public errata
locations on 2026-11-01.

This is a derived construction and comparison unit. The explicit bounded
maps, inverse laws, overlap squares and lift equivalences are implemented
using the Library's rational representability, base change and intersection
interfaces; they are not asserted as separately stated results of the source.
The source uses rigid spectra and a unit-ideal tuple. Here the tuple
hypothesis is absence of a common zero on the Banach spectrum, as in the
imported `StandardRationalCover`; the existing rational input interface
supplies unit-ideal generation for the actual quotients. The source omits the
redundant denominator coordinate of each standard quotient. This module
keeps that coordinate according to the Library's rational quotient convention
and compares actual chosen presentations by representability.

Achinger's standing convention on printed/PDF p.6 requires a nontrivial
scalar valuation. This module permits trivial valuation conditional on the
displayed scalar threshold. Its proofs only use normalized scalar
evaluation, real order, pullback of spectrum points and the published
rational quotient properties. There is no assumption that the last entry is
a nonunit, that a locus is nonempty, or that `P` is nonzero or reduced.
Scalar maps into a zero quotient are retained; the unit proofs also apply
there.

All rational constructors here have unit radii; the scalar normalization
expresses the bound `‖c‖` on the last entry through that unit-radius
constructor. The section and lift comparisons concern scalar coefficient
algebras, the degree-zero portion needed by the parent reduction. They do
not establish standard-cover descent, a scalar gluing theorem, the existence
of the threshold, induction on tuple length or on the number of nonunits,
higher Cech exactness, arbitrary-module descent, or arbitrary-radius
comparisons. The exactness argument of Lemma 7.3.3, printed/PDF pp.66–67,
and the remaining induction are outside this unit.
