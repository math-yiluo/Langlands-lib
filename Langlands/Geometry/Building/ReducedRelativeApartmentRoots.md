# Actual apartment roots with no doubled relative roots

Let `i : S.toGrp ⟶ G` be an included actual split torus over an arbitrary
field, and let `D : KPApartmentData i ω` be any actual apartment class.
The order function `ω` is arbitrary. Assume that no member of the full
relative root set has its double in that set.

`relativeRootDerivativeEquivOfNoDouble` identifies the actual relative
roots with all derivatives of the ordinary affine roots of `D`. Its value
on a relative root is precisely its actual reduced apartment form
`rootForm i a`. The definition uses neither a supplied affine root system
nor a supplied derivative identification.

The accompanying results prove that:

- The ordinary affine roots equal all filtration jumps, namely the
  extended affine roots.
- Their full derivative set equals the range of actual relative-root
  forms.
- The affine roots are reduced and every one is indivisible. Consequently
  every derivative has an indivisible affine lift.

The first equality uses the imported jump criterion: without a doubled
relative root, the doubled root group is trivial, so every strict
filtration jump is ordinary. The V0 nontriviality axiom of an actual
root-datum valuation gives a finite valuation value in each relative-root
direction, hence a jump and the derivative equality. Splitness makes
character evaluation faithful. If two affine roots were related by
doubling, evaluating their derivatives on full real cocharacters would
give doubled actual relative roots, contrary to the hypothesis. This
proves reducedness and indivisibility. The equivalence uses faithful
evaluation for injectivity and the derivative equality for surjectivity.

`IsRootDatumOf.two_nsmul_not_mem_relativeRoots` supplies the no-doubles
hypothesis from a reduced integral root datum on the actual character and
cocharacter lattices. Splitness makes the character lattice torsion free,
the actual-root predicate identifies the entire root image, and
Mathlib's reduced-root-datum theorem excludes twice a root.

This is internal infrastructure derived from the imported definitions and
theorems. It is valid in every characteristic, including characteristic
two; the doubling argument takes place on integral characters and real
apartment forms. It proves no splitting or apartment existence theorem,
and does not assert this conclusion for a nonreduced relative root set.
