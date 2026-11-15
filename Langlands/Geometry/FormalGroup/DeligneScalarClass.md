# Triviality of the normalized scalar action on actual Deligne classes

Every field scalar acts trivially on the existing genuine admissible
isomorphism classes under the valuation-normalized general linear action.
The proof uses the published explicit integral-unit and uniformizer-period
isomorphisms, the DVR coefficient-order correction, and the action laws.
It assumes no scalar-triviality witness.

This is derived infrastructure for V. G. Drinfel'd, *Coverings of p-adic
symmetric regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4).
The source defines the cyclically graded four data, the relation
`Pi^d = pi`, and the determinant normalization, and its representability
theorem describes a `PGL(d,F)` action on Deligne's factor. The registered
source is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The scalar kernel and its computation here are derived constructions for
that projective descent, rather than separately stated source theorems.

## Actual determinant and preliminary classes

All carriers have common universe `u`. For any field `F`, any natural
number `d`, and `a : Fˣ`, `det_scalarReframeHom` identifies the unit-valued
determinant of the actual scalar linear automorphism on `Fin d → F`
with `a^d`. The proof identifies its linear map with scalar multiplication
of the identity and uses the determinant scaling formula and the actual
finite dimension `d`. This lemma also applies when `d = 0`.

For preliminary four data assume `NeZero d`, a commutative coefficient
ring `O`, an `O`-algebra field `F`, a scheme `S`, and a structural ring map
`phi : O → Γ(S, top)`. No valuation or nilpotence is used in the two
preliminary-class lemmas:

- `SheafPreDatum.IsoClass.reframe_integralUnit` proves that reframing by
  the field image of an integral unit preserves the genuine class.
- `SheafPreDatum.IsoClass.shiftReframe_uniformizerInverse` assumes only
  nonzero image of `pi` and proves that the scalar `pi⁻¹` reframe together
  with shift `d` preserves the genuine class.

Both proofs use quotient induction and `Quotient.sound` applied to the
explicit frame- and u-preserving isomorphisms in the imported modules.
The equivalence relation is the existing relation of nonempty genuine
isomorphisms, with its actual lattice, tangent, frame, and u equations.

## The normalized operation on admissible classes

For the remaining constructions assume that `O` is a domain and a
DVR, that `F` is its fraction field, and that `hpi : Irreducible pi`.
The scheme and structural map are arbitrary; a nilpotence premise is
not needed for this algebraic action on the existing admissibility
predicate. The uniformizer has nonzero field image by the fraction-field
injection. The action comes from `DeligneValuedReframe`: for a linear
automorphism `g`, the integer shift is
`-coefficientOrder(det g)` and the frame is precomposed by `g`.

`coefficientOrder_det_scalarReframeHom` proves that the determinant
order for a scalar `a` is `d * coefficientOrder(a)`. It follows from the
unit-valued determinant identity and the coefficient-order homomorphism.
Consequently an integral unit has correcting shift zero, and the inverse
uniformizer has correcting shift `d`.

`SheafDatum.IsoClass.normalizedReframe_integralUnit` and
`normalizedReframe_uniformizerInverse` identify those normalized
operations with the two preceding preliminary-class equalities.
Injectivity of `toPreliminary`, the existing map forgetting the
admissibility proof, lifts the equalities to admissible classes.
No new admissibility-preservation hypothesis is introduced.

## The scalar kernel and general scalar triviality

The selected definition `SheafDatum.IsoClass.normalizedScalarKernel`
is the actual subgroup of `Fˣ` consisting of the scalars fixing every
admissible class. Its identity, product and inverse properties are
proved from the existing normalized right-action laws and the scalar
linear-group homomorphism. The definition's carrier is the universal
fixed-point condition itself, not an input asserting that it holds.

`normalizedReframe_scalar` proves that every field unit belongs to this
subgroup. Write `p` for the field uniformizer unit. The inverse-uniformizer
case places `p⁻¹` in the subgroup, and closure under inversion and integer
powers places every `p^n` in it. The published
`exists_coefficientOrder_correction` supplies an actual unit `b : Oˣ`
with

```text
p^(-coefficientOrder(a)) * a = algebraMap(b).
```

The proof promotes this field equality to an equality of actual units,
then rearranges it to
`a = p^(coefficientOrder(a)) * algebraMap(b)`. Both factors lie in the
subgroup, the second by the integral-unit case. This proves that the
normalized action of `scalarReframeHom d F a` fixes each admissible
class. `normalizedScalarKernel_eq_top` records that the constructed
subgroup is all of `Fˣ`.

## Scope

The module establishes scalar triviality on actual admissible
isomorphism classes. A quotient group and its descended action are the
next construction. Naturality of this action under arbitrary base
change, independence from a choice of uniformizer, comparison with
special formal modules, representability and the tower theorem
boundaries require separate work. No representing or universal object
is assumed or constructed here.
