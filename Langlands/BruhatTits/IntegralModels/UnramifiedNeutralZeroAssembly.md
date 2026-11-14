# Neutral integral points from the zero-fixer decomposition

This internal assembly works at arbitrary universe parameter `u` with any
supplied maximal-unramified building datum `C`, any original zero datum `E`,
and any supplied relative-component model `D` whose full integral points are
the character-valuation kernel intersected with the pointwise fixer of the
apartment subset `Ω`.

`wholeApartmentZeroFixer_eq_apartmentTorusIwahori` is unconditional. Replace
the torus choices in `E` by the constructed
`UnramifiedZeroDatum.withApartmentTorus C E`. Its torus represents the whole
centralizer of the original apartment torus. Independence of zero data
identifies its zero subgroup with the original `E.zeroPoints`. The
whole-apartment comparison for a compatible torus therefore identifies the
original whole-apartment zero fixer with this new torus's norm-defined
Iwahori image. The original building datum and ambient rational group are
retained.

`unramifiedNeutral_integralPoints_eq_zeroFixer` retains three explicit
premises:

- `UnramifiedTorusIwahoriModelStatement`, providing the connected smooth
  model of the norm-defined torus Iwahori subgroup;
- `UnramifiedTorusConnectedBoundStatement`, bounding connected smooth torus
  model points by that Iwahori subgroup;
- the exact decomposition of the original zero fixer of `Ω` as the join of
  the whole-apartment zero fixer and `C.sharpFixer Ω`.

The proof uses neutral torus/root generation for the constructed compatible
datum, substitutes the preceding unconditional whole-apartment equality,
and applies the decomposition premise. It concludes the neutral equality
for the original arbitrary `E`. No compatibility hypothesis on `E` remains.
The theorem accepts any apartment subset for which the stated premises hold;
it does not prove the decomposition, either torus statement, or existence
of the full model. In the bounded nonempty application, the decomposition
is a separate mathematical input.

`unramifiedNeutralZeroFixerEquiv` packages the resulting equality as a
multiplicative equivalence. Its coercion theorem proves that it preserves
each original ambient rational point.

The provenance is internal composition of the compatible zero-datum
construction, whole-apartment comparison, and neutral torus/root
generation. This supplies the neutral equality used in the untranslated
apartment case of KP Theorem 8.3.13, conditional on the stated inputs. It
does not establish the complete parahoric-model statement.
