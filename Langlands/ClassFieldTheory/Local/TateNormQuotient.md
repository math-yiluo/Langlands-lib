# The field norm quotient as degree-zero Tate cohomology

Author: Worker 42.

For any finite Galois extension `L/K`, with independently sized carriers,
`tateZeroEquivNormQuotient K L` identifies Mathlib's actual degree-zero
Tate cohomology of the Galois action on `Lˣ` with the additive notation for
the existing `Langlands.LocalClassField.NormQuotient K L`.
The quotient is `Kˣ / N_{L/K}(Lˣ)`, using the determinant-defined field
norm from `Langlands.ClassFieldTheory.Local.Norms` (formerly at
`Langlands.LocalClassField.Norms`). No replacement norm subgroup or
reciprocity map is introduced.

`baseUnitNormClass` sends a base-field unit into the invariant-unit
quotient constructed by `Langlands.Tate.ZeroDefinitions`.
`normToInvariants_units` identifies the representation norm with the
embedded field norm, using the certificate in `UnitInvariants`.
`baseUnitNormClass_ker` then proves that this map has precisely the
existing field norm subgroup as its kernel. Surjectivity follows from
the proved identification of fixed units with base-field units and
surjectivity of the quotient projection. The first isomorphism theorem
constructs `normQuotientEquivInvariantQuotient`.

Composing its inverse with the published comparison `Langlands.Tate.zeroEquiv`
gives the stated additive equivalence. The representative equation
`tateZeroEquivNormQuotient_zeroClass` fixes the comparison: the Tate class
of a base unit is sent to its usual norm-quotient class. The intermediate
constructions allow any finite enumeration of the Galois group; the
public Tate comparison uses the same `Fintype.ofFinite` enumeration
as `relativeTateCohomology`. Neither field carrier is resized, and only
the scalar integers are lifted to the extension's universe.

The original source is Jean-Pierre Serre, *Local Fields*, English
translation by Marvin Jay Greenberg, Springer GTM 67 (1979), Chapter VIII,
Section 1, printed pages 127–129 (PDF pages 133–135), for degree-zero Tate
cohomology as invariants modulo norms. Chapter XI, Section 3, printed page
169 (PDF page 175), uses this quotient for the multiplicative formation.
The kernel calculation and transport between the existing Lean objects
are derived implementation work. Source ID: `serre-1979-local-fields`;
retained original `C:/Central-Library/Serre--Local Fields--1979.pdf`;
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

This construction supplies the degree-zero endpoint needed by the later
degree-minus-two Tate reciprocity statement. It does not assert the
cup-product isomorphism, identify the degree-minus-two source with
abelianization, or prove local class field theory. The construction
introduces no Frobenius sign choice; that choice enters through the
fundamental class used in the later cup product.
