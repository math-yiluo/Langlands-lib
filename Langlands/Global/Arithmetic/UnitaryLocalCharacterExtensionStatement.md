# Unitary extension of one finite local character

Author: Worker 5167, using the carried draft by Worker 1607.

`Langlands.Global.UnitaryLocalCharacterExtensionStatement.{u}` is a
proposition definition, with arbitrary field universe `u`. It says that for
every number field `F : Type u`, finite place `v`, and continuous homomorphism
`χ : (FiniteCompletion F v)ˣ →ₜ* ℂˣ` whose complex values all have norm one,
there is an actual `HeckeCharacter F` that is globally unitary and whose
`finiteComponent v` equals `χ` as a continuous homomorphism.

The definition introduces a statement, not a proof or an assumption of its
truth. It has no finite-order, algebraicity, ramification, archimedean
prescription, or compact-idele-class hypothesis. It includes local characters
of infinite order. It prescribes exactly one finite component; all other
components may be chosen by the extension.

## Actual objects and topology

The sole import is `Langlands.Global.HeckeCharacter`. Its underlying arithmetic
objects are those of `Langlands.Global.Adelic`: `FinitePlace F` is the
height-one spectrum of the ring of integers, `FiniteCompletion F v` is
`v.adicCompletion F`, and `IdeleClasses F` is the actual idele group modulo
the principal ideles, with the quotient topology. The idele topology uses the
units topology, which records both a value and its inverse.

A `HeckeCharacter F` is a continuous multiplicative map
`IdeleClasses F →ₜ* ℂˣ`. Its `IsUnitary` predicate requires norm one on
every idele class. Its finite component is composition with
`finiteClassInclusion F v`, the continuous map obtained by inserting a local
unit at `v`, inserting one elsewhere, and passing to the idele-class quotient.
Thus the conclusion asserts equality with the given map on the entire local
multiplicative group.

The main interface uses the natural topology of `v.adicCompletion F`.
In `Langlands.Global.CompletionPadic`,
`CompletionPadic.padicField v` has that same field carrier and
`CompletionPadic.completion_topology_eq` identifies the natural topology with
`(CompletionPadic.padicField v).canonicalTopologicalData.topology`.
The topology on units is determined by the field topology, so this equality
also identifies their unit-group topologies and continuous character types.
After transport along this equality, the input is a
`Langlands.Correspondence.QuasiCharacter (CompletionPadic.padicField v)`,
as defined in `Langlands.Correspondence.LocalConventions`. This transport
preserves the character's underlying function, values, and norm-one condition.
No topology comparison is an extra hypothesis of the proposition.

## Source correspondence and unitarity

Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
un corps p-adique*, Inventiones Mathematicae 139 (2000), 439–455, end of
§2.8, printed p.448 (PDF p.10), explicitly asserts extension of every character
of the chosen finite local multiplicative group to a character of the
idele-class group. This is used there for twisting and the rank-one case.
Footnote 1 on printed p.439 (PDF p.1) specifies that a quasi-character is
continuous with values in the complex units and that a character is unitary.
Consequently Henniart's convention already includes unitarity; the Lean
statement makes this condition explicit on both the input and output.

The standard general theorem supplying preservation of modulus one is
Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), Corollary 4.42, printed p.113 (PDF p.126). It extends a continuous
circle-valued character of a closed subgroup of a locally compact abelian
group to the whole group. Theorem 4.40 immediately above it describes the
surjectivity of restriction of characters, using Pontryagin duality.
Chapter 4 and §4.1, printed pp.95–96 (PDF pp.108–109), give the locally
compact abelian setting and the continuous circle-valued character convention.
These passages were read directly in the retained originals.

The norm-one conclusion is stronger than existence of an arbitrary
complex-unit-valued continuous extension. Folland supplies the unitary
extension route; it is not necessary to reinterpret Henniart's word
"character" as nonunitary. The arbitrary-number-field, arbitrary-universe
Lean formulation is the intrinsic local-to-global extension consequence of
that route, rather than a quotation of a universe-indexed theorem from
Henniart.

Registered originals:

- `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
  retained file
  `/home/taskhub/central-library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`;
  locators as above.
- `folland-2015-abstract-harmonic-analysis-second`, SHA256
  `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`,
  retained file
  `/home/taskhub/central-library/Folland--A Course in Abstract Harmonic Analysis (Second Edition)--2015.pdf`;
  Corollary 4.42, Theorem 4.40, and the Chapter 4 conventions as above.

## Remaining formal prerequisites

The intended proof must establish or reuse the following facts for these
actual objects, in every field universe:

1. `finiteClassInclusion F v` is injective, has closed range, and identifies
   `(FiniteCompletion F v)ˣ` topologically with that range. Continuity of the
   map alone does not supply continuity of the inverse on its image.
2. The idele-class group is a locally compact Hausdorff abelian topological
   group. Its quotient separation must be justified, in particular through
   closedness of the principal-idele subgroup. The necessary local compactness
   and separation facts for the local unit group and the restricted-product
   and quotient constructions must also be available. The completion itself
   already has the published local-field realization
   `CompletionPadic.topologicalData v`; its `localField` field supplies local
   compactness in the natural topology. The proof still needs the corresponding
   facts on the multiplicative subgroup and the idele-class quotient.
3. The closed-subgroup unitary character-extension theorem, with the required
   universe generality, must be formalized or reused. An algebraic extension
   alone does not establish continuity.
4. Corestrict the given norm-one character to the circle group, transfer it
   to the closed image from item 1, extend it by item 3, and compose with the
   continuous inclusion into `ℂˣ`. Verify global `IsUnitary` and equality of
   continuous homomorphisms after composition with `finiteClassInclusion F v`.

These are proof gates, not premises added to the statement. The imported
adelic module already constructs the actual continuous local maps and
quotient; it does not by itself prove the closed-image topological
identification required here. The published
`Langlands.Topology.exists_continuous_complex_character_extension` in
`Langlands.Topology.ComplexCharacterExtension` treats an open subgroup.
The finite-place image is generally not open, so that theorem does not
directly provide item 3. Likewise
`Langlands.Global.FiniteOrderCharacterPrescriptionStatement` only covers
finite-order input and does not settle this unrestricted proposition.

The exact proof is a separate successor. No automorphic twist, Weil
representation, or relative isometry construction is asserted by this file.
