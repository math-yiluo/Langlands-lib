# Local H¹ vanishing and H² invariant existence

`Langlands.ClassFieldTheory.Local.CohomologyExistence` is a proposition
definition, not a theorem proof or a constructor for invariant maps.
For every prime `p` and every `F : PadicField p`, it asserts:

- Continuous H¹ of the actual absolute Galois group with discrete
  algebraic-closure units is zero, and continuous H² admits an additive
  equivalence to the actual quotient Q/Z.
- For every finite Galois extension `L/F`, ordinary relative H¹ with
  coefficients `Lˣ` is zero, and relative H² admits an injective additive
  invariant map whose range is the subgroup of Q/Z annihilated by
  `[L:F]`.

The zero-group assertions use `Subsingleton` on an additive group. The H²
assertions quantify the existence of actual maps between the cohomology
groups defined in `Cohomology.lean`; they do not redefine those groups or
assume their classification. Because `[L:F]` is positive for a finite field
extension, the specified range is precisely `(1/[L:F])ℤ/ℤ`.

The base field and finite extension retain independent universes `u` and
`v`. `F` includes exactly a field, its specified Q_p algebra structure,
and finite dimensionality. Neither `F.TopologicalData` nor a local
class-formation record is assumed. The canonical local-field realization
is available independently; the cohomology groups themselves use the
Krull topology and discrete coefficient topology.

## Scope of this target

This is the existence and vanishing part of the local framework. It does
not choose a canonical invariant map, distinguish it from its negative,
or claim that independently chosen relative and absolute maps agree.
The restriction/corestriction laws, genuine finite-to-absolute comparison,
arithmetic normalization, fundamental-class laws, and Tate cup-product
statements are further required families of the assigned task.

In particular, this target must not be treated as a supplied arithmetic
invariant or as completion of the local class-formation assignment.
The later normalization must select Serre's arithmetic-Frobenius
convention. Its fundamental class has invariant `+1/[L:F]`; the inverse
of its degree `-2` cup-product is arithmetic reciprocity. The host's
geometric reciprocity uses the inverse convention. No choice-based
constructor is introduced here.

## Original source and exact correspondence

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, GTM 67, Springer, 1979. Registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained file `C:/Central-Library/Serre--Local Fields--1979.pdf`.

| Lean assertion | Original source |
| --- | --- |
| Relative H¹ vanishes for every finite Galois `L/F`. | Chapter X, section 1, Proposition 2, printed page 150 (PDF page 156), Hilbert's theorem 90. |
| Absolute H¹ vanishes with discrete closure units. | Chapter X, section 3, printed page 154 (PDF page 160), defines the direct-limit cohomology and describes its computation by continuous cochains; section 4, printed page 156 (PDF page 162), explicitly records absolute H¹ = 0. |
| Absolute H² admits an additive equivalence to Q/Z. | Chapter XIII, section 3, Proposition 6, printed page 193 (PDF page 198), defines the local invariant isomorphism. This target asserts its existence without choosing its normalization. |
| Relative H² embeds with image `(1/[L:F])ℤ/ℤ`. | Chapter XIII, section 3, Corollary 2 to Proposition 7, printed page 194 (PDF page 199). The source uses the actual finite-to-absolute map; the present target states only the resulting injective invariant-map existence. |
| These assertions apply to the local multiplicative formation. | Chapter XIII, section 4, Theorem 1, printed pages 195–196 (PDF pages 200–201), especially axioms I and II(a). |

The interpretation of absolute H² as continuous cohomology is the
continuous/direct-limit comparison, not an opaque identification in the
definitions. That comparison is a separate prerequisite theorem. No
central-simple-algebra Brauer group is silently equated with continuous
cohomology in this target.

## Dependencies and verification boundary

The cohomology definitions come from the paired
`Langlands/ClassFieldTheory/Local/Cohomology` module and the pinned
Mathlib complexes. The local-field domain is the accepted
`Langlands.LocalField.Definitions` artifact
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1, declaration
`Langlands.PadicField`. Its current published Lean hash is
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`;
the published Markdown hash is
`6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
with Lean 4.34.0 and Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.
This file contains no proof of the proposition. Its later proof must be
bound to the independently accepted exact target.
