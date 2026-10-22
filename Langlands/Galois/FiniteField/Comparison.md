# Target for the finite-field Galois comparison

`FrobeniusComparison` states the full comparison for every finite field
`k : Type u`, with no restriction on `u`. It is a proposition definition,
not a proof and not an assumption used to define the absolute Galois group.

Its first assertion is existence of a continuous group equivalence from
Mathlib's actual `Field.absoluteGaloisGroup k` with Krull topology to
`Langlands.Weil.ProfiniteIntegers`. The latter is the already accepted genuine
profinite completion of `Multiplicative ℤ`. A `ContinuousMulEquiv` includes
bijectivity, multiplication preservation, and continuity in both directions.
The equivalence must send geometric Frobenius to the canonical image of `+1`
and arithmetic Frobenius to the image of `-1`.

The remaining assertions fix the field-theoretic meaning of these generators.
Arithmetic Frobenius acts on the algebraic closure by `x ↦ x ^ Nat.card k`.
For every finite-dimensional intermediate field `L` of that closure, continuous
restriction takes both absolute Frobenius elements to the corresponding
automorphisms of `L`. Arithmetic Frobenius acts there by the same cardinality
power. Each of the arithmetic and geometric elements has order `[L : k]`;
every element of `Gal(L/k)` is a power with exponent less than `[L : k]`.
This explicitly covers all finite intermediate fields, not a hypothesized
cofinal family.

The source is Serre, *Local Fields* (1979 English translation), Chapter XIII,
section 2, printed pages 190–191: the profinite-integer description of a
quasi-finite field, its finite cyclic extensions, and Example (a) for a finite
field. Source ID `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The geometric normalization follows the convention in Henniart,
“Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique”, *Inventiones mathematicae* 139 (2000), page 439, section 1.1.
Source ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
It is the inverse of Serre's arithmetic generator.

The definitions and Mathlib support are documented in `Frobenius.md`. The
comparison is with a finite residue field's absolute Galois group; it does not
construct the residue homomorphism from a local field, identify its inertia,
or identify a local Weil group.
