# Proof of the finite-field absolute Galois comparison

The closing theorem `frobeniusComparison` proves the full proposition
`FrobeniusComparison`. The public construction `profiniteEquivalence k` is a
continuous group equivalence from Mathlib's actual `Field.absoluteGaloisGroup k`
to `Langlands.Weil.ProfiniteIntegers`. Its associated continuous homomorphism
`toProfiniteIntegers k` can be composed directly with a later local residue map.
The proof never assumes procyclicity, Frobenius classification, or the desired
comparison.

## Finite coordinates and the comparison map

For any homomorphism from the multiplicative integers to a finite group, its
kernel is a finite-index normal subgroup. `liftFinite` projects the actual
profinite completion to the corresponding quotient and factors the homomorphism
through that quotient. This is continuous because the quotient is finite and
discrete. On canonical integer images it agrees with the original homomorphism.

For each finite Galois intermediate field of the algebraic closure, use the
homomorphism sending an integer to the corresponding power of geometric
Frobenius. These finite-coordinate maps are compatible with field restriction:
both sides are continuous and agree on the dense canonical integer image.
Mathlib's `InfiniteGalois.continuousMulEquivToLimit` turns the resulting map to
the finite Galois inverse limit into `fromProfinite`, a continuous homomorphism
to the actual absolute Galois group.

This construction matters for universes. Mathlib's categorical profinite
completion lift uses a common universe for source and target. Here the source
profinite integers are in `Type 0`, while `k : Type u` and its algebraic closure
remain in arbitrary `Type u`. The raw finite-coordinate homomorphisms and the
Galois restriction limit support these different universes directly. No
resizing or replacement of the closure is used.

## Surjectivity and injectivity

Mathlib proves that arithmetic Frobenius generates the Galois group of a finite
field extension and has order equal to its degree. Inverting proves the same
facts for geometric Frobenius. The Krull neighborhood basis at the identity
consists of fixing subgroups of finite Galois intermediate fields. Generation in
each finite restriction therefore proves density of geometric Frobenius powers
in the actual absolute Galois group. These powers lie in the image of
`fromProfinite`. Its source is compact and its target Hausdorff, so its image is
closed; density then proves surjectivity.

For injectivity, fix any finite-index normal subgroup `N` of the integer group
and let `n` be its positive index. Mathlib's `FiniteField.Extension` constructs
an extension of `k` of degree `n`. Embed that extension in the specified algebraic
closure using `IsAlgClosed.lift`; its field range, with the proved range
equivalence, has the same degree. Geometric Frobenius on that range has order
`n`. Its integer-power kernel is contained in `N`, since `n` divides every
exponent in that kernel and the `n`-th power of the integer generator belongs
to `N`.

If an element maps to the identity in the absolute Galois group, its coordinate
in that Frobenius-kernel quotient is the identity: the quotient factor is
injective by the kernel quotient theorem. Compatibility in the profinite limit
then makes its coordinate at `N` the identity. This holds for every `N`, proving
injectivity.

A continuous bijection from the compact profinite integers to the Hausdorff
absolute Galois group is a homeomorphism. Combine this with the proved
multiplication law, then invert, to obtain `profiniteEquivalence`.

## Normalization and compatibility

`profiniteEquivalence_symm_frobenius` identifies every integer image under the
inverse equivalence with the corresponding geometric Frobenius power.
`profiniteEquivalence_geometric` specializes to `+1`.
`profiniteEquivalence_arithmetic` uses inversion to obtain the image of `-1`.
The closing theorem also proves the cardinality-power action on the algebraic
closure and, for every finite-dimensional intermediate field, both restriction
equations, the cardinality-power action there, and generation and order for
both Frobenius conventions.

The finite-intermediate-field statements apply to all finite-dimensional
intermediate fields. Their finiteness follows from finiteness of the base;
Mathlib supplies their Galois property. They are not an assumed cofinal system.

## Provenance and scope

The source theorem is Serre, *Local Fields* (1979 English translation),
Chapter XIII, section 2, printed pages 190–191, including Example (a).
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The inverse sign follows the geometric Frobenius convention in Henniart 2000,
page 439, section 1.1; source `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The implementation uses the finite-coordinate proof above, rather than
assuming Serre's classification as an axiom.

The imported project definitions are the exact Frobenius interface and the
genuine profinite-integer object from the accepted Weil pullback definition.
All other mathematical support comes from pinned Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`, as audited in `Frobenius.md`.
This result does not construct a local residue map, characterize local inertia,
or identify a p-adic Weil group. Native compilation is development evidence;
independent proof checking, semantic review, and publication remain separate
requirements.
