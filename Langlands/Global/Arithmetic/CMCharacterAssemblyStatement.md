# Regular CM unit prescription from its three inputs

Worker 84. This derived proposition concerns the assembly step in Henniart
2000, Section 3.6, Lemma 3, printed p.451. It reuses the actual objects and
four targets of `Langlands.Global.Arithmetic.CMCharacterStatement`.

`Langlands.Global.CMRegularUnitPrescriptionOfInputsStatement.{u,v}` is the
implication from the following three existing arithmetic assertions to
`CMRegularUnitPrescriptionStatement.{u,v}`:

1. `CMUnramifiedInfinityRealizationStatement.{u}`;
2. `CMFiniteCharacterPrescriptionStatement.{u}`;
3. `IntegralUnitCharacterExtensionStatement.{u}`.

The number-field universe `u` and imaginary-quadratic subfield universe `v`
remain independent. The conclusion retains the finite set disjoint from its
conjugates, the actual arithmetic complex conjugation, one common positive
integer multiplier of every infinity weight, distinct weights above the
chosen embedding of the imaginary-quadratic subfield, and agreement with the
prescribed characters on the actual integral units. It does not prescribe
uniformizer values.

The source extends each local unit character to finite order, constructs a
finite-order conjugate-self-dual global character with those finite local
components, and multiplies it by a conjugate-self-dual character unramified
at all finite places that realizes the scaled infinity type. Since the latter
character is trivial on integral units, the local prescription survives.
Multiplication by a positive integer preserves distinct integer weights.

This is an internal decomposition of the published CM regular-prescription
target, with each of its three existence inputs explicit. Defining this
proposition proves neither the implication nor its inputs. Even a proof of the
implication would not prove the CM existence theorem until all three inputs
are proved. It also supplies no Harris normalization, central-character
comparison, or auxiliary general-position construction.

The original passage was read directly by Worker 84 in the registered
Henniart source `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
pp.448–451, including all three character lemmas and their proofs.
The target's separated finite set and embedding-independent infinity weights
are the documented generalizations in the existing CM statement pair.
