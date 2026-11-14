# Residue field and algebra structures (M243.020–.021)

These are Type-valued source instances in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
They construct the field structure on the fixed-subring quotient and its
algebra structure on the selected residue field.

| Row | Source lines | Adapted declaration | Data |
| --- | --- | --- | --- |
| M243.020 | 236–241, declaration 237 | `decompositionResidueField.instField` | `Field (decompositionResidueField K A)` |
| M243.021 | 242–248, declaration 243 | `selectedResidueField.instAlgebra` | `Algebra (decompositionResidueField K A) (selectedResidueField A)` |

Source: Naganori Yamaguchi's NYLL, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`.
The `noncomputable instance` bodies, docstrings, universes `u v`, and
section variable lines are retained verbatim. Lean retains `[IsGalois K L]`
in M243.020 because its `Ideal.Quotient.field` uses the M243.016 maximality
instance. M243.021 uses M243.019's `LiesOver` proof and
`Ideal.Quotient.algebraQuotientOfLEComap`; its elaborated type has no Galois
hypothesis. Both have `(K : Type u) {L : Type v} [Field K] [Field L]
[Algebra K L] (A : ValuationSubring L)`, with the Galois binder before `A`
only in M243.020. Residue types stay in `Type v`.

Changes are module extraction, prefixing `Langlands.NYLL`, narrowed imports,
new module prose, and the header's modification record. The instance scopes
stay global, as in the source. The imports are the published `IsMaximalProof` (M243.016) and
`LiesOverProof` (M243.019) modules. Their global instances supply maximality
and the lies-over equality used by the unchanged bodies. Mathlib's field and quotient-algebra constructors are reused;
these definitions provide the exact names and structures needed by NYLL
consumers. The field structure is the Mathlib constructor specialized to the
contracted ideal; the algebra structure is the canonical quotient algebra.
A development probe with these prerequisite imports alone found neither
instance through typeclass search for these exact NYLL abbreviations.
These two registrations therefore provide the required instances without
duplicating an applicable existing instance.

Registered source `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Original Apache-2.0 copyright and author header is retained; reuse
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
