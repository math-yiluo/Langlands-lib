# Subfields of the complex numbers are fixed fields

Author: Worker 109.

`Langlands.Shimura.complexFixedField` proves the complete published proposition
`Langlands.Shimura.ComplexFixedFieldStatement`: for every intermediate field
L of ℂ/ℚ, the fixed field of its fixing subgroup equals L. The theorem has no
additional hypotheses and covers transcendental subfields and infinite-degree
extensions. The statement and all its imported definitions are unchanged.

The proof imports
`Langlands.FieldTheory.AlgClosedAutomorphismExtensionProof` and uses its theorem
`Langlands.FieldTheory.algClosedAutomorphismExtension`.
The private helper `complexFixedField_of_extension` reduces the target to
`Langlands.FieldTheory.AlgClosedAutomorphismExtensionStatement.{0, 0}`;
the public closing theorem discharges that hypothesis with the imported result.

The general extension theorem is specialized to the complex numbers and
fields in universe zero. It says that every field automorphism of every
field K embedded in the complex numbers extends to a ring automorphism of
the complex numbers, with the stated compatibility on the algebra map. The helper
`extend_intermediate_aut` uses the scalar-tower identity to show that an extension
of an L-algebra automorphism still fixes L.

For a transcendental x, `exists_translation` first observes that x+1 is also
transcendental: otherwise subtracting the integral element 1 would make x
algebraic. `RatFunc.algEquivOfTranscendental` identifies L(x) and L(x+1) with
the rational-function field. The equality L(x+1)=L(x) turns the resulting
isomorphism into an L-automorphism sending x to x+1.

For algebraic x, `algebraic_mem_of_fixed` places x in the relative algebraic
closure A of L in the complex numbers. Mathlib supplies that A is an algebraic
closure of L and hence a Galois extension in characteristic zero. Every
L-automorphism of A extends, using the extension theorem, to an automorphism of
the complex numbers fixing L. If x is fixed by every such automorphism, the
infinite Galois fixed-field theorem for A/L puts x in L.

The reduction translates fixed-field membership using
`IntermediateField.fixingSubgroupEquiv`. In the algebraic case it applies the
preceding helper. In the transcendental case it extends the translation and
contradicts x=x+1. The inclusion of L in its fixing group's fixed field is the
standard Galois-connection inclusion. No algebraicity of the complex numbers
over L or finite-degree hypothesis is used.

These are internal derived lemmas implementing a variant of the expected route
in the unchanged [statement documentation](ReflexGaloisStatement.md). The
algebraic case uses the relative algebraic closure and infinite Galois theory
instead of choosing a second minimal-polynomial root. That documentation records
the original target's provenance; no additional original-literature claim is
made here. The generic extension theorem and the cited Mathlib constructions
supply the formal prerequisites.
