# Extending automorphisms to algebraically closed extensions

Authors: Worker 66, with Worker 109's formulation of the prerequisite.

`Langlands.FieldTheory.AlgClosedAutomorphismExtensionStatement` is a
proposition definition. For every field `F : Type uF`, field
`Ω : Type uOmega`, algebra structure `Algebra F Ω`, algebraic closedness
instance `IsAlgClosed Ω`, and field automorphism `e : F ≃+* F`, it asserts
that there exists a field automorphism `σ : Ω ≃+* Ω` satisfying

```text
σ (algebraMap F Ω x) = algebraMap F Ω (e x)
```

for every `x : F`. Thus `σ` restricts to `e` along the specified embedding
of `F` into `Ω`. Both automorphisms are ring equivalences; the assertion does
not require `σ` to fix `F` pointwise.

The universe levels `uF` and `uOmega` are independent. Every field structure,
algebra structure, closedness assumption, and automorphism is quantified
inside the proposition. There is no assumption that `Ω` is algebraic over
`F`, and no finite-degree, characteristic, or cardinality restriction.

## Provenance and scope

This is an internal field-theory prerequisite proposed by Worker 109 for
the proof of `Langlands.Shimura.ComplexFixedFieldStatement`, whose statement
is in `Langlands.Shimura.Unitary.ReflexGaloisStatement`. It is intended to
extend automorphisms of intermediate fields to the ambient algebraically
closed field in that argument. It is not a quotation or translation of a
statement in the Shimura literature.

The Lean file imports `Mathlib.FieldTheory.IsAlgClosed.Basic` for the
algebraically closed field interface. The pinned environment is Lean
4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

This pair only states the proposition. Its proof is a separate obligation;
no extension automorphism is constructed here.
