# Arithmetic normalization of the actual Harris Hodge trace

This module proves the arithmetic formula for the intrinsic central trace on the existing regular Kottwitz Hodge module, then constructs an explicit conjugated reflex scalar map and its scheme and section maps. Its provenance is internal. It uses the actual coordinate and trace calculation in `HarrisHodgeCentralTrace`, the Harris signature formulas, the existing `HarrisTaylor.lieTraceValue`, and the reflex-field inclusion and scalar map in `HarrisReflexBase`. It does not change those existing definitions.

The parameters are a totally real number field `E`, its totally complex quadratic extension `K`, a central simple unitary datum `D` of degree `n`, and its fixed Harris signature charts `C`. There is also an imaginary quadratic CM field `L`, an `L`-algebra structure on `K`, and a complex embedding `τ₀` of `L`. The charts use exactly `harrisCMSection E (algebraMap L K) τ₀`. All the algebra's displayed rational, `E`, and `K` scalar towers are retained. The intrinsic arithmetic trace theorem also assumes `IsCMField K`, as required by the existing arithmetic value. These arithmetic types and the later schemes have universe zero. No nonexceptional reflex-field hypothesis is imposed.

`HarrisTaylor.sum_embeddings_inducing_eq_trace` first proves that the sum of `i(a)` over embeddings of `K` restricting to `τ₀` is `τ₀(Algebra.trace L K a)`. Its proof gives `ℂ` the `L`-algebra structure defined by `τ₀`, constructs the equivalence between `L`-algebra embeddings and the subtype of ring embeddings with this restriction, and applies Mathlib's separable field-trace formula.

`sum_realHodgeFunction_mul_embedding` uses the actual Harris multiplicities: `n-1` at the distinguished embedding, `1` at its conjugate, `n` at every other embedding restricting to `τ₀`, and zero at the remaining embeddings. The proof rewrites each weighted summand using indicator functions. The imaginary quadratic field is totally complex, so the conjugate distinguished embedding does not restrict to `τ₀`. Summing gives

```text
∑ i, realHodgeFunction C i * i(a)
  = n * τ₀(trace L K a) - distinguishedEmbedding(a)
      + conjugate(distinguishedEmbedding(a)).
```

The multiplicities are cast into `ℂ`. Combining this equality with the intrinsic trace theorem on the actual regular Hodge module gives `trace_kottwitzHodgeAction_center_harrisTaylor`:

```text
traceℂ(left multiplication by a on kottwitzHodgeModule C)
  = distinguishedEmbedding
      (cmConjugation E K (HarrisTaylor.lieTraceValue L K n a)).
```

The endomorphism on the left is the existing `kottwitzHodgeAction` of the double tensor of `algebraMap K A a`. The proof uses linearity of the field trace to extract `n²`, the actual restriction of the distinguished embedding to `L`, and the theorems identifying CM conjugation with complex conjugation under each complex embedding. Thus it computes an actual module trace; it does not merely assign multiplicities to an unrelated endomorphism.

The arithmetic value being compared is the published definition
`complexConj K (algebraMap L K (trace L K (n²*a))) + n*a - complexConj K (n*a)`.
Its original convention is Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3), printed p.90 (PDF p.98; registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`). The present result is a derived comparison with that existing definition. It makes the conjugation relative to the fixed Kottwitz identity Hodge summand explicit; it asserts no equivalence with the full Lie-plus moduli condition.

`harrisTaylorReflexToCM` is the new rational algebra map obtained by composing the existing `harrisReflexToCM` with `cmConjugation E K`. `distinguishedEmbedding_harrisTaylorReflexToCM` proves that its distinguished complex value at `t` is `conjugate(t)`. `harrisTaylorReflexToCM_of_complex_eq` then proves that a reflex element whose complex inclusion is `distinguishedEmbedding(cmConjugation E K b)` maps to `b`. This specifies the normalization that will recover the Harris–Taylor arithmetic trace from the reflex determinant. The earlier unconjugated map remains available with its original meaning.

`harrisTaylorCMToReflexBase` is the actual spectrum morphism of this new scalar map. Its complex-point formula is the spectrum map of the conjugated reflex inclusion. For an actual `p : S ⟶ Spec K`, `harrisTaylorReflexStructure C p` is its composition with that spectrum morphism. The composition theorem proves compatibility with any actual scheme map `T ⟶ S`, and `secHom_harrisTaylorReflexStructure` computes the coefficient map on every open of `S`.

Finally, `harrisReflexSectionDeterminant_harrisTaylor_CM` identifies the existing all-family reflex determinant section at the new structure morphism with the polynomial obtained by first applying `harrisTaylorReflexToCM` to its coefficients and then applying the actual section homomorphism of `p`. This is a coefficient-map identity, proved by composition of polynomial maps. Identifying a particular central coefficient of that determinant with the intrinsic trace, replacing the CM tower, constructing a varying-base joint moduli functor, and obtaining scheme-level representability remain further work.
