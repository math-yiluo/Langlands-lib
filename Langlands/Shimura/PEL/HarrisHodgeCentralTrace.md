# Central traces on the actual regular Kottwitz Hodge module

This module constructs coordinates for the existing regular Kottwitz Hodge module and computes the intrinsic complex trace of its actual central action. Its provenance is internal: the construction and proofs use the published Hodge module in `RegularHodge`, the actual embedding-matrix splitting, and the diagonal-support and support-cardinality theorems in `CocharacterReflexConjugator`.

The parameters are a central simple unitary datum `D` over a totally real number field `E` and its totally complex quadratic extension `K`, the fixed Harris signature charts `C`, a CM section `Φ`, and its proof `hΦ`. The algebra has the stated compatible rational, `E`, and `K` scalar structures. All arithmetic types in this module are in universe zero.

`kottwitzHodgeMatrixEquiv` first identifies
`ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)` with `ℂ ⊗[ℚ] A`, then applies the existing algebra equivalence to the product of `n` by `n` matrix algebras labelled by complex embeddings of `K`. The column criterion uses the existing `kottwitzCocharacterValue_diagonal` formula for the actual cocharacter unit, with the definitionally equal matrix presentation made explicit locally.

`mem_kottwitzHodgeModule_iff_columns` proves that a vector belongs to the actual Hodge module exactly when every column outside `kottwitzEmbeddingSupport` is zero. In the forward direction, the defining right-multiplication equation at the complex unit `-1` forces those entries to vanish. In the reverse direction, the diagonal formula verifies the defining equation for every complex unit.

`KottwitzHodgeCoordinateIndex` consists of an embedding, any row in `Fin n`, and a selected column at that embedding. Its finite-type instance is constructed from these actual finite indices. `kottwitzHodgeCoordinateEquiv` is a complex linear equivalence between the Hodge module and arbitrary complex functions on this index. Its forward map extracts the selected matrix entries. Its inverse fills the other entries by zero and applies the inverse matrix equivalence. The column criterion proves membership and the inverse laws; linearity follows from the algebra equivalence.

`kottwitzHodgeCoordinateEquiv_center` proves that left multiplication by the actual tensor of `algebraMap K A a` acts on coordinate `q` by the scalar `q.1 a`. The proof uses the actual multiplication and the existing formula identifying a central element with the scalar matrix at its labelled embedding.

`trace_kottwitzHodgeAction_center_coordinates` transports the actual central endomorphism through this linear equivalence. In the function basis, its diagonal entry at `q` is `q.1 a`, so intrinsic trace is the sum of these entries. `trace_kottwitzHodgeAction_center` sums first over rows and selected columns, then applies the existing support-cardinality theorem. It proves

```text
traceℂ(left multiplication by a on kottwitzHodgeModule C)
  = n * ∑ i : K →+* ℂ, realHodgeFunction C i * i(a).
```

Here each natural-number multiplicity is cast into `ℂ`. The trace belongs to the actual regular Hodge module with the fixed Kottwitz convention. Its further arithmetic comparison with the Harris–Taylor numerical formula, the corresponding normalized reflex scalar map, and the corrected CM tower remain separate obligations.
