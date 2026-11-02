# The ultrametric projective tensor seminorm is a norm

Author: Worker 1010. The module builds on Worker 972's published ultrametric
projective tensor seminorm in `Langlands.Geometry.Analytic.ValuedField.TensorSeminorm`.

## Result and scope

The module proves the published proposition
`Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u}` in
`Langlands.Analysis.NonarchimedeanCompletedTensorStatement`. Its closing theorem is

```lean
Langlands.Analysis.nonarchimedeanCompletedTensor.{u} :
  Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u}
```

It has no outer arguments or added hypotheses. The algebra `W` it produces is the
completion of `E ⊗[F] E'` for the ultrametric projective tensor norm, and `τ` is the
canonical map into that completion. The statement's hypothesis
`IsUltrametricDist F` is not used. Completeness of `F` is used only to bound a
linear functional on a finite-dimensional subspace.

## Implemented proof

The tensor-specific helpers are in the namespace
`Langlands.Analysis.NonarchimedeanCompletedTensorProof`. The generic completion
instance is imported from [UltrametricCompletion](UltrametricCompletion.md)
as `Langlands.Analytic.completion_isUltrametricDist`. `seminormFun`,
`Representation`, `le_seminormFun`, `seminormFun_le`, `seminormFun_add_le` and
`ultrametricTensorSeminorm_tmul_le` come from Worker 972's module: `seminormFun t`
is the infimum, over finite representations `t = ∑ i, a i ⊗ₜ b i`, of
`max_i ‖a i‖ * ‖b i‖`.

### Shortening a representation

`exists_linearIndependent_right` works with an ultrametric seminormed `F`-space `X`
on the left and a normed `F`-space `Y` on the right. It proves by strong induction
on the number of terms that every sum `∑ i, a i ⊗ₜ b i` with all
`‖a i‖ * ‖b i‖ ≤ M` can be rewritten as a sum `∑ j, a' j ⊗ₜ b' j` with linearly
independent right factors `b'` and all `‖a' j‖ * ‖b' j‖ ≤ M`. This generalizes the
elimination step in Worker 972's private `one_le_aux`
(`TensorSeminorm.lean`, original lines 267–321), which invokes
`one_le_of_linearIndependent`.

If `b` is linearly dependent, pick a relation `∑ c i • b i = 0` with some
`c j • b j ≠ 0`, or a zero factor `b j = 0`. If `b j = 0`, the term `j` is dropped.
Otherwise let `k` maximize `‖c i‖ * ‖b i‖`. Then
`b k = ∑_{i ≠ k} d i • b i` with `d i = -(c k)⁻¹ * c i`, and
`‖d i‖ * ‖b i‖ ≤ ‖b k‖`. Replacing `a i` by `a i + d i • a k` for `i ≠ k` and
dropping the term `k` gives the same tensor with one term fewer. The ultrametric
inequality in `X` gives
`‖a i + d i • a k‖ * ‖b i‖ ≤ max (‖a i‖ * ‖b i‖) (‖a k‖ * ‖b k‖) ≤ M`.

`exists_linearIndependent_of_representation` applies this to a `Representation`
`r` of `t : E ⊗[F] E'` with `M = r.value`.

### Left factors lie in a fixed finite-dimensional span

`mem_span_of_linearIndependent` assumes `∑ j, a j ⊗ₜ b j = ∑ p, e p ⊗ₜ f p` with
linearly independent `b`. It shows that every `a j` lies in
`Submodule.span F (Set.range e)`. The proof uses a left inverse `g` of the injective
map `Fintype.linearCombination F b`, from
`LinearMap.exists_leftInverse_of_injective`. Applying
`rid ∘ lTensor X (proj j ∘ g)` to both sides turns the left side into `a j` and the
right side into `∑ p, (proj j (g (f p))) • e p`.

### Positivity

`exists_dual_lid_rTensor_ne_zero` shows that every nonzero `t` has a functional
`φ : Module.Dual F E` with `lid (φ.rTensor E' t) ≠ 0`. Take a representation with
independent right factors. Some left factor `a j₀` is nonzero because `t ≠ 0`.
`Module.Projective.exists_dual_ne_zero` gives `φ` with `φ (a j₀) ≠ 0`. Then
`lid (φ.rTensor E' t) = ∑ j, φ (a j) • b j`, which is nonzero by independence of `b`.

`seminormFun_pos` proves `0 < seminormFun t` for `t ≠ 0`. Fix one representation
`r₀` of `t`, let `V₀` be the span of its left factors, and let
`w = lid (φ.rTensor E' t) ≠ 0`. Since `V₀` is finite-dimensional and `F` is complete,
`φ` restricted to `V₀` is continuous (`LinearMap.toContinuousLinearMap`), so
`‖φ v‖ ≤ C * ‖v‖` on `V₀` with `C = max ‖φ|V₀‖ 1 > 0`. Let `r` be any representation
of `t`. Shorten `r` to `∑ j, a j ⊗ₜ b j` with independent `b` and products at most
`r.value`. By the previous step every `a j` lies in `V₀`, and
`w = ∑ j, φ (a j) • b j`. The ultrametric inequality in `E'` gives
`‖w‖ ≤ max_j ‖φ (a j)‖ * ‖b j‖ ≤ C * r.value`. Hence `‖w‖ / C ≤ seminormFun t`
(`le_seminormFun`), and the left side is positive.

The proof does not use Hahn–Banach extensions, which can fail when `F` is not
spherically complete. It uses no orthogonal bases either: the only functional
that has to be bounded lives on the fixed finite-dimensional space `V₀`.

`seminormFun_smul_le` proves `seminormFun (c • t) ≤ ‖c‖₊ * seminormFun t` by
scaling the left factors of each representation.

### The normed tensor algebra and its completion

Now `E` and `E'` are commutative.

- `tensorRingNorm F E E'` is Worker 972's `ultrametricTensorSeminorm F E E'`, a ring
  seminorm, upgraded to a `RingNorm` by `seminormFun_pos`.
- `NormedTensor F E E'` is a type synonym for `E ⊗[F] E'`. It gets the
  `NormedCommRing` instance from `RingNorm.toNormedRing (tensorRingNorm F E E')`, the
  algebra structure of the tensor product, `NormedAlgebra F` from
  `seminormFun_smul_le`, and `IsUltrametricDist` from `seminormFun_add_le`. By
  `norm_def`, the norm is `seminormFun` by definition.
- The imported `Langlands.Analytic.completion_isUltrametricDist` shows that the uniform completion of an ultrametric
  seminormed group is ultrametric. The proof is by density, using
  `UniformSpace.Completion.induction_on₂` and `norm_coe`.
- `W = UniformSpace.Completion (NormedTensor F E E')`. Mathlib supplies a complete
  normed commutative ring and normed `F`-algebra structure on it.
- `toCompletion F E E' : E ⊗[F] E' →ₐ[F] W` is `UniformSpace.Completion.coeRingHom`
  with `commutes'` by `rfl`. `toCompletion_injective` is
  `UniformSpace.Completion.coe_injective`, which holds because `NormedTensor F E E'` is
  a metric (hence T₀) space. `norm_toCompletion_tmul_le` combines `norm_coe` with
  `ultrametricTensorSeminorm_tmul_le`.

`nonarchimedeanCompletedTensor` packages `W`, its four instances, `toCompletion`, its
injectivity, and the pure-tensor bound.

## Relation to the literature

The statement records Gruson–van der Put, "Banach spaces", Lemma 5.2(2). Their proof
uses `α`-orthogonal families (Lemma 5.2(1)). The implemented proof follows the route
described above instead, and proves only the inequality `≤` on pure tensors that the
statement records.
