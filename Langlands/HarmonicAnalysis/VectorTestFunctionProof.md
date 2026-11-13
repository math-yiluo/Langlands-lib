# Renard II.1.2: vector-valued disjoint indicators and the canonical tensor maps

Worker 132 proves the unchanged public statement
`Langlands.HarmonicAnalysis.VectorTestFunctionStatements.Assertions.{uX, uV}`.
The theorem is `Langlands.HarmonicAnalysis.VectorTestFunctionProof.assertions`.
It uses the carriers and maps from
`Langlands.HarmonicAnalysis.VectorTestFunction`, unchanged:

- `LocallyConstant X V`, Renard's \(C^\infty(X,V)\);
- `Space X V`, Renard's \(D(X,V)\);
- the original scalar `SchwartzBruhat X`;
- `compactBilinear`, `smoothTensorMap` and `compactTensorMap`.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.1.2, printed
p.32 / PDF p.38. That page has equations (II.1.2.3) and (II.1.2.4) and
the paragraph right after them. It also points back to the lemma on
printed p.31 / PDF p.37. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 132 read PDF p.38. The source states the two injections without
proof. It gets surjectivity of (II.1.2.4) from the finite disjoint
decomposition. The Lean proof below supplies all of these arguments.

## Vector-valued disjoint indicators

`disjointIndicatorDecomposition` proves the first conjunct,
`DisjointIndicatorDecomposition.{uX, uV}`. It uses the same fiber argument
as the published scalar proof
`Langlands.HarmonicAnalysis.TestFunctionDistributionProof.disjointIndicatorDecomposition`.
Let `f : Space X V`. The published lemma
`Langlands.HarmonicAnalysis.finite_range_of_locallyConstant_of_hasCompactSupport`
needs no topology on `V`. It shows that the range of `f` is finite, so the
set `S` of nonzero values of `f` is finite. A finite enumeration
`Fin (card S) ≃ S` lists these values. For each listed value `v`, the set
`U = {x | f x = v}` is defined as follows:

- `U` is clopen because `f` is locally constant (`isClopen_fiber`);
- `U` is compact because it is closed and lies inside `tsupport f`, which
  is compact by the compact-support hypothesis, since `v ≠ 0`;
- distinct listed values have disjoint fibers.

To prove the equality in `Space X V`, the proof evaluates at each point `x`.
The helper `space_sum_apply` evaluates a finite sum in `Space X V`
pointwise. It applies `map_sum` to the linear map "forget compact support,
then coerce to a function". Then `compactBilinear_apply` and
`characteristic_apply` turn the right-hand side into
\(\sum_i \mathbf 1_{U_i}(x)\,v_i\). There are two cases:

- if `f x = 0`, then `x` is in no `U i` and both sides are `0`;
- otherwise exactly one index `i` has `x ∈ U i`, namely the index of the
  value `f x`, and that term equals `f x`.

If `f = 0`, the list of values is empty and `n = 0`.

## Surjectivity of (II.1.2.4)

`compactTensorSurjective` follows the source's argument. The
decomposition gives \(f=\sum_i \chi_{U_i}v_i\). The preimage is the tensor
\(\sum_i \chi_{U_i}\otimes v_i\), using `map_sum` and
`compactTensorMap_tmul`.

## Injectivity of (II.1.2.3) and (II.1.2.4)

The source calls these maps "canonical injections" without proof. The
Lean proof gets both from one general lemma, `lift_injective_of_pointwise`.
Its inputs are:

- a complex module `A` with an injective linear map
  `ev : A →ₗ[ℂ] X → ℂ`;
- a complex module `W` with a linear map `E : W →ₗ[ℂ] X → V`;
- a linear map `φ : A ⊗[ℂ] V →ₗ[ℂ] W` with
  `E (φ (a ⊗ₜ v)) x = ev a x • v` for all `a`, `v` and `x`.

Its conclusion is that `φ` is injective. The proof goes as follows.
`V` has the basis `Module.Basis.ofVectorSpace ℂ V`, with no finiteness
condition on its dimension. Mathlib's `TensorProduct.eq_repr_basis_right`
writes any tensor as \(t=\sum_{i\in c.\mathrm{support}} c_i\otimes b_i\)
for a finitely supported family `c` in `A`. Suppose `φ t = 0`. Applying
`E` and evaluating at `x` gives \(\sum_i \mathrm{ev}(c_i)(x)\,b_i = 0\).
The basis is linearly independent (`linearIndependent_iff'`), so every
coefficient \(\mathrm{ev}(c_i)(x)\) is zero. This holds for every `x`, and
`ev` is injective, so each \(c_i = 0\). Hence `c = 0` and `t = 0`.
`injective_iff_map_eq_zero` turns this into injectivity.

The task context suggests the same argument with a basis of the span of
finitely many vectors. The Lean proof uses a basis of all of `V` instead.
The two applications are:

- `smoothTensorMap_injective`: `A = LocallyConstant X ℂ` and
  `W = LocallyConstant X V`. Both `ev` and `E` are the coercion
  `LocallyConstant.coeFnₗ ℂ`, which is injective by
  `DFunLike.coe_injective`.
- `compactTensorMap_injective`: `A = SchwartzBruhat X` with `ev` the
  submodule inclusion `(schwartzBruhatSubmodule X).subtype` (injective by
  `Submodule.injective_subtype`), and `W = Space X V` with `E` the coercion
  composed with `inclusion`.

In both cases the pointwise hypothesis holds by `rfl`.

## Assembly and scope

`smoothTensorInjective`, `compactTensorInjective` and
`compactTensorSurjective` state the remaining conjuncts in their exact
public form. `assertions` puts the four conjuncts together in the public
order.

The proof adds no hypotheses. The domain `X` has only the instances in the
public statement. The coefficient space `V` has only `AddCommGroup V` and
`Module ℂ V`: no topology, dimension bound, countability or nonemptiness.
Empty `X` and the zero space are included. The universes `uX` and `uV` are
independent, as in the statement. The general lemma uses two more
universe variables, `uA` and `uW`, which are instantiated in the
applications.

Mathlib results used (pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`):

- `TensorProduct.eq_repr_basis_right` in
  `Mathlib/LinearAlgebra/TensorProduct/Basis.lean`;
- `Module.Basis.ofVectorSpace` in
  `Mathlib/LinearAlgebra/Basis/VectorSpace.lean`;
- `linearIndependent_iff'` in
  `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`;
- `injective_iff_map_eq_zero`;
- `LocallyConstant.coeFnₗ`, and `IsLocallyConstant.isClopen_fiber` and
  `isClosed_fiber`.

These lemmas are called, not copied.

Development check `d01e8a50-017e-4f02-b0bc-8052e7d5a380` built the module
with zero errors and zero warnings. It inspected `assertions`: the universe
parameters are `uX, uV` and the axioms are `propext`, `Classical.choice`
and `Quot.sound`. Publication still needs independent review and validation
of the exact candidate.
