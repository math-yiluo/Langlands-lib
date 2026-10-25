# Topology and continuous actions on rationalized lattices

Module `Langlands.Topology.Rationalization.Lattice`, namespace
`Langlands.Topology.Rationalization`. Author: Worker 108.

## Construction and hypotheses

The carrier is Mathlib's tensor product `ℚ ⊗[ℤ] M`, with its existing
additive commutative group and left rational module structure. Its topology
is exactly `finalTopology M` from [Basic](Basic.md): a subset is open if and
only if its inverse image under every map `x ↦ q ⊗ₜ[ℤ] x`, for `q : ℚ`,
is open in `M`. This module installs that definition locally when forming
its topological declarations. There is no arbitrary topology parameter on
the tensor product, no comparison hypothesis, and no global topology instance.

Except for `exists_chart`, the scalar homeomorphism and purely algebraic action definitions,
the results assume `[AddCommGroup M] [TopologicalSpace M]
[IsTopologicalAddGroup M]` and the explicit conditional hypothesis

```lean
hM : ∀ n : ℕ, 0 < n → IsOpenEmbedding (fun x : M => n • x)
```

Hausdorffness and compactness are separate assumptions, used as listed below.
In particular, `hM` is not asserted for every compact abelian group. Its
injectivity part implies absence of additive torsion; the proof derives this
fact rather than assuming an unproved rank or torsion statement. Its openness
part controls the topology of the integral image.

## Topological interface

All conclusions on the tensor product in this table use `finalTopology M`.
The standard hypotheses in the preceding section, including `hM`, apply
unless the row explicitly gives weaker hypotheses.

| Declaration | Additional hypotheses and conclusion |
| --- | --- |
| `scalarHomeomorph q hq` | Only `AddCommGroup M`, `TopologicalSpace M`, and `hq : q ≠ 0` are needed. The homeomorphism sends `z` to `q • z` and its inverse sends `z` to `q⁻¹ • z`. |
| `scalarHomeomorph_apply`, `scalarHomeomorph_symm_apply` | With the same weaker hypotheses, these simp lemmas give the two formulas just stated. |
| `isOpenEmbedding_integral hM` | The map `x ↦ (1 : ℚ) ⊗ₜ[ℤ] x` is an open embedding. Thus the original topology of `M` is the topology induced from its image. |
| `isOpenEmbedding_chart hM q hq` | For `hq : q ≠ 0`, the `q`-th tensor chart is an open embedding. |
| `topologicalAddGroup hM` | Addition and negation on the rationalization are continuous, expressed as `IsTopologicalAddGroup`. |
| `hausdorff hM` | Assuming `[T2Space M]`, the rationalization is a `T2Space`. |
| `compactOpen_integral hM` | Assuming `[CompactSpace M]`, the range of the integral chart is both compact and open. No Hausdorff assumption is needed for this conclusion. |
| `locallyCompact hM` | Assuming `[CompactSpace M]`, the rationalization is a `LocallyCompactSpace`. This lemma also does not require a Hausdorff assumption. |

The class-valued results are theorems for local installation, not globally
registered instances. For a compact Hausdorff lattice satisfying `hM`, use
`letI := finalTopology M`, then install `topologicalAddGroup hM`,
`hausdorff hM`, and `locallyCompact hM` locally as needed. The resulting
rationalization is a Hausdorff locally compact topological additive group,
with the integral lattice as a compact open subspace.

Continuity of rational scalar extension is already supplied by the imported
`continuous_baseChange` from Basic. For any continuous additive homomorphism
`f : M →+ N`, it proves continuity of
`f.toIntLinearMap.baseChange ℚ` from `finalTopology M` to `finalTopology N`.
That result needs only additive commutative group structures and topologies;
it therefore applies in particular to two compact Hausdorff lattices with
positive multiplication open embeddings. No new algebraic extension is defined
for this purpose.

## Implemented topological proofs

The algebraic helpers use Mathlib's
`tensorProduct_isLocalizedModule` instance to regard the existing tensor
product as localization at the nonzero integers. They do not replace its
carrier by a new type. Once `IsAddTorsionFree M` is available,
`IsLocalizedModule.injective_iff_isRegular` and injectivity of nonzero integer
multiplication show that the integral chart is injective. Localization
surjectivity places every tensor in some nonzero rational chart. The public
theorem `exists_chart` exposes this covering result for reuse by
[Comparison](Comparison.md) and
[AdelicScalarTopology](../../AbelianScheme/Tate/AdelicScalarTopology.md);
it requires only `[AddCommGroup M]` and no topology or torsion hypothesis. The finite
common-denominator lemma `IsLocalizedModule.exist_integer_multiples_of_finite`,
applied to a Boolean-indexed pair, places any two tensors in the same nonzero
chart. These covering statements need only the additive group structure.

The key identity, for torsion-free `M`, is

```text
q ⊗ₜ[ℤ] x = (1 : ℚ) ⊗ₜ[ℤ] y  ↔  q.num • x = q.den • y.
```

Multiply the tensor equality by the nonzero rational `q.den`, use
`q * q.den = q.num`, move integer scalars across the tensor sign, and use
injectivity of the integral chart. Consequently the inverse image of the
integral image of an open set `U` under the `q` chart is exactly

```text
(fun x => q.num • x) ⁻¹' ((fun y => q.den • y) '' U).
```

The image on the right is open by `hM` because `q.den > 0`; its inverse image
is open because fixed integer multiplication on a topological additive group
is continuous. The defining open-set characterization of `finalTopology`
therefore shows that the integral chart is open. Together with its continuity
from Basic and its injectivity, this proves the open embedding result.

Basic proves continuity of every fixed rational scalar multiplication,
including zero. For nonzero `q`, the maps multiplying by `q` and `q⁻¹` are
mutual inverses, giving `scalarHomeomorph`. Composition with the integral
embedding gives the open embedding for every nonzero chart.

For continuity of addition at `(z,w)`, choose one nonzero chart containing
both tensors. The product of its open embeddings transports the desired local
continuity statement to `M × M`, where it follows from continuity of addition
and of the chart. Negation follows from Basic's universal continuity criterion,
since its composite with a chart is that chart after negation on `M`.

To prove Hausdorffness, prove that zero is closed. Under a nonzero chart the
inverse image of `{0}` is `{0}` by injectivity; under the zero chart the inverse
image of its complement is empty. These facts and Hausdorffness of `M` give
closedness of zero for the final topology. The topological additive group
criterion `IsTopologicalAddGroup.t2Space_iff_zero_closed` then applies.

If `M` is compact, continuity of the integral chart gives compactness of its
range, while its open embedding gives openness. Its range contains zero, so
it is a compact neighborhood of zero. Mathlib's
`IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup` gives local compactness.

## Rationalized actions

Let `Γ` be a group with `[DistribMulAction Γ M]`. No topology, compactness,
separation, or hypothesis `hM` is needed for the following algebraic definitions
and formulas. A group action preserving addition and zero acts by additive
automorphisms because the inverse group element supplies the inverse map.

`actionMap g : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ ⊗[ℤ] M` is exactly

```lean
(DistribSMul.toAddMonoidHom M g).toIntLinearMap.baseChange ℚ
```

`actionMap_tmul` gives `actionMap g (q ⊗ₜ x) = q ⊗ₜ (g • x)`.
Tensor induction proves `actionMap_one` and `actionMap_mul`, namely
`actionMap 1 z = z` and `actionMap (g * k) z = actionMap g (actionMap k z)`.
The pure-tensor steps use the original action laws; additivity proves the sum
steps, and simplification proves the zero steps.

`rationalAction` packages these maps as
`DistribMulAction Γ (ℚ ⊗[ℤ] M)`. The identity and multiplication laws are the
preceding tensor-induction results; linearity supplies preservation of zero
and addition. This is a definition marked `instance_reducible`, with no global
or scoped instance registration. Install it locally using
`letI := rationalAction (M := M) (Γ := Γ)`. The theorems
`rationalAction_smul` and `rationalAction_tmul`, explicitly referring to this
local action, record respectively the scalar-extension expression and its
pure-tensor formula. Each `actionMap g` is rational-linear, so these formulas
also use the existing rational module structure without altering it.

With the standard topological hypotheses on `M` and `hM`, additionally assume
`[TopologicalSpace Γ] [ContinuousSMul Γ M]`. The result
`continuous_actionMap hM` proves joint continuity of
`(g,z) ↦ actionMap g z` for the product of the given topology on `Γ` and
`finalTopology M`, with target topology `finalTopology M`.
At `(g,z)`, choose a nonzero chart containing `z`. The product of the identity
on `Γ` with this open chart reduces continuity to the composite of the original
joint action on `M` and the chart. The pure-tensor formula identifies that
composite with the required map. `continuousSMul_rationalAction hM` packages
the result as `ContinuousSMul` for the locally installed `rationalAction`.
Continuity of multiplication or inversion on `Γ` is unnecessary for this
argument, so it applies in particular when `Γ` is a topological group.
Neither compactness nor Hausdorffness of `M` is needed for action continuity.

## Provenance and boundary

This is internal project mathematics: the local chart arguments are derived
from the final topology in Basic and Mathlib's localization, tensor product,
and topological group APIs. They are not presented as a quotation or
formalization of a particular literature theorem. Basic is reused by import;
the tensor carrier, rational scalar action, and algebraic base change are
Mathlib's existing constructions. The proof descriptions above follow the
implemented Lean proofs.

This generic unit does not construct the finite-etale geometric monodromy
or specialize it to full or away integral Tate limits. Verifying compactness,
Hausdorffness, positive multiplication open embeddings, and the continuous
integral action for those geometric objects remains the responsibility of the
parent geometric development. This module provides the conditional topology
and action interface once those inputs are established. It makes no assertion
of joint scalar continuity for the usual real topology on `ℚ`, and does not
construct or trivialize root-of-unity twists.
