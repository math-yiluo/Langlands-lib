# Determinant transport for the first-block fiber kernel

Module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift`.
Namespace `Langlands.RankinSelberg.TwoBlockFirstBlockQuotient`.
Worker 117 authored the transport proofs. They use Worker 27's fiber kernel
construction and the separately submitted normalized mixed-quotient shift.

This internal helper proves the exact transport identity

```text
κk ∘ₘ (νL.restrict mixedSlice0) = κ0 ∘ₘ (νL.restrict mixedSlicek).
```

It then proves `FirstBlockKernelShiftStatement` by `firstBlockKernelShift`:
if the zero kernel composed with the outer slice k equals the total slice k
for every integer k, the k-th kernel composed with the fixed outer zero slice
equals the total slice k. The normalized zero-kernel disintegration premise
remains outside this unit. This conditional result does not establish the
complete first-block integration theorem.

## Objects and hypotheses

The statement quantifies over every canonical p-adic field `F` in universe `uF`
and every positive two-block shape, with first and second sizes `a = m 0 + 1`
and `b = m 1 + 1`. Write `G = GL_(a+b)`, `H = diag(N_a,N_b)` and
`L = diag(GL_a^0,N_b)` for the published groups. The small, total and mixed
quotients are the actual left quotients `N_a \ GL_a`, `H \ G` and `L \ G`,
with their canonical quotient topologies and Borel measurable structures.
The integer slices use the published normalized determinant order.

The small measure `νA` is s-finite and compatible with the specified first-block
ambient Haar and unipotent Haar measures. The explicit `hInvariant` hypothesis
is its published norm-one right-invariance property, used to form
`fiberKernel F h νA hInvariant k`. No kernel-existence assumption is added:
this is the actual quotient-descended kernel constructed in
`TwoBlockFirstBlockFiberKernel`, with its everywhere representative formula.

The mixed measure `νL` is compatible with the specified ambient Haar on `G`
and `mixedHaar F h`. The latter is the transport of the product of
restriction-normalized norm-one Haar and the second-block unipotent Haar.
The target measure `νH` may be any measure on `H \ G`. The conditional premise
is equality of the zero-kernel composition with each restricted `νH` slice.
No s-finiteness or compatibility hypothesis on `νH` is needed for this transport
step. There are no representation, character, convergence, or kernel
s-finiteness hypotheses in this helper.

## Implemented proof

`map_restrict_smallSlice_of_ord` uses compatible-measure right invariance.
For `z : GL_a` with `ord(det z) = k`, the preimage of small slice k under
right translation by z is exactly slice zero. Restrict the measure-preserving
translation homeomorphism and take its pushforward. The resulting equality is
exact and contains no scalar.

`exists_determinantOrder` realizes every integer k by a nonzero field element
using the published surjectivity of normalized order. It then uses Mathlib's
surjectivity of the determinant on the positive-rank general linear group.

`fiberPoint_firstBlockEmbedding_mul` proves, by induction on the actual small
quotient and multiplicativity of the first-block embedding, the identity

```text
fiberPoint q (diag(z,1) g) = fiberPoint (q · z) g.
```

`fiberKernel_eq_zero_shift` applies quotient induction on the mixed base point,
the everywhere representative formulas for the kernel and `mixedLeftShift`,
and composition of measurable pushforwards. The small-slice pushforward above
then gives equality of measures at every base point:

```text
κk q = κ0 (mixedLeftShift z q).
```

`fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice` chooses such a z for k.
The separately proved exact pushforward of mixed slice zero to mixed slice k
converts the zero-kernel composition over the k-th outer slice into an integral
over the zero slice. Evaluation on an arbitrary measurable set, the kernel
composition formula, and measurable change of variables identify it with the
k-th kernel composition. Kernel evaluation is measurable; neither kernel nor
base measure s-finiteness is used in this change of variables.

Finally, `fiberKernel_comp_zeroSlice_eq` combines that transport with the
supplied zero-kernel slice identity. The closed Prop-valued statement
`FirstBlockKernelShiftStatement` packages exactly this conditional conclusion;
`firstBlockKernelShift` proves it using that lemma. All transport steps retain
the restriction normalization, so no k-dependent factor or density appears.

## Provenance and limits

The motivating original is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions* (1983), registered source
`jpss-1983-rankin-selberg`, Section 4.6, printed page 412, displays (5) and (6).
The retained PDF SHA-256 is
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page 412 is zero-based PDF index 46 / one-based page 47, visually checked
in the earlier source audit; no source erratum note was found there.

JPSS equation (6) has the fixed zero outer determinant slice, inner slice k,
and the fiber point `[diag(u,1)g]_H`, with no displayed scalar. It does not
separately state these kernel-transport constructions. Their provenance is
internal: they combine the existing actual groups, slice formulas, compatible
quotient right invariance, normalized mixed shift and measurable fiber kernel
with elementary measure pushforward and integration identities.

This unit does not prove the normalized zero-kernel quotient-measure tower,
its restriction to equal determinant slices, kernel s-finiteness, or the
Tonelli and Bochner consequences of the complete target. Its final equality
is conditional on the zero-kernel slice identities described above.
