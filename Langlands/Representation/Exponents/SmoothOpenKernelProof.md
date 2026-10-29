# Open kernels of generalized characters of smooth representations

Author: Worker 19.

`Langlands.smoothGeneralizedEigencharacterOpenKernel` proves
`SmoothGeneralizedEigencharacterOpenKernelStatement.{uR,uG,uV}` from
[`SmoothOpenKernelStatement`](SmoothOpenKernelStatement.md).
The helper `isOpen_ker_of_isGeneralizedEigencharacter` exposes its direct
application. Both retain independent field, group and carrier universes, an
arbitrary topological group and an arbitrary smooth representation over a
field. The group need not be commutative, and no topology on the field or
carrier or admissibility, irreducibility or dimension premise is used.

The proof extracts a nonzero vector `v` and one uniform natural power `r`
from `isGeneralizedEigencharacter_iff`. Smoothness supplies an open subgroup
`K` fixing `v`. For `g ∈ K`, linearity gives
`(π(g) - χ(g)) v = (1 - χ(g)) • v`. Induction computes the `m`-th defect
power on `v` as `(1 - χ(g))^m • v`. Its vanishing at `m = r` forces that
scalar power to be zero because `v` is nonzero. If `χ(g) ≠ 1`, the field's
power-nonvanishing theorem contradicts this equality. This also deals with
`r = 0`, which cannot have a nonzero generalized witness. Hence every element
of `K` lies in the character kernel. `Subgroup.isOpen_mono` proves the kernel
open. The exact closed theorem introduces its binders and applies the helper.

This is an internal argument from the published algebraic occurrence and
smoothness definitions. It generalizes the complex-coefficient result in
`ProductLeviSquareIntegrableSufficiencyProof` to an arbitrary field. The
proof here is Worker 19's direct generalized-vector argument; it uses
neither a square-integrability criterion nor an exponent-smoothness premise.
Consumers of normalized refined Jacquet modules can already use the published
complex corollary
`ProductLeviSquareIntegrable.isOpen_ker_of_isGeneralizedEigencharacter_refined`;
this module adds only the generic arbitrary-field theorem and helper.

This module's own import closure has 31 project modules, all with nonempty
Markdown pairs. Apart from this new proof and its published statement, they
are unchanged previously audited files and match the current Library at
`61f87bbe6fe6e5ffe1387e9640956e5d8d8c9fc5`. The target and every pair it
imports are unchanged. No classification, analytic criterion, weakly-critical
support, refinement/minimality, tempered unitarity/genericity, equal-exponent
grouping or exhaustion proof occurs in this closure. Thus it preserves the
independence constraints of the strict GL and product-Levi consumers,
including exclusion of tasks `3a43d7be-3215-46cc-a077-dfb4ed8542d7` and
`535b7e03-2a69-4128-a6c8-7a269cb6c783` and all forbidden proof successors
and transitive dependencies.
