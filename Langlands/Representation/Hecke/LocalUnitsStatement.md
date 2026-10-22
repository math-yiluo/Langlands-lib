# Finite-family compact-open local units: statement

`Langlands.Hecke.HeckeAlgebra.FiniteFamilyLocalUnitsStatement.{u}` is a
proposition about the published actual convolution algebra. It quantifies over
an arbitrary-universe Hausdorff locally compact totally disconnected topological
group `G`, a measurable structure with `BorelSpace G`, a genuine left Haar measure
`μ`, a finite set `s` of elements of `HeckeAlgebra μ`, and an open subgroup `U`.

The conclusion supplies one open subgroup `K`, a proof of compactness of its
underlying set, and `K ≤ U`. Its actual normalized indicator
`e_K = (μ.real K : ℂ)⁻¹ • 1_K` is a convolution idempotent and satisfies
`e_K * f = f` and `f * e_K = f` for every `f ∈ s`. The finite family may be
empty; that case still asserts the existence of a compact open subgroup inside
`U` and the idempotence of its indicator. Choosing the top open subgroup removes
the refinement constraint. All products are the published left-Haar convolution
`(f * g)(x) = ∫ y, f(y) * g(y⁻¹*x) ∂μ`, with the measure recorded in the carrier.

This is an internal formulation combining the published common compact-open
bi-invariance proposition and its proof with the published normalized-indicator
averaging and idempotence results. Its provenance is those existing Library
constructions: `Langlands.Representation.Hecke.CommonInvarianceStatement`,
`CommonInvarianceProof`, and `NormalizedIndicator`. The new statement does not
assume a compact-open basis or any invariance of the finite family, and it adds
no countability, global sigma-finiteness, unimodularity, subgroup normality, or
`NonarchimedeanGroup` hypothesis. Positivity and finiteness of the compact-open
Haar mass are already proved in `NormalizedIndicator`.

The intended implication uses common bi-invariance to obtain `K`, then applies
the left and right averaging unit identities to each function and the existing
indicator idempotence theorem. This module defines only the target proposition;
it does not contain or claim a proof. The finite-family formulation is internal
rather than a quotation of a separate original-source theorem. It concerns
convolution local units; representation actions and corner algebra structures
are separate modules.

Worker 86 authored this statement and explanation.
