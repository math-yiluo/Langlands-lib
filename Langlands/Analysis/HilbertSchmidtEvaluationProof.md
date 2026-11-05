# Evaluation-family Hilbert–Schmidt criteria

Worker 116 proves the exact proposition
`Langlands.Analysis.OperatorIdeals.HilbertSchmidtEvaluationCriteriaStatement`
by `hilbertSchmidtEvaluationCriteria`. The component theorems
`hilbertSchmidtDominatedEvaluation` and `hilbertSchmidtUniformEvaluation`
prove its two named conjuncts. The complete complex Hilbert space, measurable
space and supplied Hilbert-basis index type have independent universes u, v
and w. There is no separability or countability hypothesis.

For a bounded linear functional l, the private lemma `evaluation_bessel`
uses Mathlib's Riesz isometric equivalence to represent l by a vector z.
Its isometry gives ‖z‖=‖l‖. Symmetry of the inner-product norm then turns the
finite orthonormal Bessel inequality into
∑ᵢ∈s ‖l(bᵢ)‖² ≤ ‖l‖². The private lemma `l2_norm_sq_integral` identifies
the squared norm of an actual L² class with the integral of the squared
norms of its chosen representative. It takes the real part of the L² inner
product integral, using integrability of the inner product of two L²
classes.

The private lemma `evaluation_basis_bound` applies these facts to an
arbitrary supplied Hilbert basis b and each finite set s of its indices.
The L² condition supplies integrability of every scalar squared norm, so
the finite sum commutes with integration. For this finite set only, the
proof intersects the almost-everywhere representation equalities for
A(bᵢ). Bessel's inequality and the assumed envelope g then bound the
pointwise finite sum almost everywhere, giving
∑ᵢ∈s ‖A(bᵢ)‖² ≤ ∫g. Nonnegativity of the summands and the uniform bound
on finite subsums yield summability over the full arbitrary index type
and the asserted bound on its total sum. No jointly measurable kernel,
dual-valued measurability or common null set for the full basis is used.

`hilbertSchmidtDominatedEvaluation` applies this bound to a Hilbert basis
whose index type is a subset of the domain, witnessing the existing
`IsHilbertSchmidt` predicate, and also returns the bound for every supplied
basis. `hilbertSchmidtUniformEvaluation` squares the norm bound and applies
the dominated theorem with the constant function C². Finiteness of the
measure makes that constant integrable, and its integral is C² μ(X), with
μ(X) converted to a real number. The statement's nonnegativity premise on
C is retained; the actual squaring step already uses the nonnegative norm
on its left.

This is an internal derivation motivated by the evaluation step of
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma
9.3.3, printed pp.247–248 (one-based PDF pp.259–260), registered source
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete author errata `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no correction to that lemma. The argument here uses finite Bessel
sums in place of the source's two-variable kernel argument and proves
the more general operator criteria described by the target Markdown.
It constructs no automorphic evaluation family and proves no trace-class
or spectral conclusion.
