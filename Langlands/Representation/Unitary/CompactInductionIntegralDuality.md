# Integral duality for compact induction

Author: Worker 142.

This derived internal helper supports Renard 2026, IV.2.1, (IV.2.1.1)–(IV.2.1.2),
printed p.97 / PDF p.103, and the unchanged published target
`Langlands.Renard.CompactRepresentation.CompactQuotientNormalizedInductionDualityStatement`.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Let `G` be a locally compact nonarchimedean group and `P` a subgroup with compact
left quotient `P\G`. For any complex coefficient representation,
`compactQuotientInductionEquiv` identifies compact induction with smooth
induction. The maps preserve the underlying functions and right-translation
actions. The inverse equips a smooth function with compact quotient support,
using the published closedness of that support and compactness of the quotient.

`exists_compactIntegralDualEquiv` additionally assumes that `P` is closed and the
coefficient representation `σ` is smooth. Its supplied character `χ : P →* ℂˣ`
has open kernel and satisfies `χ(q) * χ(q) = δ(q)` after complex embedding, for a
supplied function `δ : P → ℝ≥0`. A supplied subgroup `K` has a measurable space
and a measure `μ` positive on every open neighborhood of its identity. The
hypothesis `hscalar` requires that, for every locally constant complex function
`φ` on `G` satisfying `φ(q*x) = δ(q)*φ(x)`, every function `k ↦ φ(k*g)` is
`μ`-integrable and its integral equals that for `g = 1`, for every `g : G`.
There is no admissibility assumption, and the group and coefficient-carrier
universes are independent.

With these inputs, the theorem constructs an equivariant linear equivalence
from the smooth dual of compact induction of `χ ⊗ σ` to compact induction of
`χ ⊗ σ̃`. It characterizes the equivalence by integrating the coefficient pairing
over `K` with respect to `μ`. The implementation specializes the published
`exists_integralDualEquiv_of_section` at the identity coefficient homomorphism
and identity section, obtaining an equivalence `F` for smooth induction. If `c`
and `d` are the compact-to-smooth comparisons for the two coefficient
representations, the transported map is
`(smoothContragredientEquiv c.symm).trans F |>.trans d.symm`.
The pairing formula follows from that for `F`, because both comparisons preserve
values.

This conditional transfer retains the character, nonnegative function and
analytic data as explicit inputs. It neither identifies `δ` with the relative
modular character nor constructs its positive half character or the measure.
The naturality and hermitian duality clauses of the full target remain separate
obligations. The source motivates this helper; the particular comparison and
transport are internal packaging of published Lean results.
