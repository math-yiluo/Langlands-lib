# Compactly supported distributions act on smooth representations

This module proves `Langlands.compactDistributionAction`, whose type is exactly
`Langlands.CompactDistributionActionStatement.{u, v}`, Renard III.1.3, printed
p.59 / PDF p.65. The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, French edition of
9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 284 read PDF pp.37–38 and 65 for this proof.

The internal vector-pairing construction uses the published finite decomposition
of a vector-valued compact test into scalar indicators times vectors. A
distribution evaluates the indicators, producing a finite linear combination
of those vectors. Applying any algebraic linear form gives exactly the
distribution applied to the scalar-valued test. Restricting a locally constant
vector map to the compact topological support of a distribution therefore
defines its pairing with that distribution. This follows the support
restriction and vector-test constructions in II.1.2.

Smoothness makes each orbit map locally constant, by the published
discrete-orbit characterization. The action value is chosen from the preceding
vector-pairing existence theorem. Algebraic linear forms separate vectors,
via `Module.eval_apply_injective`, so the scalar characterization forces
additivity and complex homogeneity in both the vector and the distribution.
These laws package the chosen values into
`CompactDistributionAction.act`, a complex-linear map from compactly supported
distributions to endomorphisms.

For multiplicativity, `Distribution.compactSupportPairing_convolution`
expresses the scalar pairing with `T ∗ S` as iterated evaluation on the
coefficient `(x, y) ↦ ℓ(ρ(xy)a)`. The representation law identifies this with
`ℓ(ρ(x)(ρ(y)a))`. Applying the characterization for `S` to the linear form
`ℓ ∘ ρ(x)`, and then the characterization for `T`, yields the composition
of the two action operators. Dual separation gives the operator equality.
For point masses, `Distribution.compactSupportPairing_dirac` evaluates each
coefficient at its point, and dual separation again yields the original
group operator.

The final theorem assembles the linear action, its characterization, and
these two laws. The helper constructions and lemmas in the namespace
`Langlands.CompactDistributionAction` are internal derived content implementing
the vector pairing and action described by Renard; they assume no additional
mathematical inputs. The group and vector-space universes remain independent.
No topology, dimension, countability, or completeness assumption is imposed
on the vector space. The statement module, its paired Markdown, and everything
it imports remain unchanged.
