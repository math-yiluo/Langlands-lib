# Full-distribution Hecke actions in Renard II.3.13

This statement unit concerns every Hausdorff locally compact totally
disconnected group, at arbitrary universe `uG`, and every Borel left Haar
measure `μ`. There is no countability, unimodularity or measure-valued
restriction on the full algebraic distributions.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.13 first Definition, Remark and (II.3.13.1), printed p.53 /
PDF p.59; second Definition and the following paragraph, printed p.54 /
PDF p.60; displayed inclusion chain, printed p.55 / PDF p.61.

The unit reuses `Distribution.heckeDistribution`, the two full-dual Hecke
actions, the three essentially compact submodules, the original topological
compact-support submodule, and the compact-distribution convolution.
`Hecke.HeckeAlgebra μ` remains the existing function model for `H(G)`.

`KernelStatement` identifies the defining transposes with the literal kernels
`x ↦ ∫ h(y)f(xy) dμ(y)` and `x ↦ ∫ h(y)f(yx) dμ(y)`.
It asserts integrability and existence of genuine test functions with these
values, and fixes both actions by evaluation on every distribution.
These kernels expand the first Definition's pairings with the inverted
distribution. The published left action uses `μ.inv` in its test convolution;
the statement retains the corresponding kernel for general nonunimodular
groups.

`CompactCompatibilityStatement` gives a compact subtype witness for the
actual Hecke density and identifies both full-dual actions with the existing
compact convolution. It is the first assertion in the Remark.

`InversionStatement` is the Remark's reversal identity and its left-hand
counterpart. Its Hecke witness is constrained to the actual inverted
distribution. Thus it does not omit the modular factor by confusing inversion
of distributions with bare inversion of functions.
`AssociativityStatement` states the right associativity exercise, together
with the left and mixed counterparts obtained from the same kernels.
Those extra counterparts are internal consequences, not additional numbered
assertions in the source.

`EvaluationStatement` is precisely (II.3.13.1): `h * check(f)` is represented by
the published left-Haar test convolution, and `T * (h * check(f))` by the
published scalar distribution/test convolution, evaluated at `1`.

`InclusionsStatement` spells out `H(G) ⊆ E′(G) ⊆ D′(G)ec ⊆ D′(G)rec`
and the left analogue of the last inclusion on the actual submodules.
`RangePreservationStatement` asserts that the products in the second
Definition actually lie in the Hecke density range, beyond their defining
compactness.

`Statements` is the conjunction of these seven closed Prop-valued targets.
No proofs or algebra instances are supplied here. The products of two
essentially compact distributions and the completion and categorical-center
comparisons are separate obligations.
