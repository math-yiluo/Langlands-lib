# Compact opposite-character mirabolic test functions

Author: Worker 481. Construction specification and prospective proof route: Worker 408.

`Langlands.Whittaker.MirabolicUnitTestStatement.{uF} F T n` is an unproved
proposition definition. It specifies the compact mirabolic functions used
before the Kirillov lift in the equal-rank JPSS unit-test argument.

## Parameters and actual groups

The declaration has implicit parameters `p : ℕ` and `[Fact p.Prime]` and
explicit parameters `F : PadicField.{uF} p`, `T : F.TopologicalData` and
`n : ℕ`. It installs `T.topology`, `T.valuativeRel` and `T.localField`.
It then quantifies over every
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, with continuity
interpreted using the supplied topology.

Its local bindings are the published actual matrix group
`G = GeneralLinear (n + 1) F.Carrier`, its subgroup
`P = GeneralLinear.mirabolic n F.Carrier`, the actual subgroup
`N = GeneralLinear.upperUnipotent (n + 1) F.Carrier`, and
`χ = Whittaker.standardCharacter ψ n`. Thus `P` fixes the last row
`(0, …, 0, 1)`, and
`(χ u : ℂ) = ψ.complex (∑ i : Fin n, u.val i.castSucc i.succ)`.
No alternative matrix groups, characters or test-function predicates are defined.
Every `n` is included; for `n = 0`, both `P` and `N` are trivial.

## Existence target

For each character, the proposition asks for
`P₀ : OpenSubgroup P`, `φ : RankinSelberg.WhittakerFunctions ψ n`,
`φ' : RankinSelberg.InverseWhittakerFunctions ψ n` and
`J₀ : OpenSubgroup G`. The two function types already enforce global left
covariance by `χ` and its inverse, respectively; they do not require global
local constancy or membership in a representation's coefficient model.

Write `C` for the image of `P₀` under `P → G`, and
`S = {g | ∃ u : N, ∃ k : P₀, g = u.val * k.val.val}`.
The conjunction requires:

- `P₀` is compact in `P`, and `J₀` is compact in `G`.
- Every `k : P₀` has `T.determinantNorm (n + 1) k.val.val = 1`.
  This is the published residue-normalized determinant character, with
  equality in `ℝ≥0ˣ`.
- If `j ∈ J₀` and `j ∈ P`, then `j ∈ C`.
- On each product `u k`, the two functions have values `(χ u : ℂ)` and
  `(χ u : ℂ)⁻¹`.
- Outside `S`, both functions vanish.
- Both functions are right invariant under every `k : P₀`, at every `g : G`.

Because character values are units, the prescribed values never vanish.
Consequently the actual nonzero support of each function is exactly `S`.
Every nonzero point is a product `u c` with `c ∈ C`, and `C` is compact as
the continuous image of the compact subset `P₀` of `P`. This supplies a common
compact representative set for support modulo `N`. These are direct
consequences of the stated clauses, not additional Lean theorems in this module.

Right `P₀` invariance gives smoothness on `P`. The ambient subgroup clause
also gives right invariance on `P` under `J₀ ∩ P`, exactly the ambient-subgroup
formulation used in the shared mirabolic test-function interface. The
proposition allows zero extension outside `P`; it imposes no ambient
smoothness. No test-vector lift, measure, quotient mass or unit-integral
identity is supplied or assumed.

## Source and internal construction

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, source ID `jpss-1983-rankin-selberg`.
The retained file is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385–386 and 393 (one-based PDF pages 20–21 and 28) were read
visually. No JPSS errata file was found in the current Library or literature
filename search; the expected project and workspace `notes/errata`
directories were absent.

JPSS §2.1, p.385, gives the Whittaker covariance condition and explains
passage to the inverse character. Page 386 defines the coefficient functions
`W(g) = λ(π(g)v)` and, in §2.2, the smooth covariant functions on the
mirabolic group with compact support modulo `N`. Its inclusion of that space
in the restrictions of coefficient functions is a separate Kirillov assertion.
On p.393, the equal-rank argument chooses opposite-character mirabolic
functions, lifts them to coefficient functions, chooses a common right
stabilizer and a last-row characteristic function, and reduces the integral
to a positive scalar times an integral of their product on `N \ P`.

The exact compact-open data specified here are an internal construction
target supporting that argument, rather than a separately stated JPSS
theorem. A prospective proof first uses the open kernel of the continuous
standard character on `N`. A sufficiently small compact open subgroup `P₀`
of `P` has intersection with `N` in that kernel and lies in the
determinant-norm-one locus. Prescribing the two character values on `N P₀`
is then independent of the chosen product decomposition. Extending by zero
gives the two equivariant functions and their common right stabilizer.
A compact open ambient subgroup `J₀` can be chosen with
`J₀ ∩ P` contained in `P₀`, since `P₀` is a neighborhood in the subspace
topology. This paragraph describes a route for the future proof; no proof
is implemented here.

## Published dependencies and scope

The imports preserve the published pairs for `Group.GL.Mirabolic`,
`Group.GL.CompactOpen`, `Group.GL.NormalizedCharacter`,
`Whittaker.GeneralLinear` and `RankinSelberg.QuotientIntegrals`.
They supply the actual subgroups, compact-open neighborhood machinery,
normalized determinant character, standard character and equivariant
function subtypes.

For a future proof, `Representation.Twist.ContinuousCharacterProof` proves
`Langlands.isOpen_ker_of_continuous_complex_character`;
`Whittaker.standardCharacterContinuous` and the supplied-topology
nonarchimedean certificate let it apply here.
`HarmonicAnalysis.Conductor` also supplies additive-character triviality
on a valuation lattice. This module does not import an unpublished helper
or define the separate shared `IsMirabolicTestFunction` predicate.
