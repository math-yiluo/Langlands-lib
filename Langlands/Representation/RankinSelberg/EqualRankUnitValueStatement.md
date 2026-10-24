# An actual equal-rank JPSS integral with rational value one

Author: Worker 358.

`Langlands.RankinSelberg.EqualRankUnitValueStatement.{uF,uV,uW} F T n`
is a proposition definition. It states the concrete rational-value consequence
of the equal-rank test-vector construction in Jacquet--Piatetski-Shapiro--Shalika
(JPSS), *Rankin--Selberg Convolutions* (1983), printed page 393. This module
does not prove the proposition.

## Exact scope and conclusion

The telescope is copied from the published `EqualRankAnalyticStatement F T n`;
only its final conclusion changes. The prime `p` and `Fact p.Prime` are implicit
parameters. The explicit parameters are `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData`, and `n : ℕ`. The rank is `n + 1`, including rank one.
Inside the proposition, the topology, valuative relation and local-field
structure come from `T`. The general linear group, upper-unipotent subgroup
and left-unipotent quotient receive exactly the same Borel structures as in
the analytic statement.

The proposition quantifies every `UnitaryAdditiveCharacter F.Carrier`. This
bundle includes continuity and nontriviality and takes values in the unit
circle. It then quantifies right invariance of `unipotentHaar F.Carrier n`,
every quotient measure `μ`, and the hypothesis `IsCompatible` for `μ` with
`generalLinearHaar F.Carrier n` and `unipotentHaar F.Carrier n`. These ambient
and unipotent Haar measures give their respective integral compact subgroups
mass one. The compatibility predicate is the existing quotient integration
formula; no new measure convention is introduced.

The representation carriers `V : Type uV` and `W : Type uW` have independent
universes and their own complex module structures. The representations `π`
and `σ` are of Whittaker type for `standardCharacter ψ n` and
`inverseStandardCharacter ψ n`, respectively. The existing
`IsOfWhittakerType` means admissible, finitely generated over the group algebra,
and with a functional space linearly equivalent to `ℂ`. Admissibility includes
smoothness. This scope includes reducible representations and does not require
finite-dimensional carriers. Finally, every actual functional pair
`ℓ : glFunctionals ψ n π`, `ℓ' : glInverseFunctionals ψ n σ` with
`ℓ.val ≠ 0` and `ℓ'.val ≠ 0` is covered.

The conclusion is exactly

```lean
(1 : RationalFunctions) ∈ equalRankRationalValues T.residueCardinality ψ
  (normalizedAbsoluteValue T) μ π σ ℓ ℓ'
```

Unfolding the existing `equalRankRationalValues`, this means that there exist
`f : (coefficientModel π ℓ).toSubmodule`,
`f' : (coefficientModel σ ℓ').toSubmodule`, and
`Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)` such that
`HasRationalContinuation T.residueCardinality
  (equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ) 1`.
The coefficient models are actual images of coefficient maps: their elements
arise from vectors of the specified representations and specified functionals.
The integral is the existing quotient integral
`∫_{N \ G} f(g) f'(g) Φ(e_{n+1}g) |det g|^s dμ`.

`HasRationalContinuation` requires agreement on a right half-plane, with
nonvanishing denominator there, at the spectral point `q^(-s)`. For the
constant rational function one, the denominator and its evaluation are one.
Thus the source's integral identically equal to one gives precisely the
required continuation. The Lean conclusion only asks for that continuation;
it does not state equality at every complex parameter. It neither asserts
convergence and rationality for all test data nor assumes those results,
Kirillov surjectivity, or existence of a normalized generator.

## Checked source and derived provenance

Registered original: `jpss-1983-rankin-selberg`, H. Jacquet, I. I.
Piatetski-Shapiro and J. A. Shalika, *Rankin--Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367--464.
Retained file:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
SHA256:
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The fingerprint was checked and the following scanned pages were read visually:

- Section 2.1, printed page 385, PDF page 20 (one-based): admissible finite-type
  representations with one-dimensional Whittaker functional space, including
  the discussion of rank one.
- Section 2.2 and display (3), printed page 386, PDF page 21: coefficient
  functions `W(g) = λ(π(g)v)` and the inclusion
  `K₀(ψ) ⊆ K(π; ψ)` for smooth mirabolic functions compactly supported modulo
  the upper-unipotent group.
- Printed page 393, PDF page 28: the equal-rank construction in the proof of
  Theorem 2.7(i)--(ii), from the assertion that the test data can give value
  one through the conclusion of the case `r = t`.

On page 393, JPSS chooses compact mirabolic test functions for the two opposite
characters, lifts them to Whittaker functions using Section 2.2, and chooses
a common sufficiently small right stabilizer `K_m`. The last-row test is the
characteristic function of `η K_m`. The integral reduces to a positive
constant times a compact mirabolic integral with factor `|det p|^(s-1)`.
The mirabolic functions can be chosen so that the remaining integral is
constant in `s` and normalized to one. Concretely, one uses a small compact
open mirabolic neighborhood where the determinant has absolute value one
and where the character is trivial on its unipotent intersection. Opposite
covariant functions on its unipotent saturation have product the indicator
of a compact open quotient neighborhood. Its measure is finite and positive;
rescaling one function absorbs this volume and the positive reduction
constant. This explains the source's normalization step, rather than
deducing the target from an abstract fractional-ideal generator.

There are two scope interfaces that require explicit reasoning beyond copying
the displayed formula.

First, page 393 writes central characters of `π` and `π'`. The target does not
assume scalar central action on either possibly reducible representation.
For a central element `z`, the functional `v ↦ ℓ(π(z)v)` is again equivariant
for the same unipotent character. The one-dimensional functional space makes
it `c(z) ℓ`; invertibility of `π(z)` makes `c(z)` nonzero, and composition
makes `c` multiplicative. Consequently every coefficient function satisfies
`f(zg) = c(z) f(g)`. Smoothness, applied to a vector on which `ℓ` is nonzero,
makes this central character locally constant. The same reasoning applies to
`σ` and `ℓ'`. This provides central characters on the actual coefficient
images, which is all the integral calculation uses. It does not claim that
the original representation has scalar central action. This is derived
provenance explaining the full Whittaker-type scope, not a stronger theorem
quoted verbatim from the source. Likewise, any nonzero chosen functional
spans its functional space, so using it gives the same coefficient image as
the source's choice.

Second, the published `Langlands.WhittakerTypeKirillovStatement` uses
`F.canonicalTopologicalData.topology`, whereas this target uses `T.topology`.
The published theorems `Langlands.PadicField.TopologicalData.topology_eq_canonicalModule`
and `Langlands.PadicField.canonicalTopologicalData_topology` identify both
with `F.canonicalTopology`. A proof must transport continuity, smoothness,
open subgroups and compact support through that equality, and identify the
entrywise characters and functional spaces of the Kirillov target with the
bundled coefficient models here. No equality of the whole topological-data
structures is assumed. The integral retains `T.residueCardinality`,
`normalizedAbsoluteValue T`, and its specified compatible `μ`. The source
does not mention Lean's supplied-data packaging; this transport is an
internal interface justified by the published topology equalities.

Rank one is retained. In that case the mirabolic and upper-unipotent groups
are trivial. Equivalently one can choose vectors with nonzero functional
values, a sufficiently small compact open subgroup of `Fˣ` fixing both
vectors, and a last-row test supported on it. The determinant absolute value
is one on that subgroup, and a scalar rescaling absorbs its positive finite
Haar volume. This is the rank-one specialization of the test construction.

For every compatible quotient measure, the quotient integration formula and
the fixed normalized Haar measures must justify the positive constants used
in the reduction. That measure comparison, the Kirillov inclusion and its
adapters, compact test construction, integration identities, and conversion
of constant value one to `HasRationalContinuation` remain proof obligations.
None is asserted to be implemented by this proposition definition.

## Dependencies and intended use

The sole import is `Langlands.Representation.RankinSelberg.AnalyticStatement`,
which supplies the telescope, actual rational-value set and all required
definitions. No existing Library Lean/Markdown pair is changed.

The shared Kirillov proof prerequisite is task
`22a72323-4330-40af-aa2f-8fe757b10043`. This target isolates the concrete
unit-value input for the equal-rank analytic proof task
`5998b0b2-e367-4e85-8d4d-47e3b9b4a222`; the general convergence and
common-denominator arguments remain separate. It does not replace the
unequal-rank unit-span or normalized-generator algebra targets.

## Lean validation

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the module with zero errors and zero warnings and inspected the exact
proposition declaration successfully (`statement_returns_prop: true`). The
reported universe parameters are `uF`, `uV`, `uW`; its only reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`. This development check does
not establish a proof of the proposition or independent semantic acceptance.
