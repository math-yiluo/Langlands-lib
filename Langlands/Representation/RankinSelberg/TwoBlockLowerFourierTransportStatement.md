# Lower quotient duality and Fourier coefficient transport

The paired Lean file defines the closed proposition
`Langlands.RankinSelberg.TwoBlockLowerFourierTransportStatement.{uF,uW}`.
It states the lower quotient change of variables and conditional Fourier
comparison used in JPSS Section 4.8. It does not prove this proposition.

## Source and derived packaging

The original source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The source passages are Section 4.7(1) and its subgroup and row definitions
on printed pp.412–414, and Section 4.8(2)–(4) on printed p.415
(one-based PDF pp.47–50). These pages were visually read from the scanned
original. No applicable registered erratum was located.

The assignment's reference to “Section 4.7 equations (1) and (8)” contains
a locator error: Section 4.7 has equations (1)–(5). The relevant equation
(8) for the separate first-block integration is in Section 4.9, printed
p.418. This statement uses Section 4.7(1) and its lower-subgroup,
block-rotation, first-row and last-row conventions, followed by Section
4.8(2)–(4). This correction changes no mathematical requirement here.

Section 4.8(2) reverses the two blocks and replaces the additive character
by its inverse. Equation (3) compares the partial Fourier transforms with
the determinant factor. Equation (4) changes the variable by
`Tdual(g) = w_N * inverseTranspose(g)`. The uniform homeomorphism,
canonical Borel quotient measures, determinant-slice restrictions, and
Bochner-integrability equivalence are derived formal packaging of this
change of variables, rather than a literal proposition quoted from JPSS.
The exact conditional scalar premise below isolates the actual section
comparison from this transport statement.

## Geometric and measure quantifiers

The statement ranges over every prime `p`, every `PadicField.{uF} p`,
every `t`, and every two-block family `m` with
`∑ i, (m i + 1) = t + 1`. Thus both blocks are positive and either may
have size one. It installs the field's canonical topology and Borel
structure, and the Borel structures of the induced group, subgroup and
quotient topologies.

Write `mD i = m i.rev` and `hD = reverse_sum h`. There is one
homeomorphism

```text
D : LowerQuotient h F.Carrier ≃ₜ LowerQuotient hD F.Carrier
```

chosen before all characters, measures, representations, functionals,
sections and Schwartz functions. Both `D` and `D.symm` send a
representative `[g]` to `[Tdual(g)]`. Both negate the published lower
`determinantOrder`. For every integer `k`, the statement gives the image
and preimage correspondence between `determinantSlice F h k` and
`determinantSlice F hD (-k)` in both directions. It also states explicitly
that conjugating `D` by the two actual `lowerToStandard` equivalences
gives `[g] ↦ [Tdual(g)]` on the standard quotient.

The group and subgroup measures are exactly `generalLinearHaar F.Carrier t`
and `unipotentHaar F.Carrier t`. For every supplied right-invariance
certificate for the latter, installed locally, and every
`nuN : Measure (LeftUnipotentQuotient t F.Carrier)` satisfying
`QuotientIntegration.IsCompatible` for those measures, put

```text
nuMinus  = Measure.map (lowerToStandard h  F.Carrier).symm nuN
nuMinusD = Measure.map (lowerToStandard hD F.Carrier).symm nuN.
```

The same `D` preserves these measures in both directions. It sends the
restriction of `nuMinus` to slice `k` exactly to the restriction of
`nuMinusD` to slice `-k`, with the exact inverse map law as well.
Measure preservation is asserted as a conclusion. The statement neither
chooses a new quotient normalization nor assumes invariance under
`Tdual`. Existence of a compatible standard quotient measure is a
separate result and is not asserted or required as an input here.

## Actual Fourier and section comparison

For every unitary additive character `psi` and every actual
`Wtest : WhittakerFunctions psi t`, the statement provides one
`Wdual : WhittakerFunctions (psi.scale (-1)) t`, before the additive
measure or any subsequent analytic data. It has the exact pointwise law
`Wdual.val g = Wtest.val (Tdual(g))`. Membership in this function space
supplies its inverse-character covariance. The statement also records the
actual block-rotation cancellation

```text
Wdual.val (blockRotation hD F.Carrier * Tdual(g))
  = Wtest.val (blockRotation h F.Carrier * g).
```

For every supplied additive Haar measure `nu` satisfying `IsSelfDual psi nu`
and every `IsRowFourierPair psi nu Phi Phihat`, it asserts

```text
partialSection hD (psi.scale (-1)) nu Phihat (Tdual(g))
  = (T.normalizedAbs (determinant g) : ℂ) *
      partialSection h psi nu Phi g.
```

The imported published theorem
`Langlands.HarmonicAnalysis.twoBlockRowFourierCompanion` is the pure
Fourier result to specialize at the actual first and last unit rows.
It is not a new proof prerequisite. The specialization retains the
supplied self-dual measure and every Fourier pair.

The universes of the field and block carriers are independent. For every
dependent family `W : Fin 2 → Type uW` of complex modules, every actual
block representation `sigma`, and every supplied inverse-character
functional family `ell`, including zero functionals, set

```text
WD i     = W i.rev
sigmaD i = Whittaker.inverseTransposePullback (sigma i.rev)
ellD i   = RankinSelberg.secondDualFunctional psi (sigma i.rev) (ell i.rev).
```

For every actual `f : TwoBlockJacquet.Sections F h sigma` and
`fD : TwoBlockJacquet.Sections F hD sigmaD`, the sole additional
assembly premise is

```text
∀ g,
  TwoBlockJacquet.scalarSection (fun i => (ellD i).val) fD (Tdual(g)) 1
    = TwoBlockJacquet.scalarSection (fun i => (ell i).val) f g 1.
```

This premise is conditional data for transport. Its construction and
proof belong to the separate actual dual-section/Jacquet comparison.
No smoothness, full Whittaker-type, irreducibility, nonzero-functional,
coefficient-image or convergence hypothesis is imposed here.

Let `E` and `ED` be exactly the published descended
`TwoBlockLowerUnfolding.integrand` for the supplied original and reversed
data. The statement asserts the corresponding actual `groupIntegrand`
identity at `Tdual(g)` with factor `|det g|`, and

```text
ED (D z) = ((q : ℝ) ^ (-determinantOrder F h z) : ℂ) * E z,
```

where `q = T.residueCardinality`. These are actual integrands, using the
published lower block rotations and partial Fourier values.

## Slice coefficients and scope

For every right-invariance certificate, every compatible standard
quotient measure, and every `k : ℤ`, the conditional comparison gives

```text
Integrable ED (nuMinusD.restrict (determinantSlice F hD (-k))) ↔
  Integrable E (nuMinus.restrict (determinantSlice F h k)).
```

It also gives the complex total Bochner integral identity with scalar
`(q : ℂ)^(-k)` and the real norm-integral identity with scalar
`(q : ℝ)^(-k)` on these two slices. These equalities have no integrability
premise: total Bochner integrals and measure-preserving equivalences allow
the equality also in the nonintegrable case. The separate equivalence
records precisely convergence transport, without asserting convergence
for arbitrary inputs. Reindexing gives `ZD(k) = q^k Z(-k)`, the
coefficient action of `X ↦ q^-1 X^-1`.

The proposition does not construct a section equivalence, identify
coefficient models, prove a first-block Laurent identity or Section 4.10,
construct local factors, or prove dominant-rank multiplicativity.
The proof successor must establish the uniform quotient transport and
rotation cancellation, specialize the existing pure Fourier theorem,
and assemble the conditional actual integrand and coefficient laws.
