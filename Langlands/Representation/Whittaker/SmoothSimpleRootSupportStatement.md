# Uniform simple-root support for smooth Whittaker coefficients

Authors: Worker 358 and Worker 456. The proposition body comes from Worker
358's shared draft for the unequal-rank compact-support project. Worker 456
checked its scope and source provenance and prepared this statement pair.

`Langlands.Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T r`
is a `Prop` definition. This module states the support estimate; it supplies
no theorem proving that proposition.

For every prime `p`, p-adic field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, and natural number `r`, the proposition quantifies
over a `UnitaryAdditiveCharacter F.Carrier`, an arbitrary complex module
`V : Type uV`, a smooth representation `π` of the actual group
`GeneralLinear (r + 1) F.Carrier`, an actual standard Whittaker functional
`ℓ : glFunctionals ψ r π`, and an element `f` of its actual coefficient-image
model. It asks for a real number `R > 0` such that

```text
f(diagonalUnits a * κ) ≠ 0  ⇒
  T.normalizedAbs(a[i] / a[i+1]) ≤ R
```

for every diagonal tuple of field units `a`, every integral factor `κ`, and
every `i : Fin r`. The indices in Lean are `i.castSucc` and `i.succ`, so
these are exactly the adjacent simple-root coordinates. The integral factor
belongs to `Conductor.integralSubgroup
(ValuativeRel.valuation F.Carrier).integer r`, the image of the actual
integral general linear group inside the field group.

The bound is chosen after `ψ`, `V`, its module structures, `π`, its smoothness
hypothesis, `ℓ`, and `f`, but before `a`, `κ`, and `i`. Thus one bound works
for all integral factors and all simple roots of this coefficient. It is
not asserted to be uniform over all coefficients or representations.
`T.normalizedAbs` is the Library's residue-cardinality normalization
`q^(-ord x)` for nonzero `x`; the ratios here are nonzero because the entries
of `a` are units.

All topological and valuation instances inside the proposition come from the
supplied `T`. No topology is chosen. The universes `uF` and `uV` are
independent: the representation carrier need not live in the field's
universe. There is no topology on `V` and no continuity assumption on `ℓ`.
`UnitaryAdditiveCharacter` already contains continuity, values in the unit
circle, and `nontrivial : toAddChar ≠ 1`; an additional nontriviality premise
would duplicate its data.

There is no irreducibility, admissibility, finite generation, unitary central
character, or torus-expansion premise. Zero functionals and zero coefficients
are included: their nonvanishing premise cannot hold, so any positive bound
works. The zero representation space is also allowed. When `r = 0`, the
group is `GL₁`, the simple-root index type is empty, and `R = 1` satisfies the
support requirement. No positive-root hypothesis excludes this case.

The provenance is an internal strengthening of the support ingredient used
by Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), §2.5 pp.388–389 and Lemma 2.6
pp.389–390. The registered original is `jpss-1983-rankin-selberg`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Those three printed pages were read visually for this contribution. No
source-specific `notes/errata/jpss-1983-rankin-selberg.md` was found in the
checked project notes or supplied Library snapshot on 25 October 2026.

JPSS §2.5 discusses gauges and finite torus expansions; its single-gauge
majorization has a unitary-central-character hypothesis, and the displayed
expansion is in the generic setting. Lemma 2.6 uses bounded adjacent
diagonal ratios, arising from the compact support in a gauge's root
variables, in its geometric argument for compact matrix support. JPSS does
not state this module's full smooth-representation proposition in those
terms. The stronger scope here is motivated by the following elementary
argument, checked independently of those stronger source results.

1. Since the coefficient model is an image, choose a vector `v` with
   `f(g) = ℓ(π(g)v)`. Smoothness makes the orbit map `g ↦ π(g)v` locally
   constant. The actual integral subgroup is compact, so
   `{π(κ)v : κ integral}` is finite. This uses finiteness of the orbit as a
   set, without a finite-dimensionality assumption on `V`.
2. Each vector of this finite orbit is smooth. Intersect finitely many
   open stabilizing subgroups. For each simple root, the continuous map
   `t ↦ u_i(t) = I + t E_(i,i+1)` takes zero to the identity, so a small
   enough fractional ideal maps into that common stabilizer. Because
   there are finitely many roots, choose one nonnegative integer `m` such
   that all `u_i(t)` with `t ∈ ϖ^m O` fix every orbit vector.
3. Put `c = a[i] / a[i+1]` and `w = π(κ)v`. Actual matrix conjugation gives
   `diagonalUnits a * u_i(t) = u_i(c*t) * diagonalUnits a`. The stabilizer
   condition and Whittaker equivariance therefore give
   `f(diagonalUnits a * κ) = ψ(c*t) f(diagonalUnits a * κ)`.
   At a nonzero value, cancellation forces `ψ(c*t) = 1` for every
   `t ∈ ϖ^m O`.
4. The character's additive conductor `nψ` is the largest integer `n` for
   which it is trivial on `ϖ^(-n) O`. Its existence follows from continuity
   and nontriviality, as implemented in
   `Langlands.HarmonicAnalysis.Conductor`. Triviality on
   `c ϖ^m O = ϖ^(ord(c)+m) O` implies
   `-ord(c)-m ≤ nψ`. Thus `q^(-ord(c)) ≤ q^(nψ+m)`.
   The positive number `q^(nψ+m)` supplies one bound for every integral
   factor and root. For the empty-root case one simply chooses `R = 1`.

The relevant existing APIs include `Whittaker.modelMap_surjective`,
`Hecke.orbitMap_locallyConstant`, `Conductor.isCompact_levelOpenSubgroup`,
`Conductor.levelSubgroup_zero`, and
`PadicField.TopologicalData.additiveTrivialAt_iff_le_conductor`.
These names describe ingredients for a subsequent proof; the argument above
is not implemented by this statement module.

No finite Schwartz expansion, asymptotic expansion, single-gauge
majorization, or estimate on the size of a nonzero coefficient is asserted.
There is no lower bound on a root coordinate and no compactness claim for
the whole torus or the coefficient's support. The later geometric passage
from bounded root coordinates to rectangular block support, and the final
compact-support assembly, are separate obligations.
