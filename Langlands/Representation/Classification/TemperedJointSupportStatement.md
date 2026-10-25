# Joint fine, middle and coarse support of tempered product-Levi representations

`Langlands.GLTemperedJointSupportStatement.{uF,uV}` is a closed proposition
definition. It states the common existence prerequisite for the support
hypotheses of `GLRelativeRegularComparisonStatement` and
`GLSupportedRelativeRecoveryStatement`. This module supplies the statement;
it proves none of its support, analytic, or induction assertions.

## Quantifiers and analytic input

For every prime `p`, field `F : PadicField.{uF} p`, compatible realization
`T : F.TopologicalData`, positive natural rank `n`, ordered block shape
`B : GeneralLinear.BlockShape n`, and actual complex representation
`π : Rep.{uV} ℂ (B.Levi F.Carrier)`, the only representation hypotheses are
`Representation.IsIrreducible π.ρ` and
`RelativeRegularComparison.IsLeviTempered T B π`.

Here `B.Levi F.Carrier` is the product of the general linear groups of the
specified block sizes. The analytic hypothesis uses the topology supplied by
`T` and the actual quotient

`B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)`.

It quantifies over every measurable structure making that quotient a Borel
space, and every Haar measure on it. For each measure,
`IsTemperedModCenter` requires admissibility and a smooth unitary scalar
central character for which every absolute matrix coefficient, with a
smooth-dual functional and any representation vector, lies in `L^(2+ε)` for
every positive real `ε`. Admissibility includes smoothness.
`T.exists_isHaarMeasure_leviCentralQuotient` ensures that this quantification
is nonvacuous. The quotient uses the full product center, rather than only
the diagonal scalar center of the surrounding general linear group.

No tensor presentation, chosen central character, selected support, critical
pair, opposite embedding, or quotient map is supplied as input. No head,
relative recovery, or Langlands classification or exhaustion theorem is a
premise. There is no outer real parameter or ambient induced quotient in
this target.

## The joint support data and actual groups

The conclusion first chooses `Q : BlockRefinement B` and writes
`D := B.flatten Q`. It then chooses `R : BlockRefinement D`,
`S : BlockRefinement B`, and a literal equality of ordered block shapes

`h : D.flatten R = B.flatten S`.

Write `C := D.flatten R`. The corresponding standard nested Levis are the
fine Levi `C.Levi F.Carrier`, middle Levi `D.Levi F.Carrier`, and coarse
Levi `B.Levi F.Carrier`. Unrefined blocks and equality of consecutive Levis
are allowed. The shapes include their coordinate identifications; `h` is
not merely equality of ranks or an arbitrary group equivalence.

For a refinement `U` of a shape `A`, the actual subgroup
`refinedParabolic F.Carrier A U` is the product of upper block parabolics
inside `A.Levi F.Carrier`. Its Levi subgroup is
`refinedLevi F.Carrier A U`. The constructed equivalence
`flattenedLeviEquiv F.Carrier A U` identifies
`(A.flatten U).Levi F.Carrier` with this subgroup by nested block-diagonal
matrices. Thus the cases `(D,R)`, `(B,Q)`, and `(B,S)` use actual subgroups
and their existing identifications.

The same existential data include:

- `ω : Rep.{max uF uV} ℂ (C.Levi F.Carrier)`, irreducible, satisfying
  `CuspidalSupport.IsLeviCuspidal C ω.ρ`, and unitarizable;
- `v₀ : Fin C.length → ℝ`, satisfying the existing
  `RelativeRegularComparison.IsPositiveRootParameter D R v₀`;
- `σ : Rep.{max uF uV} ℂ (D.Levi F.Carrier)`, irreducible and satisfying
  `RelativeRegularComparison.IsLeviSquareIntegrable T D σ`.

Cuspidality means admissibility together with vanishing of the actual
unipotent coinvariants for every proper standard refinement of `C`.
Unitarizability is existence of an invariant positive definite Hermitian
form, without a prescribed carrier norm, topology, or Hilbert completion.
Square-integrability quantifies over all Borel Haar measures on the actual
quotient of the middle product Levi by its full center. For each measure
it requires admissibility, a smooth unitary scalar central character, and
`L²` integrability of all the descended absolute smooth matrix coefficients.

## Cone, twists, and three simultaneous maps

In each middle block `i`, let the fine sizes be `d₀,...,d_(r-1)`. The positive
root condition supplies a strictly positive coefficient `c_j` for every
adjacent scalar root and expresses the restriction of `v₀` as

`∑ j < r-1, c_j * (e_j / d_j - e_(j+1) / d_(j+1))`.

The existing `D.flattenBlockEquiv R` places these coordinates in `Fin C.length`.
The reciprocal sizes convert the scalar root `z_j/z_(j+1)` into determinant
exponents, since `|det(z I_d)|^a = |z|^(d*a)`. In particular the size-weighted
sum is zero in each middle block. This is a strictly positive root expansion;
it imposes no strict ordering of the entries of `v₀`. An unrefined middle
block has an empty root sum and parameter zero.

All three actual complex-linear intertwiners are existentially quantified
together, after the same `Q,R,S,h,ω,v₀,σ`:

| Map | Source representation | Target |
| --- | --- | --- |
| `qFineMiddle` | `innerInduced T D R (fineTwist T D R ω v₀ 0)` | `σ.ρ` |
| `qMiddleCoarse` | `middleInduced T B Q σ` | `π.ρ` |
| `qFineCoarse` | `innerInduced T B S (fineTwist T B S (h ▸ ω) (h ▸ v₀) 0)` | `π.ρ` |

Here the source of each map is the `.ρ` of the displayed representation.
The conclusion requires `Function.Surjective` for each map. They are
quotient witnesses for the given `π` and the same `σ`, without sections,
canonical choices, or uniqueness conclusions.

`fineTwist` first twists on the flattened product Levi, then pulls the action
back along the inverse of `flattenedLeviEquiv`. Its determinant exponent is
`-v₀(k) + t(parent(k))`; the zero function supplied here makes it exactly
`-v₀(k)`. `middleInduced` performs the corresponding actual flattened-Levi
identification for `σ` and applies untwisted normalized refined induction.
`innerInduced` uses `T.normalizedRefinedInduced`: inflate along the actual
Levi projection, use positive-half-modulus covariance, and let the coarse
group act by right translation on smooth induced functions. Absolute values
are residue-normalized as `q^(-valuation)`. Silberger's fine twist `+i v₀`
therefore has the negative determinant exponent in this convention.

The direct fine-to-coarse source uses literal equality transport `h ▸ ω`
and `h ▸ v₀`. It preserves the given fine representation and parameter;
there is no second independently selected fine support. Equality of shapes
alone does not assert induction in stages or exactness. Those are the
obligations needed to construct the third map from the first two.

The independent universes `uF` and `uV` belong to the field and input carrier.
Both support carriers may lie in `Type (max uF uV)`. Twists preserve that
universe, and induced carriers also have universe `max uF uV`.
Intertwiners to the original carrier in `Type uV` allow distinct source and
target universes. No equality of field and carrier universes is imposed.

## Originals, derivation, and retained scope

The direct source is A. J. Silberger, *The Langlands Quotient Theorem for
p-adic Groups*, Math. Ann. 236 (1978), 95–104 (S78). Printed pp.98–99 describe
tempered support; the initial proof setup of Proposition 5.1 on p.99 chooses
discrete-series middle support for a tempered coarse representation and then
unitary cuspidal fine support with a strictly positive root expansion.
Section 2, p.97, recalls exactness and transitivity of induction and Jacquet
functors. The normalization is fixed on p.96.

The retained original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 389 read pp.96–100 and checked the p.99 support formulas as an image.

S78 cites A. J. Silberger, *Introduction to Harmonic Analysis on Reductive
p-adic Groups* (1979) (S79), Corollary 4.5.11, pp.189–190, for discrete-series
support, and Corollary 2.4.2, p.92, and Theorem 4.4.4, pp.177–180, for fine
support and the strict root criterion. The registered source is
`silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`,
retained at
`/home/taskhub/central-library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`.
Worker 389 read the passages in §2.4, pp.90–92, Theorem 4.4.4, pp.177–180,
and pp.189–190, checking the images of Corollary 2.4.2, Theorem 4.4.4(4),
and Corollary 4.5.11. No source-specific retained erratum was found.

This target is a derived GL product-Levi specialization and joint assembly
of that setup, not a literal statement of either book corollary. Corollary
4.5.11 embeds a tempered representation into normalized opposite induction
from discrete-series data. Corollary 2.4.2 starts from a critical pair and
exponent and gives an opposite-induction embedding from irreducible
admissible J-supercuspidal data. Neither embedding is literally the required
upper quotient. Theorem 4.4.4 treats coefficient functions on bounded central
strips; clause (4) puts their real exponent plus a strictly positive simple
root combination in the central dual. Its comparison with the predicates
used here also needs proof.

The [scope audit](../../../notes/jacquet/silberger-lemma53-scope.md) records
the constituent restriction required for the relative multiplicity argument
of S78 Lemma 5.3. This target does not extend that lemma to arbitrary
irreducible admissible representations. Its eventual quotient witnesses
place `π` and `σ` in their specified supported inductions; they supply no
unrestricted multiplicity or relative recovery result.

## Proof obligations and existing focused work

A subsequent proof must establish the analytic comparison with the source's
tempered and discrete-series conditions on the full central quotients,
including measure compatibility and coefficient/exponent comparisons.
It must extract support without selected support or critical data as inputs.
A route through factorization must prove the needed analytic tensor
equivalences and recover the original product-Levi representation:
admissible algebraic tensor factorization alone proves no analytic support
theorem.

The proof must also justify opposite-to-upper transport, with the actual
modulus factors, any parabolic conjugations or block reversals, smooth
duality and admissible biduality, and the analytic properties of dual inputs.
Fine support requires the strict exponent criterion, separation of the real
cuspidal central character, and unitarizability of the remaining cuspidal
data. Removing the real central direction in each middle block must yield
the stated root expansion, rather than assuming that expansion or inferring
an invariant form merely from a unitary central character.

Finally it must construct nested refinements with literal flatten equality,
transport the same fine data, prove normalized induction in stages through
the actual subgroup identifications, and use exactness or preservation of
surjectivity to construct the fine-to-coarse map from the first two maps.
All these steps must fit the allowed carrier universes.

The separate discrete-series positive-root support, nested-refinement,
tempered opposite-support, discrete-series Jacquet/summand, and analytic
tensor tasks retain their scopes. This module neither duplicates their
targets nor proves their inputs. It assembles the existence statement
needed by the supported comparison and recovery consumers, with no quotient
uniqueness or classification conclusion.
