# Entire dependence on corank determinant slices

Module `Langlands.Representation.RankinSelberg.CorankOneEntireSliceProof`
proves
`Langlands.RankinSelberg.corankOneEntireSlice.{uF,uV} :
CorankOneEntireSliceStatement.{uF,uV}`.
The theorem has no free term parameters or added hypotheses. It proves the
published closed proposition with independent field and original
representation-carrier universes.

The inputs are exactly those of the statement: a canonical p-adic field,
a unitary additive character, a rank parameter `r` including zero, the supplied
compatible quotient measure, a full inverse-character Whittaker-type
representation, any functional and any vector in its actual coefficient image,
and a family `U` of standard-character Whittaker functions on `GL_(r+2)`.
The family has one compact open right level and pointwise entire dependence.
Zero functionals and coefficients and reducible test representations are
included.

Write `T = F.canonicalTopologicalData`, `d = r + 1`,
`Q = N_d \ GL_d(F)`, and `S_m = determinantSlice T r m`.
For every integer `m`, the theorem proves integrability on `S_m` for every
family parameter and analyticity at every parameter of the literal
`sliceCoefficient`. On a representative `g`, the integrand is

```text
(U z).val (rankInclusion 1 g) * Wprime.val.val g
  * determinantWeight (normalizedAbsoluteValue T) g (0 - 1/2).
```

Thus the spectral variable remains `s = 0` and the corank determinant shift
remains `-1/2`. The parameter `z` varies only the family. The supplied measure,
the actual quotient and Haar measures, determinant order, normalized absolute
value and restricted Bochner integrals are those in the statement.

## Implemented proof

The assembly reinstalls the canonical topology, valuation, local-field and
Borel instances used by the statement, and extracts its common subgroup `K`.
It then combines two proved helpers.

First, `CommonLevel.corank_common_compact_support` in
`CorankCommonCompactSupport` derives a single compact subset `C` of `Q`
containing all the slice-restricted supports. Its proof uses
`CommonLevel.root_bound` in `CommonLevelRootSupport`: continuity and
compactness of the integral subgroup give one additive lattice whose
conjugate simple-root unipotents lie in `K`, uniformly in the integral factor.
Right invariance and left Whittaker covariance force the additive character
to be trivial on the corresponding scaled lattice whenever a value is nonzero.
The conductor characterization bounds every adjacent diagonal ratio.

In an Iwasawa representative `n diag(a) k` on `GL_d`, the corank inclusion
appends the diagonal coordinate `1`. The last simple-root bound therefore
bounds the last coordinate of `a`, and reverse induction bounds all
coordinates above. On `S_m`, their absolute-value product is the fixed
positive number `q_F^(-m)`, giving positive lower bounds as well.
The image of the resulting product of compact annuli with the compact
integral subgroup is compact. This contains the actual supports uniformly
in `z`, the inverse-character test function and the spectral variable.
The final assembly specializes this stronger support result to `Wprime.val`
and `s = 0`.

Second, compatibility of the supplied measure `ν` gives its regularity,
hence finiteness on compact sets. With this instance,
`CommonLevel.corank_slice_of_common_support` in
`CorankSliceFiniteEvaluation` applies to the derived `C`.
It obtains an original vector representing `Wprime` using
`modelMap_surjective`. Smoothness of the original representation gives an
open stabilizer `K₁` of that vector. The subgroup

```text
J = K₁ ∩ (rankInclusion 1)⁻¹(K) ∩ GL_d(O_F)
```

is compact open. Every integrand is right `J`-invariant: the first factor is
fixed by `K`, the second by the vector stabilizer, and the determinant weight
by the integral subgroup. The determinant slice is also `J`-stable, since
the determinant of an integral group element has order zero.

The compact set `C ∩ S_m` has a finite cover by right `J`-orbits in `Q`.
Keeping one representative of each distinct orbit gives pairwise disjoint
compact open orbits chosen independently of `z`. Each has finite `ν`-mass.
The helper proves an equality of indicator functions, and integrates it to
obtain both integrability on `S_m` and the actual formula

```text
sliceCoefficient T ν (corankOneIntegrand ... (U z) Wprime.val 0) m
  = ∑ q ∈ u, (ν.real (rightTranslateOrbit N J q) : ℂ)
      * corankOneIntegrand ... (U z) Wprime.val 0 q.
```

This is an equality for the existing integral. Its finite set and orbit masses
are independent of `z`. Quotient induction identifies each point value with
the displayed representative formula, whose only variable factor is
pointwise analytic by hypothesis. Closure under multiplication by constants
and `Finset.analyticAt_fun_sum` prove analyticity at every parameter.
The final theorem returns this pair of conclusions.

## Source, provenance and scope

This is derived internal content from H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin–Selberg Convolutions*, American Journal of Mathematics
105 (1983), 367–464, registered as `jpss-1983-rankin-selberg`.
Section 4.5, printed pages 408–409 (one-based PDF pages 43–44), supplies
the common-level, common-support and finite-evaluation mechanism. The retained
original has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The corank extraction uses the appended identity coordinate in place of the
equal-rank last-row Schwartz test. The helper Markdown files explain their
individual derivations. The assembly discharges their support and measure
hypotheses from the unchanged statement.

This theorem establishes the entire determinant-slice assertion. Subsequent
factor specialization, second-block deformation adapters and unrestricted
multiplicativity remain separate obligations. It asserts no full-plane
convergence of the unsliced integral. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
