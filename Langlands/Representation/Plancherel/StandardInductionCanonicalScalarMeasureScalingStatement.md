# Rescaling the quotient measures of a canonical standard-composite scalar

Author: Worker 200.

## Declaration and provenance

`Langlands.Plancherel.StandardInductionCanonicalScalarMeasureScalingStatement`
is a proposition-valued definition, an exact proof target. This pair states
the target and does not prove it.

It concerns the published construction
`standardInductionCompositeCanonicalRationalScalar` of the module
`StandardInductionCanonicalScalar`: the rational scalar of the composite
`J₀₁ J₁₀` of the actual standard intertwining integrals between the
inductions from two parabolics, for fixed subgroup, compact-model and measure
data. The target says how this scalar changes when the two quotient measures
are multiplied by positive constants.

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (registered
original `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). In I.1,
printed p.240 / PDF p.6, the source normalizes the Haar measure of every
closed algebraic subgroup by a special maximal compact subgroup. The integrals
`J_{P'|P}` of IV.1, printed pp.277–278 / PDF pp.43–44, and the scalar `j_P` of
IV.3, printed p.285 / PDF p.51, depend on that normalization. The source does
not state the rescaling rule separately. The provenance is internal, and no
new translation of a numbered literature result is claimed.

## Quantified data

The proposition quantifies over exactly the data of the published canonical
scalar, twice, with shared subgroups and representation:

* a nonarchimedean local field `F : Type u` of arbitrary characteristic, a
  connected reductive group scheme `L` over `F` (`hL`), a topology on
  `L(F)` for which the valuation-image projection is continuous (`hp`);
* a locally compact, Hausdorff, nonarchimedean group `G : Type uG`, closed
  semidirect decompositions `P₀ = M U₀` and `P₁ = M U₁` with closed
  parabolics, `IsUnimodularModulus` for both radicals and continuous Levi
  projections, a compact open subgroup `K` with `G = P₀ K = P₁ K`, a
  multiplicative homeomorphism `e : L(F) ≃ₜ* M`, continuity of every
  rational norm character of `L`, and a canonical
  `SmoothRep.{0,uG,uV} ℂ M` named `A`;
* Borel structures on the two radicals, the two intersections and the two
  quotient spaces; quotient measures `q₁₀` on `(U₀ ∩ U₁) \ U₁` and `q₀₁` on
  `(U₁ ∩ U₀) \ U₀`; regular right-invariant Haar measures `μU₀`, `μU₁`,
  `μI₁₀`, `μI₀₁` with the two `QuotientIntegration.IsCompatible` identities;
* nonzero `c, d : ℝ≥0`, and a second family of regular right-invariant Haar
  measures `μU₀'`, `μU₁'`, `μI₁₀'`, `μI₀₁'` with compatibility identities for
  `c • q₁₀` and `d • q₀₁`;
* closedness of `M` and the two `SquaredModulusCompatibility` identities;
* continuations `p`, `q` of the compact conjugates of the two
  `standardInductionIntertwinerFamily`s built from `q₁₀`, `q₀₁` and the first
  Haar measures, on their `standardIntertwiningFullDomainRegion`s, and
  continuations `p'`, `q'` of the corresponding families built from
  `c • q₁₀`, `d • q₀₁` and the second Haar measures;
* nonempty subsets `D₁₀`, `D₀₁` of the first two full domains, and nonempty
  open subsets `D₁₀'`, `D₀₁'` of the full domains for the rescaled measures;
* a nonempty set `D` of parameters at which the induction from `P₀` of the
  twist of `A` is irreducible.

No relation between the two continuation choices, between the subsets, or
between the two families of auxiliary Haar measures is assumed.

## Conclusion

The canonical scalar built from `c • q₁₀`, `d • q₀₁`, the second Haar
measures, `p'`, `q'`, `D₁₀'`, `D₀₁'` and `D` equals

\[
(c d) \cdot j(q_{10}, q_{01}),
\]

where `j(q₁₀, q₀₁)` is the canonical scalar built from `q₁₀`, `q₀₁`, the first
Haar measures, `p`, `q`, `D₁₀`, `D₀₁` and `D`. The factor `c d` is the
constant regular function `algebraMap ℂ _ ((c : ℂ) * (d : ℂ))` in the published
field `rationalUnramifiedFunctionField L hp hL`.

## Intended proof route

This is not proof evidence. The published `domain_smul_measure` and
`operator_smul_measure` (module `StandardIntertwiningMeasure`) show that the
full domains for `c • q₁₀` and `q₁₀` coincide and that the standard integral
for `c • q₁₀` is `c` times the one for `q₁₀`. The published
`compactIntertwiningOperator_smul` passes this to the compact pictures. On
the open sets `D₁₀'`, `D₀₁'`, rational uniqueness of continuations then gives
`p' = c • p` and `q' = d • q` on the common regular regions. Hence the
continued composites differ by `c d`. Since both canonical scalars use the
same internally selected coefficient, which depends on `D` but not on any
measure, the regular presentations of the two scalars agree after
cross-multiplication on a nonempty open set, so the fractions agree.

## Scope

Convergence, continuation, generic irreducibility and the squared-modulus
identities remain data of the statement, as in the published canonical
scalar. The constants `c`, `d` are arbitrary. The target does not relate
normalizations by different compact subgroups, does not compute any constant,
and says nothing about the source's special maximal compact subgroup,
parabolic independence, nonvanishing, positivity, `μ` or the Plancherel
formula.
