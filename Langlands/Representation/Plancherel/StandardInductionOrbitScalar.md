# Orbit scalars for actual standard integral families

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

IV.1, printed pp.276–278 / PDF pp.42–44, defines scalar rationality on the
complex orbit by pullback to unramified characters, identifies induced
representations with fixed compact carriers, and requires naturality under
isomorphisms of inducing representations. The original standard integral
is defined by absolute convergence against every smooth contragredient
functional, together with representability in the original inducing
carrier. IV.1.1 then proves a convergence cone and rationality for
finite-length inducing representations.

At the start of IV.3, printed p.285 / PDF p.51, generic induced
irreducibility and Schur's lemma give scalarity of the opposite-intertwiner
composite and its rational scalar on the complex orbit. The present module
specializes the existing continued-induction orbit-scalar results to the
actual standard integral families. Their naturality squares and witnesses
for every inducing self-twist are supplied by the proved results of
`StandardInductionSelfComparison`. This specialization is not a separately
numbered source assertion or a proof of IV.1.1 or all of IV.3.

## Actual data and retained hypotheses

Let `F` be a nonarchimedean local field, in arbitrary characteristic, and
`L` a connected reductive group scheme over `F`. Put `H = L(F)` and let
`νL` be its complete rational norm-character family. Its topology,
`NonarchimedeanGroup` instance, continuity `hp` of the rational
valuation-image projection, and continuity of the norm characters are
explicit inputs.

The ambient `G` is a locally compact Hausdorff nonarchimedean group.
There are actual subgroup decompositions `P₀ = M U₀`, `P₁ = M U₁`,
with closed parabolics, radicals and Levi, a compact open subgroup `K`,
factorizations `G = P₀ K = P₁ K`, continuous semidirect projections,
and the two `IsUnimodularModulus` premises. A topological group
equivalence `e : H ≃ₜ* M` supplies the character chart. Write
`νM ψ = νL ψ ∘ e.symm` and
`χM = unramifiedCharactersHomeomorph e νL`.
The inducing object `A` is the canonical complex `SmoothRep` of `M`;
`Iᵢ(χ)` denotes its actual `UnramifiedLeviInduction` from `Pᵢ`,
twisted by `χM χ` with the existing positive Levi half-modulus
normalization. The orbit representation is `π = SmoothRep.pullback e A`.

The actual forward quotient is `(U₀ ∩ U₁) \ U₁`, implemented by
`QuotientSpace (U := U₀) U₁`, and the reverse quotient is implemented by
`QuotientSpace (U := U₁) U₀`. Their measures `q₁₀,q₀₁` remain explicit.
The module retains Borel structures on both radicals, both subgroup
intersections and both quotients, regular right-invariant Haar measures
on the radicals and intersections, and the two quotient-integration
compatibility proofs. The two `SquaredModulusCompatibility` premises
are identities of actual conjugation moduli from the existing
Haar-modulus construction. They are supplied rather than proved here.

The field universe `u`, ambient-group universe `uG` and inducing-carrier
universe `uV` are independent. There is no characteristic-zero, split,
quasisplit, positive-rank, finite-length, admissibility or unitary-locus
restriction. No rational-point realization of the displayed ambient
structural and measure data is asserted.

## The original families and their continuation

For each direction, `Ωᵢⱼ` is exactly
`standardIntertwiningFullDomainRegion` for its source decomposition,
target radical, quotient measure and inducing object. Thus membership
means that every source vector has the original integral at every group
element: all scalar integrals against the smooth dual converge
absolutely and have a representing vector in the original inducing
carrier. Neither full domain is asserted open.

`J₁₀,J₀₁` are the actual `standardInductionIntertwinerFamily` objects
on those domains. They are the existing `fullSourceIntertwiner`
evaluated at the twisted inducing representation. They are not free
operator-family inputs.

Separate nonempty ambient opens `D₁₀ ⊆ Ω₁₀` and `D₀₁ ⊆ Ω₀₁` are
explicit convergence premises. For every element of the full stabilizer
of `π`, `standardInductionSelfBaseChangeData_stabilizer` proves the
needed original self-comparison witness for these same families and
opens. It uses the actual inducing twisting equivalence, translation
invariance of the exact full domains, and naturality of the original
integrals. No comparison square is assumed by this module.

`p` and `q` are independently supplied `RationalOperatorContinuationData`
for the compact restrictions of these families. Each contains a single
whole-operator denominator, nonzero at every point of its original full
domain, and a polynomial numerator family. This is an explicit
continuation premise; it is not deduced from scalar integrability.
The continued ambient composite `C` is the reverse continued intertwiner
after the forward continued intertwiner on

\[
R=p.\mathrm{regularRegion}\cap q.\mathrm{regularRegion}.
\]

The original domains and the chosen convergence opens need not intersect.
The existing continuation results show that `R` is nonempty and dense
using the actual rational character space. For a compact vector `v` and
complex linear functional `ℓ` put

\[
f_C=\mathrm{continuedCompositeRationalScalar}(p,q,v,\ell).
\]

This is the concrete function-field fraction extracted from the actual
compact composite. On `R` its coefficient is
`ℓ((q.continuedOperator ∘ p.continuedOperator)(v))`.
It is not a supplied scalar selected to enforce an equation.

## Stabilizer fixedness and the orbit presentation

For the four declarations in the module, `G` is additionally separable,
and a separate nonempty ambient open `D` satisfies
`I₀(χ).IsIrreducible` for every `χ ∈ D`. The normalized extraction
premise is `ℓ(v) = 1`. This pair is supplied; its existence is not
proved. The irreducibility premise concerns the actual induced smooth
representation and need not hold at the evaluation parameter.

`standardInductionCompositeRationalScalar_stabilizer_fixed` proves

\[
\tau^* f_C=f_C\qquad
(\tau\in\operatorname{Stab}_{X(H)}(\pi)).
\]

The full stabilizer is defined by equality of actual smooth-representation
isomorphism classes. Translation has convention
`τ*(b)(χ) = b(τχ)`. The proof specializes
`continuedInductionCompositeRationalScalar_stabilizer_fixed` to the
actual standard families and supplies the proved full-stabilizer
witnesses. Its imported engine obtains generic scalarity by smooth
Schur on the actual induced representation, transports the original
comparison squares to compact carriers and proves equality in the
concrete rational function field. Stabilizer finiteness is not required.

`standardInductionCompositeOrbitScalarPresentation` additionally assumes
`Finite` for that full stabilizer. It specializes the corresponding
continued-induction constructor with the same proved witnesses. It
chooses an `UnramifiedInvariantScalarPresentation` of the exact fraction
`fC`: an invariant regular numerator and nonzero invariant regular
denominator representing it. Finiteness is used for existence of this
presentation; it is not proved here.

The existing presentation interface supplies the scalar on the
representation-isomorphism-class twist orbit of `π`, its open dense
nonempty denominator regular region, continuity and agreement with
other presentations on their common regular region. These are
properties of this complex orbit; no density on the unitary locus or
algebraic-variety quotient identification is inferred.

## Continued and original ambient equations

`standardInductionComposite_eq_orbitScalar` takes any invariant
presentation `r` of `fC`, the normalized extraction pair and generic
induced irreducibility. For `χ ∈ R` with `r.denominator(χ) ≠ 0` it proves

\[
C(\chi)
 =r([\pi\otimes\chi])\,\operatorname{id}_{I_0(\chi)}.
\]

The proof is the corresponding continued-induction theorem specialized
to the actual standard families. It is an equality of ambient
`Representation.IntertwiningMap` objects, not only their extracted
coefficients. Once `r` is supplied this theorem needs no finite-stabilizer
premise. It allows reducible evaluation parameters in the stated regular
region.

`standardInductionOriginalComposite_eq_orbitScalar` instead takes
`χ ∈ Ω₁₀ ∩ Ω₀₁` with the same invariant denominator nonzero, and proves

\[
J_{01}(\chi)J_{10}(\chi)
 =r([\pi\otimes\chi])\,\operatorname{id}_{I_0(\chi)}.
\]

Each continuation's `subset_regularRegion` sends this parameter into
`R`. The proof uses `continuedInductionIntertwiner_agrees` separately
for the two directions, combines those equalities by congruence of
intertwiner composition, and applies the preceding continued equation.
This theorem does not assert that the two original domains intersect.

## Remaining obligations

Initial nonempty-open full convergence, the two rational continuations,
generic induced irreducibility, finite full stabilizer and the normalized
extraction pair remain application premises. No opposite-parabolic
relation between `P₀` and `P₁` is assumed or constructed. The chosen
denominator loci are not asserted maximal and values at poles are not
defined.

Opposite-parabolic identification, parabolic independence,
nonvanishing, positivity, the source-normalized global `j` and `mu`,
compatible normalization of the measures, actual structural realizations,
and the Schwartz, spectral and main Plancherel conclusions remain
separate obligations. The supplied representation-theoretic and analytic
premises are not permitted external structural inputs for completion of
the standing program.
