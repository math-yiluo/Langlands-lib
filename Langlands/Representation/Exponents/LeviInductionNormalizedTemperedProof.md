# Normalized parabolic induction preserves temperedness (Renard VII.2.2): proof

`leviInductionNormalizedTempered`, in namespace
`Langlands.Aubert.General.RepresentedParabolic`, proves the published proposition
`LeviInductionNormalizedTemperedStatement.{u,v}`, with independent field and
representation-carrier universes and no hypotheses. The setting is a connected reductive
group `G` over a nonarchimedean local field `F`. It carries the canonical rational-point
topology and the retained local-compactness and nonarchimedean-group instances. Let
`p : P ⟶ G` be an actual rational parabolic with rational Levi `l : M ⟶ P` and matching
geometric unipotent radical `r`, and give `M(F)` the topology `leviPointTopology l hl`. If
a smooth complex representation `σ` of `M(F)` satisfies the normalized-exponent
temperedness predicate for `M`, then the normalized induction
`(leviInductionFunctor p l r hp hr hl hmul).obj σ` satisfies the same predicate for `G`. No
standardness, irreducibility or finite length is assumed. Presentation existence, Jacquet
admissibility, quotient compactness and Iwahori contraction are not hypotheses either:
each is a published theorem used inside the proof.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`), VII.2.2 Lemma,
printed pp.227–228 / PDF pp.233–234. Renard computes the exponents of `r_Q^G i_P^G σ`
through the geometric lemma VI.5.1 and compares them with the exponents of `σ` along the
intersection parabolics. The Library proof follows this route for arbitrary represented
parabolics. It does not reduce to standard parabolics.

## Implemented proof

The theorem applies the published conditional assembly
`leviInductionNormalizedTempered_reduction` (module
`Exponents/LeviInductionTemperedReduction`) to four published unconditional proofs:

| Premise | Proof |
| --- | --- |
| `RepresentedGeometricLemmaStatement` | `representedGeometricLemma` |
| `ArbitraryParabolicJacquetAdmissibilityStatement` | `arbitraryParabolicJacquetAdmissibility` |
| `ArbitraryParabolicQuotientCompactStatement` | `arbitraryParabolicQuotientCompact` |
| `ParabolicRootPresentationExistenceStatement` | `parabolicRootPresentationExistence` |

Inside the imported assembly, the temperedness predicate for `G` has two parts.

- Admissibility of `i_P^G σ` comes from admissibility of `σ` and compactness of
  `P(F) \ G(F)`, through `leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement`.
- The cone clause has to hold for every parabolic triple `(Q, L, A)` of `G`. Presentation
  existence gives the required root presentation of the specified triple. For each
  presentation, radical and real exponent `χ` of `r_Q i_P σ`, the geometric lemma gives
  a finite filtration of `r_Q ∘ i_P` with intersection pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}`.
  The published `normalizedRealPart_mem_nonnegCone_of_isGluedFrom` (module
  `Exponents/GeometricLemmaTemperedCone`) then places the real part of `χ` in the
  nonnegative root cone. It uses three facts: temperedness of `σ` along each `P'`; negation
  stability of relative roots (the published `relativeRootNegation`); and admissibility of
  each `r^M_{P'} σ`, transported along `leviPointsEquiv`, which is Jacquet admissibility
  applied to `M` and `P'`.

The four premises are proved in `Geometric/RepresentedGeometricLemmaProof`,
`Exponents/ArbitraryParabolicJacquetAdmissibilityProof`,
`Exponents/ArbitraryParabolicQuotientCompactProof` and
`GroupScheme/Rational/ParabolicRootPresentationProof`. This theorem adds only their
composition with the assembly. The statement pair and its imported closure are unchanged.
