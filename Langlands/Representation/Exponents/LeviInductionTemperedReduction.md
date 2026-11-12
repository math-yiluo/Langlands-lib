# Parabolic induction preserves temperedness, from four structural inputs

Author: Worker 4770. Module `Langlands.Representation.Exponents.LeviInductionTemperedReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This internal supporting module is a conditional assembly of Renard VII.2.2 for
represented parabolics. It derives the exact published target
`LeviInductionNormalizedTemperedStatement` from four published structural statements.
It proves none of these four statements, so it does not prove the target
unconditionally.

## Declarations

- `LeviInductionTemperedReductionStatement : Prop` (universes `u`, `v`) is the implication

  ```text
  RepresentedGeometricLemmaStatement.{u, v} →
    ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
      ArbitraryParabolicQuotientCompactStatement.{u} →
        ParabolicRootPresentationExistenceStatement.{u} →
          LeviInductionNormalizedTemperedStatement.{u, v}
  ```

  Each of the five propositions is the published one, unchanged:
  - `RepresentedGeometricLemmaStatement` (Renard VI.5.1, in
    `Langlands/Representation/Geometric/RepresentedGeometricLemmaStatement.lean`): for
    represented parabolics `P = MN` and `Q = LU`, `r_Q ∘ i_P` is glued (`IsGluedFrom`)
    from the pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}` of intersection data
    `GeometricLemmaIntersectionDatum`, one for each double coset `P(F) z Q(F)`;
  - `ArbitraryParabolicJacquetAdmissibilityStatement` (Renard VI.6.1, Corollary): the
    normalized Jacquet functor `jacquetFunctor` of every represented parabolic of every
    connected reductive group preserves admissibility;
  - `ArbitraryParabolicQuotientCompactStatement` (Renard V.5.1, Corollary): the quotient
    `Induction.LeftQuotient (pointImage p)` is compact for every represented parabolic;
  - `GroupScheme.ParabolicRootPresentationExistenceStatement` (motivated by Renard V.3.14):
    every rational parabolic, rational Levi and split component of a connected reductive
    group admits a compatible `ParabolicRootPresentation`;
  - `LeviInductionNormalizedTemperedStatement` (Renard VII.2.2): the target.

  The universes match the target: the geometric lemma and Jacquet admissibility are used
  for representations with carriers in `Type v`, compactness and presentation existence
  concern only groups over `k : Type u`.

- `leviInductionNormalizedTempered_reduction : LeviInductionTemperedReductionStatement.{u, v}`
  proves the implication.

## Proof

Fix the four inputs, then `k`, `G`, `hG`, the canonical topology on `G(k)` with its
local-compactness and nonarchimedean instances, and a represented parabolic
`p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P` with `hp`, `hl`, `hr`, `hmul`. Install on `M(k)`
the instances of the target statement: `hl.isConnectedReductive.isAffineHom`, the
topology `leviPointTopology l hl`, and `leviPoints_locallyCompactSpace` and
`leviPoints_nonarchimedeanGroup`. Let `σ` be a smooth representation of `M(k)` with
`hσ : IsNormalizedExponentTempered hl.isConnectedReductive σ`. The conclusion
`IsNormalizedExponentTempered hG ((leviInductionFunctor p l r hp hr hl hmul).obj σ)` has two
parts.

1. **Admissibility.** `hσ.isAdmissible` gives admissibility of `σ`. The published
   `leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement`
   (`ArbitraryParabolicInductionAdmissibility.lean`), applied to the compactness input,
   gives admissibility of the induced representation.

2. **The cone condition.** Fix a rational parabolic `q : Q ⟶ G`, a rational Levi
   `lQ : L ⟶ Q` and a split component `a : A ⟶ L` with `hq`, `hlQ`, `ha`. The condition
   `SatisfiesNormalizedExponentConeCondition` has two parts.
   - The nonempty-presentation part is the presentation-existence input applied to
     `(q, lQ, a)`.
   - For the second part fix a presentation `pres`, a radical `rQ : V ⟶ Q` with `hrQ`,
     `hmulQ`, and a normalized Jacquet exponent `χ` of the induced representation along
     `(q, lQ, rQ)`. The geometric-lemma input, applied to `(p, l, r)` and `(q, lQ, rQ)`,
     gives `m`, representatives `z : Fin m → G(k)`, data
     `D i : GeometricLemmaIntersectionDatum … (z i)` and the gluing `hD`. The published
     theorem `relativeRootNegation` (`RelativeRootNegationProof.lean`), applied to the
     maximal split torus `pres.data.i` of `G` (`pres.isCompatible.maximalSplit`), gives
     the negation stability `hneg` of its relative roots. The published
     `normalizedRealPart_mem_nonnegCone_of_isGluedFrom` (`GeometricLemmaTemperedCone.lean`),
     applied to `D`, `hD`, `ha`, `pres`, `hneg`, `σ`, `hσ` and `χ`, gives
     `normalizedRealPart χ ∈ pres.nonnegCone`. Its remaining hypothesis is the
     admissibility of each Jacquet module `(leviJacquetFunctor (D i).p' (D i).l' (D i).r' …).obj σ`,
     a representation of `M'_i(k)`.
   - That admissibility is the Jacquet-admissibility input for the connected reductive
     group `M` (`hl.isConnectedReductive`), with the local-compactness and nonarchimedean
     instances of `M(k)` above, the represented parabolic `((D i).p', (D i).l', (D i).r')`
     of `M` and the admissible `σ`. It gives admissibility of
     `(jacquetFunctor (D i).p' (D i).l' (D i).r' …).obj σ`, a representation of the literal
     Levi image in `M(k)`. By definition `leviJacquetFunctor` is this Jacquet functor
     followed by pullback along `leviPointsEquiv (D i).p' (D i).l' …`, and the published
     `isAdmissible_comp_continuousMulEquiv` transports admissibility along that
     topological-group isomorphism.

The canonical topology of `M(k)` used by the Jacquet-admissibility statement for `M` is
`RationalPointFamily.pointTopology` with the affine instance
`hl.isConnectedReductive.isAffineHom`, which is `leviPointTopology l hl` by definition, so
no topology comparison is needed. The check of the theorem reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance and scope

This is derived content for the proof of Renard, *Représentations des groupes réductifs
p-adiques* (French version of 9 July 2026), VII.2.2, Lemma and proof, printed
pp.227–228 / PDF pp.233–234. Renard reduces to standard parabolics, applies the
geometric lemma VI.5.1 to `r_Q i_P σ`, uses temperedness of `σ` along the parabolics
`w·Q ∩ M` of `M`, compares the cones through the representatives `W_{L,M}` of (V.4.6.1)
and transfers exponents with VII.1.1. The route here keeps arbitrary represented
parabolics and does not reduce to standard ones. Its cone comparison is that of the
published `normalizedRealPart_mem_nonnegCone_of_isGluedFrom`, which uses weights on
unipotent radicals instead of `W_{L,M}`. The admissibility of `i_P σ` is the compactness
argument behind Renard's induction functor, and the admissibility of the Jacquet modules
of `σ`, used by the VII.1.1 transfer, is VI.6.1.

The four inputs remain separate proof obligations:

| Input | Proof task |
| --- | --- |
| `RepresentedGeometricLemmaStatement` | `c060fb34-b423-4ac5-8448-788ac7627913` |
| `ArbitraryParabolicJacquetAdmissibilityStatement` | `56206cc7-3e1e-4fae-840d-f5e8ccffd8ed` |
| `ArbitraryParabolicQuotientCompactStatement` | `c1ce4629-6768-4eb5-b4ee-0086526913ea` |
| `ParabolicRootPresentationExistenceStatement` | `c6c736b5-f1c4-4203-bb23-f7981c4fc3af` (as part of `ParabolicRootPresentationStatement`) |

The task identifiers locate work; they are not proof receipts. No standardness,
irreducibility, finite-length or presentation hypothesis is added beyond these four
inputs. A reduction of the same name by Worker 1585, staged in the previous TaskHub
instance, was not carried over; this module was written anew against the current
Library.
