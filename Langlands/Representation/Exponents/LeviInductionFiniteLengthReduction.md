# The represented-parabolic assembly for Renard VI.6.2

Author: Worker 4950. This internal supporting unit defines
`Langlands.Aubert.General.RepresentedParabolic.LeviInductionFiniteLengthReductionStatement`
and proves it as `leviInductionFiniteLength_reduction`. It keeps two published
propositions as antecedents and does not prove the unconditional
`LeviInductionFiniteLengthStatement`.

The independent universes are `u` for the field and the rational-point groups and
`v` for the representation carriers. The conclusion is the existing closed
`LeviInductionFiniteLengthStatement.{u, v}`. Its quantifiers, topology instances,
represented parabolic, Levi and radical data and normalized functor
`leviInductionFunctor` are unchanged.

The two antecedents are the published propositions:

- `LeviCuspidalEmbeddingStatement.{u, v}` (Renard VI.2.1, Corollary);
- `LeviSupercuspidalInductionAssociationStatement.{u, v}` (Renard VI.5.4,
  Theorem). Only its first conjunct is used: finite length of `i_R^G ρ` for an
  irreducible supercuspidal `ρ`.

Their proofs are separate obligations. Publishing this reduction does not
complete the host proof task.

## Proof

Fix the field, the group `G`, the represented parabolic `P = M U` and the
instances of the target. Give `M(F)` its canonical topology `leviPointTopology l hl`
with the published local-compactness and nonarchimedean instances.

1. **Reduction to irreducibles.** The published
   `leviInduction_preservesFiniteLength_of_irreducibles` reduces the target to
   irreducible smooth `σ` of `M(F)`. It applies
   `SmoothRep.preservesFiniteLength_of_irreducibles`, which inducts on length
   using the exactness of `leviInductionFunctor` from the published
   `leviParabolicFunctorsExact`.
2. **Cuspidal embedding.** The first antecedent is applied to the connected
   reductive group scheme `M`, using `hl.isConnectedReductive`. Its canonical
   point topology is, by definition, the installed `leviPointTopology l hl`. This
   gives an actual rational parabolic `Q = N V` of `M` and an irreducible `ρ` of
   `N(F)`. The representation `ρ` is supercuspidal in the written-out sense:
   its normalized Jacquet module vanishes along every proper actual rational
   parabolic of `N`. The antecedent also gives an injective intertwiner
   `f : σ → i_Q^M ρ`. The carrier of `ρ` is in `Type v`, and that of `i_Q^M ρ`
   is in `Type (max u v)`. The other conclusions of the antecedent are not used.
3. **Induction in stages.** `LeviParabolicExtensionDatum.ofExtension` is built
   from the published `leviParabolicExtension`. It gives an actual rational
   parabolic `R = N W` of `G` with the same Levi `N` and the same embedding of
   `N` in `G`, with `R(F) ⊆ P(F)` and `Q(F) = M(F) ∩ R(F)`. The published
   `LeviParabolicExtensionDatum.leviInduction_iso` applies the published
   transitivity theorem `leviParabolicTransitivity` (Renard VI.1.4). It gives an
   isomorphism of functors
   `i_R^G ≅ i_Q^M ⋙ i_P^G`, at carrier universes `v` and `max u v`.
4. **Finite length of the supercuspidal induction.** The second antecedent is
   applied with `P = P' = R` and `ρ = ρ'`. Its first conjunct gives an actual
   composition series of `i_R^G ρ`. The published
   `LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength` turns it
   into finite group-algebra length (`SmoothRep.HasFiniteLength`).
5. **Transport and descent.** The component at `ρ` of the isomorphism of step 3
   is a surjective equivariant map `i_R^G ρ → i_P^G (i_Q^M ρ)`. So the target
   also has finite length, by `IsFiniteLength.of_surjective`. The published
   `leviInduction_hasFiniteLength_of_injective` postcomposes induced functions
   with `f`, and allows the two carrier universes `v` and `max u v`. It gives an
   injective intertwiner `i_P^G σ → i_P^G (i_Q^M ρ)`. Finite length descends to
   `i_P^G σ`.

No standardness, admissibility, finite-length, unimodularity,
presentation-existence, quotient-compactness, Jacquet-admissibility,
geometric-lemma or Weyl-group hypothesis is added. The only hypotheses are the
two named antecedents. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The provenance is internal. This file composes the named published interfaces.
The original argument is Renard 2026, VI.6.2, Lemma and proof, printed p.178 /
PDF p.184 (source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The proof
says that for supercuspidal `τ` the Lemma is Theorem VI.5.4. In general `τ` is
a subrepresentation of some `i_{P'}^M ρ` with `ρ` irreducible supercuspidal
(Corollary VI.2.1). Exactness of `i_P^G` makes `i_P^G τ` a subrepresentation of
`i_P^G i_{P'}^M ρ`, which has finite length. The opening sentence of VI.6.2
announces the passage from irreducible to finite-length representations.

The implementation makes three points explicit that the source leaves implicit:

- the construction of the parabolic `R = P'N` of `G` (published
  `leviParabolicExtension`);
- the two carrier universes of the stages;
- the passage from the irreducible case to all finite-length representations.
