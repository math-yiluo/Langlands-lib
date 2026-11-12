# Equivariant retractions onto normal adjoint subgroups: proof

Worker 4293.

`Langlands.GroupScheme.normalAdjointEquivariantRetraction` proves exactly the
published `Langlands.GroupScheme.NormalAdjointEquivariantRetractionStatement.{u}`
(`Adjoint/NormalEquivariantRetractionStatement.lean`) at an arbitrary universe
`u`. Let `k : Type u` be an algebraically closed field of any characteristic.
Let `G` and `H` be group schemes over `Spec k` with `IsAdjoint G` and
`IsAdjoint H`, and let `j : H ⟶ G` be a closed subgroup whose range functor is
normal on all tests. Let `S` be a split torus with automorphic actions `b` on
`G` and `c` on `H` for which `j` is equivariant on every test scheme. The
theorem then constructs an actual homomorphism `r : G ⟶ H` with `j ≫ r = 𝟙 H`.
It also proves
`b.act s g ≫ r.hom.hom = c.act s (g ≫ r.hom.hom)` for every scheme `T` over
`Spec k`, every `s : T ⟶ S.X` and every `g : T ⟶ G.X`, including nonreduced
`T`. The statement and the modules it imports are unchanged. No hypothesis is
added. `IsAdjoint` keeps its published meaning: connected reductive, with
finite full scheme-theoretic centre equal to the bottom subgroup functor.

## Implemented proof

The Lean proof is a single term composing published Library theorems. It adds
no new lemma. From the outside in:

1. `normalAdjointEquivariantRetraction_of_semisimpleNormalComplement`
   (`Adjoint/NormalEquivariantRetractionReduction.lean`) proves the target from
   `SemisimpleNormalComplementStatement.{u}`. A commuting closed normal
   complement `K` has flat surjective multiplication `H × K → G`. The trivial
   centre of `H` makes this multiplication a monomorphism and hence an
   isomorphism. `leviRetraction` gives `r`. A second centre argument shows that
   `r` sends the action's image of every complement point to the identity,
   which gives equivariance on every test scheme.
2. `semisimpleNormalComplement_of_almostSimpleGeneration`
   (`Reductive/SemisimpleNormalComplementConstruction.lean`) proves
   `SemisimpleNormalComplementStatement.{u}` from
   `SemisimpleAlmostSimpleGenerationStatement.{u}`. Its complement is the full
   closed normal centralizer of the given subgroup.
3. `semisimpleAlmostSimpleGeneration_of_rootLines`
   (`Reductive/NormalRootDichotomyReduction.lean`) proves
   `SemisimpleAlmostSimpleGenerationStatement.{u}` from four statements:
   `NormalReductiveCenterStatement.{u}`, `SemisimpleRootGenerationStatement.{u}`,
   `AbsoluteRootVectorLineStatement.{u}` and `MaximalTorusConjugacyStatement.{u}`.
   It obtains the normal-root dichotomy from these and then argues by induction
   on the Lie dimension.
4. The four inputs are supplied as follows:
   - `normalReductiveCenter` (`Reductive/NormalCenterProof.lean`);
   - `semisimpleRootGenerationReduction`
     (`Reductive/RootGenerationReduction.lean`), applied to
     `rootRankOneFactorization`
     (`Rational/RootRankOneFactorizationProof.lean`) and to
     `algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
     solvableTorusQuotient`
     (`Absolute/MaximalTorusCentralizerFromQuotient.lean`,
     `Dynamic/CentralizerReductiveProof.lean`,
     `Absolute/SolvableTorusQuotientProof.lean`). The last term proves
     `AlgClosedMaximalTorusCentralizerStatement.{u}`, exactly as in
     `normalReductiveCenter`;
   - `absoluteRootVectorLine` (`Absolute/RootVectorLineProof.lean`);
   - `maximalTorusConjugacy` (`Absolute/MaximalTorusConjugacyProof.lean`).

Each leaf is an unconditional published theorem. The proof therefore keeps no
structural premise: neither the almost-simple decomposition, the existence of
a complement, nor root generation is assumed. All normality, commutation,
retraction and equivariance assertions concern the actual group schemes and
hold on every test scheme over `Spec k`.

As the reduction module records, its argument does not use the split-torus
hypothesis on `S` or the triviality of the centre of `G`. Both remain
hypotheses of the unchanged statement.

## Provenance

The theorem only composes published Library results. The statement's Markdown
gives the source: Conrad, Gabber and Prasad, *Pseudo-reductive Groups*, second
edition (2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`,
proof of Proposition 3.3.10(c), printed pp.113–114 / PDF pp.139–140. There,
after passing to adjoint quotients, the normal subgroup is a direct factor. The
composed modules prove that direct factor through Milne, *Algebraic Groups*
(2017), registered as `milne-2017-algebraic-groups`, Theorem 21.51, printed
pp.440–441 / PDF pp.456–457. Their own Markdown documents that route. The
implemented route uses the full scheme-theoretic centralizer as the
complement. It does not reproduce either printed argument verbatim.
