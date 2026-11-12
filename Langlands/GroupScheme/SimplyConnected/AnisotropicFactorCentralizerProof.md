# Anisotropic almost-simple factors centralize the maximal split torus: proof

Authors: Worker 4904.

Steps 2 and 3 below reuse the argument of the conditional reduction that
Worker 1326 wrote in the previous project instance. It is kept in this
task's shared draft. That worker has no identity in the current instance,
so the work is acknowledged here instead of in a coauthor list.

The theorem `Langlands.GroupScheme.simplyConnectedAnisotropicFactorCentralizer`
has type exactly
`Langlands.GroupScheme.SimplyConnectedAnisotropicFactorCentralizerStatement.{u}`,
from `Langlands.GroupScheme.SimplyConnected.AnisotropicFactorCentralizerStatement`,
at arbitrary universe `u`. So for every field `k : Type u`, every simply
connected `G` over `Spec k`, every `i : S.toGrp ⟶ G` with
`IsMaximalSplitTorus i`, and every `a : A ⟶ G` with `IsAlmostSimple A`,
`IsClosedSubgroup a`, `(SubgroupFunctor.range a).IsNormal` and
`IsAnisotropic A`, it proves `SubgroupFunctor.range a ≤ torusCentralizer i`
on every test scheme. The theorem has no hypothesis besides those of the
statement. The field, its characteristic and `G` are arbitrary; `G` is not
assumed split, quasi-split or isotropic.

## Implemented proof

The proof has three steps. Each step applies results already proved in the
Library.

1. **Normal complements over an arbitrary field.** The proof first obtains
   `hComplement : SemisimpleNormalIsogenyComplementStatement.{u}` without
   assuming it. It applies `semisimpleNormalIsogenyComplement_of_generation`
   (module `Reductive.NormalIsogenyComplementGeneration`) to a proof of
   `SemisimpleAlmostSimpleGenerationStatement.{u}`. That proof is
   `semisimpleAlmostSimpleGeneration_of_rootLines` (module
   `Reductive.NormalRootDichotomyReduction`), applied to these four Library
   theorems:
   - `normalReductiveCenter` (module `Reductive.NormalCenterProof`);
   - `semisimpleRootGenerationReduction rootRankOneFactorization
     (algClosedMaximalTorusCentralizer_fromQuotient
     dynamicCentralizerReductive solvableTorusQuotient)`, which proves
     `SemisimpleRootGenerationStatement`. The modules are
     `Reductive.RootGenerationReduction`,
     `Rational.RootRankOneFactorizationProof`,
     `Absolute.MaximalTorusCentralizerFromQuotient`,
     `Dynamic.CentralizerReductiveProof` and
     `Absolute.SolvableTorusQuotientProof`;
   - `absoluteRootVectorLine` (module `Absolute.RootVectorLineProof`);
   - `maximalTorusConjugacy` (module `Absolute.MaximalTorusConjugacyProof`).

   The published `Adjoint.NormalEquivariantRetractionProof` and
   `Rational.SemigroupComparisonProof` build the same proof of almost-simple
   generation. This step gives the normal-subgroup part of Milne's
   Theorem 21.51 over an arbitrary field. Its hypotheses are a semisimple `G`
   and a smooth connected closed normal subgroup `H`. Its conclusion is a
   semisimple closed normal complement `K` whose points commute with those
   of `H` on every test scheme, such that the multiplication `H ⊗ K ⟶ G` is
   a central isogeny.

2. **A retraction onto `A`.** The proof applies
   `IsSimplyConnected.exists_normalFactorRetraction_of_complement` (module
   `SimplyConnected.NormalFactorRetraction`) to `hG`, `hComplement` and `a`.
   It uses `ha`, `hn`, and the smoothness and connectedness of `A`, which
   come from `hA.isSemisimple.isConnectedReductive`. The result is a
   homomorphism `p : G ⟶ A`. For every test scheme `T`, `h : T ⟶ A.X` and
   `g : T ⟶ G.X` with `g ≫ p.hom.hom = 1`, the points `h ≫ a.hom.hom` and `g`
   commute. In that module, simple connectedness makes the central-isogeny
   multiplication `A ⊗ K ⟶ G` an isomorphism, and `p` is its projection to
   `A`. The proof does not use the section identity `a ≫ p = 𝟙 A` that also
   comes with `p`.

3. **The split torus lies in the kernel.** `A` is affine over `k`
   (`hA.isSemisimple.isConnectedReductive.isAffineHom`) and anisotropic. The
   source of `i` is a split torus, by the first component of
   `hi.isSplitSubtorus`. The proof concludes with
   `IsAnisotropic.range_le_torusCentralizer_of_kernel_commutes` (module
   `Rational.AnisotropicKernelCentralizer`). By
   `IsAnisotropic.hom_eq_zero_of_isSplitTorus`, that theorem makes the
   composite `i ≫ p : S.toGrp ⟶ A` trivial. So every point `i(t)` of the
   torus over every test scheme lies in the kernel of `p`. There it commutes
   with every point of `A`, also after restriction along any morphism of test
   schemes. This is the inequality `SubgroupFunctor.range a ≤
   torusCentralizer i`.

The proof uses only the split-torus part of `IsMaximalSplitTorus i`, not
maximality. It does not use that `i` is a closed immersion.

## Relation to the literature

The statement's Markdown gives a derivation from Milne, *Algebraic Groups*
(2022), Theorem 21.51 and the fact that a quotient of a split torus is split
(printed p. 236). It also cites Prasad–Raghunathan (1985), §1.5. The Lean
proof follows the same route:

- Step 1 is the Library's proof of the structural part of Theorem 21.51.
- Step 2 is the product decomposition `G ≅ A × G'`, obtained from simple
  connectedness.
- In step 3, the split-image theorem behind
  `IsAnisotropic.hom_eq_zero_of_isSplitTorus` stands in for "quotients of
  split tori are split".

The proof cites no literature result without its Lean proof.

## Remark

Step 1 proves `SemisimpleNormalIsogenyComplementStatement.{u}`
unconditionally, and this module uses that only as a local `have`. That
proposition is also the target of a separate proof task. This module states
no top-level theorem for it.
