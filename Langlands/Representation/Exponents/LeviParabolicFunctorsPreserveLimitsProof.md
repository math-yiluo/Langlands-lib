# Proof of limit and colimit preservation by the normalized parabolic functors

Author: Worker 4814, task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`. Module
`Langlands.Representation.Exponents.LeviParabolicFunctorsPreserveLimitsProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The theorem `leviParabolicFunctorsPreserveLimits` proves the published statement
`LeviParabolicFunctorsPreserveLimitsStatement.{u, v}` (module
`Langlands.Representation.Exponents.LeviParabolicFunctorsPreserveLimitsStatement`). This is
the Corollary of Renard 2026, VI.1.2 (printed p.136 / PDF p.142): normalized parabolic
induction `i_P^G` preserves limits and colimits, and normalized parabolic restriction
`r_P^G` preserves colimits, for diagrams indexed by categories `J : Type v` with morphisms in
`Type v`. No hypothesis beyond the statement's is used. Compactness of the parabolic
quotient is imported from its published proof, not assumed.

The source deduces the Corollary from the adjunction of the Proposition of VI.1.2 and, for
colimits under induction, from compactness of `P\G`. The Lean proof does not use an
adjunction between the two functors, whose carrier universes differ. It assembles three
published preservation results, each proved directly for the normalized functors of an
abstract semidirect decomposition and transported to `M(F)`.

## The colimit lemma for induction

`leviInductionFunctor_preservesColimits_of_compactSpace` works over a field `k : Type u` with
`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`
and a group scheme `G` with `[IsAffineHom G.X.hom]`, whose rational points carry
`RationalPointFamily.pointTopology` and the instances
`[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`.
It takes `hG : IsConnectedReductive G`, the actual parabolic data `p`, `l`, `r`, `hp`, `hr`,
`hl`, `hmul` of the statement, and an instance
`[CompactSpace (Induction.LeftQuotient (pointImage p))]`. It concludes
`PreservesColimitsOfSize.{v, v} (leviInductionFunctor.{u, v} p l r hp hr hl hmul)` for the
topology `leviPointTopology l hl` on `rationalPoints M`.

Proof. It installs `IsAffine G.X.left` (from `isAffine_of_isAffineHom`), the smoothness
`hG.smooth`, and `T2Space (rationalPoints G)` from the published `rationalPoint_t2Space k G`.
The published `Langlands.Aubert.General.normalizedInductionFunctor_preservesColimits`
(module `Langlands.Representation.Aubert.General.InductionColimits`) gives
`PreservesColimitsOfSize.{v, v}` for normalized induction from the Levi image, with these
inputs:

- the decomposition `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul`
  of `pointImage p`, and the closedness
  `isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup` of the radical
  image;
- cofinal compact open subgroups of `G(F)`: the published
  `Langlands.Plancherel.rationalPoint_compactOpenCofinal k G`;
- closedness of the parabolic image: `isClosed_pointImage p hp.isClosedSubgroup`;
- continuity of the Levi projection: the published
  `continuous_projection_pointImage p l r hp hl hr hmul`;
- the compact quotient instance.

By definition `leviInductionFunctor p l r hp hr hl hmul` is
`SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ normalizedInductionFunctor _ _`.
The pull-back functor is the functor of the published equivalence
`SmoothRep.pullbackEquivalence (leviPointsEquiv p l hp hl).symm`, so it preserves all
colimits. Instance search then gives preservation for the composite.

## The conditional assembly

`leviParabolicFunctorsPreserveLimits_of_quotientCompact` derives
`LeviParabolicFunctorsPreserveLimitsStatement.{u, v}` from
`ArbitraryParabolicQuotientCompactStatement.{u}`. After introducing the field, `G`, `hG`, the
instance `hG.isAffineHom`, the topology on `rationalPoints G`, the two instance hypotheses and
the parabolic data, it obtains
`CompactSpace (Induction.LeftQuotient (pointImage p))` by applying the compactness statement
to `k`, `G`, `hG`, `P`, `p`, `hp`. It then proves the three conjuncts:

1. limits under induction: the published `leviInductionFunctor_preservesLimits p l r hp hr hl
   hmul` (module `Langlands.Representation.Exponents.LeviInductionLimits`);
2. colimits under induction: `leviInductionFunctor_preservesColimits_of_compactSpace hG p l r
   hp hr hl hmul` above;
3. colimits under restriction: the published instance
   `leviJacquetFunctor_preservesColimits p l r hp hr hl hmul` (module
   `Langlands.Representation.Aubert.General.JacquetColimits`).

## The theorem

`leviParabolicFunctorsPreserveLimits` has type exactly
`LeviParabolicFunctorsPreserveLimitsStatement.{u, v}` and takes no hypotheses. Its proof is
`leviParabolicFunctorsPreserveLimits_of_quotientCompact` applied to the published theorem
`Langlands.Aubert.General.RepresentedParabolic.arbitraryParabolicQuotientCompact`, whose
type is `ArbitraryParabolicQuotientCompactStatement.{u}` (module
`Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof`). That theorem
proves compactness of `Induction.LeftQuotient (pointImage p)` for every represented
parabolic `p` of a connected reductive group over a nonarchimedean local field, in the
canonical point topology. So the compactness used in the conditional assembly is proved, not
assumed.
