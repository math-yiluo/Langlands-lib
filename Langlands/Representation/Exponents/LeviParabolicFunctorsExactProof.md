# Proof of exactness of normalized parabolic induction and restriction

Author: Worker 16, task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`. Module
`Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The theorem `leviParabolicFunctorsExact` proves the published statement
`LeviParabolicFunctorsExactStatement.{u, v}` (module
`Langlands.Representation.Exponents.LeviParabolicFunctorsExactStatement`). This is the
exactness part of the Proposition of Renard 2026, VI.1.2: normalized parabolic induction
`i_P^G` and normalized Jacquet restriction `r_P^G` send every actual short exact sequence of
smooth representations to a short exact sequence. No hypothesis beyond the statement's is
used. In particular the compact-subgroup property of the radical image is proved, not
assumed.

The source derives the proposition from the unnormalized Theorem of VI.1.1. The Lean proof
instead applies two published exactness theorems for the normalized functors of an abstract
semidirect decomposition, and checks their hypotheses for the actual rational points.

## Helper module

The Jacquet part uses `Langlands.Representation.Exponents.LeviRadicalCompactSubgroups`,
submitted with this proof together with the modules it imports,
`Langlands.GroupScheme.Rational.UnipotentCompactSubgroups` and
`Langlands.Algebra.GradedHopf.TrivialGrading`. The same three modules are also submitted
with the Frobenius reciprocity proof `LeviFrobeniusReciprocityProof`. Each has its own
Markdown note. The theorem used here is
`isLimitOfCompactSubgroups_pointImage_radical p r hp hr`: for a closed subgroup
`p : P ⟶ G` and a unipotent radical `r : U ⟶ P`, the literal rational-point image
`pointImage (r ≫ p)` is a limit of compact subgroups
(`Jacquet.Localization.IsLimitOfCompactSubgroups`).

## The proof

After introducing the field, `G` and `hG`, the proof installs the same instances as the
statement: `hG.isAffineHom` and the topology `RationalPointFamily.pointTopology` on
`rationalPoints G`. It then introduces the two instance hypotheses on `G(F)` and the
parabolic data `p`, `l`, `r`, `hp`, `hl`, `hr`, `hmul`. It installs, as the statement does,
`hl.isConnectedReductive.isAffineHom`, the topology `leviPointTopology l hl` on
`rationalPoints M`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and
`leviPoints_nonarchimedeanGroup p l hp hl`. It names the decomposition
`hdec := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul` of
`pointImage p` and the closedness proof
`hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup` of the
radical image. The published `inductionFunctor` and `jacquetFunctor` of the
represented-parabolic interface are, by definition, the normalized functors of this
decomposition. The two conjuncts are then proved separately.

1. Induction. `leviInductionFunctor … .map f` is, by definition, the published induction
   functor applied to `(SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).map f`.
   Pull-back keeps the underlying linear maps. So the hypothesis `hfg` is, by definition,
   short exactness of the pulled-back maps. The published
   `Langlands.Aubert.General.normalizedInductionFunctor_map_isShortExact` (module
   `Langlands.Representation.Aubert.General.AlternatingOperator`) concludes. Its
   hypotheses are supplied as follows.
   - `T2Space (rationalPoints G)`: the published `rationalPoint_t2Space k G`, from
     `T2Space k`.
   - Cofinal compact open subgroups: the published
     `Langlands.Plancherel.rationalPoint_compactOpenCofinal k G`. It needs `G.X.left`
     affine, which follows from `hG.isAffineHom` by `isAffine_of_isAffineHom`, and
     `G.X.hom` locally of finite type, which follows from the smoothness `hG.smooth`.
   - Closedness of the parabolic image: `isClosed_pointImage p hp.isClosedSubgroup`.
   - Continuity of the Levi projection of `hdec`: the published
     `continuous_projection_pointImage p l r hp hl hr hmul`.
2. Jacquet restriction. `leviJacquetFunctor … .map f` is, by definition, the pull-back
   along `leviPointsEquiv p l hp hl` of the published Jacquet functor's image of `f`.
   Pull-back keeps the underlying linear maps, so the required short exactness is, by
   definition, that of the published Jacquet functor's images of `f` and `g`. The published
   `Langlands.Aubert.General.jacquetFunctor_map_isShortExact` (same module) proves it from
   `hdec`, `hU`, `hfg` and the limit-of-compact-subgroups property
   `isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1`. Here `hr.1`
   is the `IsUnipotentRadical` part of `LeviSubgroup.IsGeometricUnipotentRadical`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
