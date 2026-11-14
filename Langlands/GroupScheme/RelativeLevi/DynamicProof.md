# Dynamic parabolics, unipotent radicals and Levi subgroups over any base

Worker 591. This proof assembles published Library results to prove exactly
`Langlands.GroupScheme.DynamicRelativeLeviStatement.{u}`. It leaves the statement
and its imports unchanged, assumes no extra hypotheses, and works in every
universe `u` over an arbitrary scheme.

The source correspondence is that of
[`DynamicStatement`](DynamicStatement.md): Brian Conrad, *Reductive group schemes*
(2014), Example 5.2.2 on printed/PDF page 151, Corollary 5.2.5 on page 153, and
Definition 5.4.2 and the following paragraph on page 174. The original is registered
as `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
These pages were checked for this proof. The Lean proof uses the Library's proved
constructions and field theorems.

The implemented proof proceeds as follows.

1. Smoothness of the reductive ambient group implies local finite presentation.
   `dynamicBaseRepresentability` constructs closed representatives of the three
   dynamic functors. Uniqueness of representatives transfers closedness to the
   supplied `iP`, `iU` and `iZ`. `dynamicBaseSmoothConnected` supplies smoothness
   of their sources; closedness of `iP` also gives affineness over the base.
2. At each residue-field point, `IsReductive.isConnectedReductive_residueFiber`
   supplies a connected reductive ambient fibre. The representation hypothesis
   base-changes, and `Dynamic.parabolic_baseChange` identifies it with the dynamic
   functor of the actual pulled-back cocharacter. The published field theorem
   `AffineWeilParabolicRadicalTransport.isParabolicSubgroup_of_isRepresentedBy`
   proves the required parabolicity.
3. For every supplied factorization `r : U ⟶ P`, closedness follows from closedness
   of its composite with `iP`. The all-test-scheme lemma
   `Dynamic.range_unipotentRepresentative_isNormal` gives normality in `P`.
   At each geometric point, `IsReductive.isConnectedReductive_baseChange` and
   dynamic base change give the hypotheses of the field theorem
   `AffineWeilParabolicRadicalTransport.isGeometricUnipotentRadical_of_isRepresentedBy`.
   Its ground-field radical conjunct proves that this actual geometric fibre of
   `r` is a unipotent radical. Together with smoothness, these are exactly
   `IsRelativeUnipotentRadical r`.
4. For every supplied factorization `l : Z ⟶ P`, the same closed-factor argument
   gives closedness, and step 1 gives smoothness of `Z`. The inclusion of the
   unipotent functor in the parabolic functor constructs a compatible `r : U ⟶ P`.
   Step 3 makes it a relative unipotent radical. Finally,
   `Dynamic.isIso_subgroupMultiplication`, from
   [`Rational.LeviMultiplication`](../Rational/LeviMultiplication.md), proves that
   the actual multiplication `Z ×_S U ⟶ P` in the required Levi-first order is an
   isomorphism.

All representation equalities concern every test scheme, including nonreduced
ones. Neither a maximal torus nor a splitting, field, reducedness or Noetherian
hypothesis is added.
