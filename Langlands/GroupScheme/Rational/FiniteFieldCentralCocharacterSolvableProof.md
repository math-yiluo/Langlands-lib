# Over a finite field, a group whose cocharacters are all central is solvable: proof

This module proves `Langlands.GroupScheme.finiteFieldCentralCocharacterSolvable`,
whose type is exactly `Langlands.GroupScheme.FiniteFieldCentralCocharacterSolvableStatement.{u}`
at an arbitrary universe `u`. Fix a finite field `k : Type u` and a group scheme `G`
over `Spec k` that is smooth, affine and has connected underlying space. Assume that
every cocharacter `χ : (Gm (Spec k)).toGrp ⟶ G` over `k` itself satisfies
`Dynamic.centralizer χ = ⊤`. Then `IsSolvableGroupScheme G` holds: the group of
`k̄`-points of the base change of `G` to the algebraic closure is solvable.

The theorem has no further hypotheses. The cocharacters stay over `k`, and the theorem
assumes no splitness, reductivity, characteristic restriction or supplied subgroup.

## Implemented proof

The proof is a single term:

```lean
finiteFieldCentralCocharacterSolvable_of parabolicDynamic finiteFieldQuasiSplit
```

It discharges the two premises of the published reduction with two published
unconditional proofs:

- `finiteFieldCentralCocharacterSolvable_of` (module
  `Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableReduction`)
  has type `ParabolicDynamicStatement.{u} → FiniteFieldQuasiSplitStatement.{u} →
  FiniteFieldCentralCocharacterSolvableStatement.{u}`.
- `parabolicDynamic` (module `Langlands.GroupScheme.Absolute.ParabolicDynamicProof`)
  proves `ParabolicDynamicStatement.{u}`. For a connected reductive group over a
  field, a closed subgroup is parabolic exactly when its range is the dynamic
  parabolic of a cocharacter over that field (Milne, Theorem 25.1).
- `finiteFieldQuasiSplit` (module `Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit`)
  proves `FiniteFieldQuasiSplitStatement.{u}`: every connected reductive group over
  a finite field is quasi-split.

## How the imported reduction argues

This module adds no new construction. For the reviewer, here is the route of the
imported reduction, as stated in its own Markdown and Lean:

1. A finite field is perfect. Over a perfect field,
   `nonempty_centralCocharacterReductiveQuotientData` takes the ground-field
   unipotent radical `U ⊆ G` (`unipotentRadicalExistence`) and an actual fppf quotient
   `G ⟶ Q` by it (`unipotentRadicalQuotient`). `perfectFieldPseudoReductive` shows
   that `Q` is connected reductive.
2. Every ground-field cocharacter of `Q` lifts to one of `G`
   (`exists_cocharacter_lift_of_perfectField_unipotent_kernel`, which takes the
   published stable-vector proof `RelativeRoot.splitUnipotentStableVectorSubgroup` as
   input). `Dynamic.central_cocharacters_of_fpqc_of_lifts` then carries the
   centrality hypothesis on `G` down to every ground-field cocharacter of `Q`. The
   package of these data is `CentralCocharacterReductiveQuotientData G`, and
   `centralCocharacterReductiveQuotient` chooses one.
3. Finite-field quasi-splitness (the premise discharged here by
   `finiteFieldQuasiSplit`) gives `IsQuasiSplit Q`.
   `IsQuasiSplit.isSolvableGroupScheme_of_central_cocharacters` (module
   `Rational.CentralCocharacterReduction`) then argues as follows. Quasi-splitness
   gives a solvable parabolic `k`-subgroup `B ⊆ Q`. The parabolic–dynamic
   comparison (the premise discharged here by `parabolicDynamic`) shows that `B`
   is the dynamic parabolic of some cocharacter over `k`. That cocharacter is
   central, so the inclusion `B ⟶ Q` is an isomorphism
   (`isIso_parabolic_of_central_cocharacters`). Hence `Q` is solvable.
4. `isSolvableGroupScheme_of_unipotent_fppfQuotient` (module
   `Absolute.SolvableQuotientExtension`) carries solvability from `Q` back to `G`
   across the unipotent kernel.

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), proof of
Proposition A.2.11 (finite-field case), argues along the same lines: over a finite
field the maximal reductive quotient is quasi-split, and a non-central cocharacter
would come from a nontrivial derived group. This proof takes that route only
through the published Library results named above.

## Imported Library inputs

- `Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableStatement`
  (the target statement).
- `Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableReduction`
  (`finiteFieldCentralCocharacterSolvable_of`).
- `Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit` (`finiteFieldQuasiSplit`).
- `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` (`parabolicDynamic`).

The development check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
