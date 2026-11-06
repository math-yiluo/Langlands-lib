# Borel subgroups from regular cocharacters: assembly

Module `Langlands.GroupScheme.Absolute.RegularCocharacterBorel`. It assembles the three clauses
of `Langlands.GroupScheme.RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`) from the conditional lemmas of
`RegularCocharacterMaximal`, `RegularCocharacterParabolic` and `RegularCocharacterBaseChange`.
Its theorems differ in how many structure statements they take as hypotheses:

- `isBorelSubgroup_of_isRepresentedBy_parabolic` and `regularCocharacterBorelStatement_of_inputs`
  are conditional. They take published structure statements as hypotheses and do not prove them.
- `centralizer_comp_eq_range_of_isRegular` and
  `isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular` take no structure statement
  as a hypothesis. They use the Library proofs `genericCentralizer` and `maximalTorusCentralizer`.
- `regularCocharacterBorelStatement_of_relativeRootNegation` takes only
  `RelativeRootNegationStatement`, and `regularCocharacterBorelStatement_of_rootDatumExistence`
  takes only `RootDatumExistenceStatement`. Library proofs discharge every other input.

The proof of the target, `regularCocharacterBorel` in module
`Absolute.RegularCocharacterBorelProof`, applies
`regularCocharacterBorelStatement_of_relativeRootNegation` to the Library proof
`relativeRootNegation`.

## Clause 1

`isBorelSubgroup_of_isRepresentedBy_parabolic`. Hypotheses: `DynamicLieStatement`,
`DynamicSmoothStatement`, `DynamicConnectedStatement`, `LieSubgroupEqualityStatement`,
`RelativeRootNegationStatement`, `RankOneSolvableObstructionStatement`; `G` connected reductive
over a field `k`; `j : T ⟶ G` a maximal torus with `T` split; a cocharacter `ν` of `T`; a closed
subgroup `i : B ⟶ G` representing `Dynamic.parabolic (groupHom ν ≫ j)`; and solvability of `B`
(`IsSolvableGroupScheme B`). Conclusion: `IsBorelSubgroup i`. Regularity of `ν` is not used
here; it enters through the solvability hypothesis in the next theorem.

Proof: `B` is smooth by `DynamicSmoothStatement` and connected by `DynamicConnectedStatement`,
since `G` is smooth, affine and connected. For maximality, let `i' : B' ⟶ G` be a smooth
connected solvable closed subgroup and `f : B ⟶ B'` with `f ≫ i' = i`. The torus `j` factors
through `i` by some `fT`, because the image of `T` centralizes `ν ≫ j` and the centralizer lies
in the dynamic parabolic. Then `(fT ≫ f) ≫ i' = j`, so `RankOneSolvableObstructionStatement`
applies to `B'`: no root `α` has nonzero vectors of both `𝔤_α` and `𝔤_{-α}` in the image of
`Lie(B')`. Roots are stable under negation (`neg_mem_roots_of_relativeRootNegation`). Hence
`isIso_of_comp_eq_of_isRepresentedBy_parabolic` shows that `f` is an isomorphism.

## Solvability from the centralizer proofs

`centralizer_comp_eq_range_of_isRegular`. Hypotheses: `G` connected reductive over a field,
`j : T ⟶ G` a maximal torus with `T` split, and `ν` a regular cocharacter. Conclusion:
`Dynamic.centralizer (groupHom ν ≫ j) = SubgroupFunctor.range j`. Proof: a split maximal torus is
a maximal split torus (`IsMaximalTorus.isMaximalSplitTorus`), and regular means generic, because
`IsGenericCocharacter` and `IsRegularCocharacter` both say `⟨α, ν⟩ ≠ 0` for every root `α`
(`relativeRoots` is defined as `roots`). Then the Library proof `genericCentralizer` (module
`Rational.GenericCentralizerProof`) gives `Z(ν ≫ j) = torusCentralizer j`, and the Library proof
`maximalTorusCentralizer` (module `Absolute.MaximalTorusCentralizerProof`) gives
`torusCentralizer j = range j`.

`isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular`. Same setting, with
`i : B ⟶ G` representing `P(ν ≫ j)`; no structure statement is assumed. Conclusion: `B` is solvable. Proof: by the previous lemma `Z(ν ≫ j) ≤ range j`, so the Library
lemma `isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_le_range` (module
`Absolute.RegularCocharacterSolvable`, by Worker 303) applies with `χ = ν ≫ j`. `G` is locally of
finite type because it is smooth. This lemma yields the hypothesis `hsolv` of the assembled
statements below.

## The assembled statement

`regularCocharacterBorelStatement_of_inputs` proves `RegularCocharacterBorelStatement` from the
six hypotheses above, together with `BorelConjugacyStatement`, `MaximalTorusConjugacyStatement`,
`ConnectedReductiveFieldExtensionStatement`, `MaximalTorusBaseChangeStatement` and

- `hsolv`: over every field, for `G` connected reductive, `j : T ⟶ G` a maximal torus with `T`
  split and `ν` a regular cocharacter, every closed subgroup `i : B ⟶ G` representing
  `P(ν ≫ j)` has `B` solvable.

Proof: clause 1 is the previous theorem with `hsolv`. Clause 2 is
`regularCocharacterBorel_parabolic_eq_iff` (module `RegularCocharacterParabolic`). Clause 3 is
`exists_isRegular_isRepresentedBy_of_isBorelSubgroup` (module `RegularCocharacterBaseChange`),
whose hypothesis `h1` (clause 1 over algebraically closed fields) is supplied by clause 1.

`regularCocharacterBorelStatement_of_relativeRootNegation` proves
`RegularCocharacterBorelStatement` from `RelativeRootNegationStatement` alone. Proof:
`regularCocharacterBorelStatement_of_inputs` with the
Library proofs `dynamicLie`, `dynamicSmooth`, `dynamicConnected`, `lieSubgroupEquality`,
`rankOneSolvableObstruction` (module `Absolute.RankOneSolvableProof`),
`connectedReductiveFieldExtensionStatement` (module `Reductive.FieldExtensionProof`),
`borelConjugacy` (module `Absolute.BorelConjugacyProof`), `maximalTorusConjugacy` (module
`Absolute.MaximalTorusConjugacyProof`) and `maximalTorusBaseChange` (module
`Torus.MaximalBaseChangeProof`), and with `hsolv` given by
`isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_isRegular`.

`regularCocharacterBorelStatement_of_rootDatumExistence` proves the same conclusion from
`RootDatumExistenceStatement` instead of `RelativeRootNegationStatement`: the Library reduction
`relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus` (module
`Rational.AbsoluteRootRestriction`) derives negation stability from root-datum existence and the
Library proofs `connectedReductiveFieldExtensionStatement` and `maximalTorusBaseChange`.

## Provenance

Milne, *Algebraic Groups* (2017): clause 1 is Proposition 21.29 (printed p.433, PDF p.449;
maximality via Lemma 21.28 on rank one), clause 2 is part of Theorem 21.32 and its proof, and
clause 3 is the surjectivity part of Theorem 21.32 (printed pp.434–435, PDF pp.450–451). The
route here differs from Milne's as described in the Markdown of the three source modules. In
particular, maximality uses the Lie-algebra criterion `LieSubgroupEqualityStatement` together
with the rank-one obstruction in Lie form. Milne uses Borel subgroups of rank-one centralizers.
The solvability hypothesis `hsolv` corresponds to Milne's argument in 21.29 that `P(λ)` is
solvable because `Z(λ) = T` and `U(λ)` is unipotent. The centralizer proofs used are those of
Milne, Corollary 17.84 (`MaximalTorusCentralizerStatement`), and Borel–Tits 4.15 a) / Milne 25.6
(`GenericCentralizerStatement`).
