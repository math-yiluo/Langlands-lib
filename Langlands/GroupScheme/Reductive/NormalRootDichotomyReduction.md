# Normal-root dichotomy from actual root lines and maximal-torus conjugacy

This internal reduction proves the exact
`SemisimpleNormalRootDichotomyStatement` under four explicit premises:
`NormalReductiveCenterStatement`, `SemisimpleRootGenerationStatement`,
`AbsoluteRootVectorLineStatement`, and `MaximalTorusConjugacyStatement`.
Every premise and conclusion uses the same arbitrary universe. Fields are
algebraically closed, with no characteristic restriction. No proof of any
of the four premises is supplied here.

The conclusion concerns an actual semisimple group `G`, a split maximal
torus `t : T ⟶ G`, and a smooth connected closed normal subgroup
`h : H ⟶ G`. Each intrinsic adjoint root subgroup functor of `t` lies
either in the full range of `h` or in the full fixed subgroup of conjugation
by `H`. The latter is the full centralizer of `H`: membership requires
commutation on every test scheme and every refinement.

The implemented proof first uses the normal full-center premise and the
published `IsSemisimple.of_normalSubgroup_of_normalReductiveCenterStatement`
to make `H` semisimple. It converts the global maximal-torus conjugacy
premise to `MaximalToriAreConjugate G` using the existing equivalence between
group-scheme and commutative-group-scheme conjugacy. The compatible-torus
construction then supplies a maximal torus `s : S ⟶ H` and a closed
homomorphism `f : S ⟶ T` with `f ≫ t = s ≫ h`. Algebraic closedness makes
`s` split through the published finite Galois splitting theorem.

Apply `RelativeRoot.subgroup_le_range_or_fixedSubgroup` to this exact square.
Its first alternative is the required containment in `H`. In the second
alternative, the intrinsic ambient root centralizes `s ≫ h`. The root-line
premise supplies an actual closed representative `a : U ⟶ G` of this same
root functor, with `U` a vector group of dimension one. Full normality of
`H` supplies normalization by `U` on every test.

Apply `range_le_centralizer_of_rootGeneration_vectorLines` to `a` and `h`.
Its represented vector-line hypotheses for the roots of `H` come from the
same global root-line premise, now applied to `H` and `s`. The explicit
root-generation premise extends root fixedness to the entire semisimple
group `H`. The result is full centralization of `H` by the range of `a`.
The exact representing equality identifies that range with the original
ambient root functor, giving the second required alternative.

`normalRootPlacementOfRootLines` retains the geometric output as an actual
map. Given any representative `a : U ⟶ G` of the selected root functor and
any representative `c : C ⟶ G` of the full centralizer, it returns either
`f : U ⟶ H` with `f ≫ h = a` or `f : U ⟶ C` with `f ≫ c = a`.
The represented-subgroup lift constructs each map from the corresponding
natural subgroup inclusion, and its composite theorem supplies the stated
equality of actual morphisms. No closedness or smoothness of `C` is assumed.

`semisimpleAlmostSimpleGeneration_of_rootLines` passes the resulting
normal-root dichotomy to the published dimension-induction assembly
`semisimpleAlmostSimpleGeneration_of_actualRoots`. It derives the exact
`SemisimpleAlmostSimpleGenerationStatement` under the same four explicit
structural premises.

The provenance is an internal composition of the imported constructions.
It retains the original intrinsic root functors, actual normal inclusion,
and all-test centralizer. In particular it assumes no abstract root-system
partition as a replacement for the geometric assertions. This reduction
does not prove the unconditional normal-root dichotomy or the host
`SemisimpleAlmostSimpleGenerationStatement`. The structural premises
remain separate proof obligations.
