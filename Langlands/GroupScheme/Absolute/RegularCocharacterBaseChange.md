# Borel subgroups through a split maximal torus: passage to the algebraic closure

Module `Langlands.GroupScheme.Absolute.RegularCocharacterBaseChange`. It is derived
infrastructure for clause 3 of `Langlands.GroupScheme.RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`): every Borel subgroup through a split maximal torus
`j : T ⟶ G` represents `P(ν ≫ j)` for some regular cocharacter `ν`. The module connects the
conjugacy argument over `k̄` (module `BorelDynamicConjugacy`) with the descent to `k`
(module `RegularCocharacterDescent`). Its main theorems are conditional on published structure
statements, which they take as hypotheses and do not prove.

Notation (local to the Lean file): `ac[k]` is `toAlgebraicClosure k : Spec k̄ ⟶ Spec k`, where
`k̄ = AlgebraicClosure k`, and `pt[k]` is `Spec k̄` as a test scheme over `Spec k`. A `k̄`-point
of a group `H` over `k` is a morphism `pt[k] ⟶ H.X` over `Spec k`.

## Points and solvability

- `isSolvableGroupScheme_baseChange_iff`: a group `H` over `k` is solvable exactly when its
  base change `H_{k̄}` is. By definition, `IsSolvableGroupScheme H` says that the group of
  rational points of `H_{k̄}` is solvable. Proof: the Library lemma
  `isSolvableGroupScheme_iff_isSolvable_points` (module `Absolute.RationalPointClosureSolvable`)
  over the algebraically closed field `k̄`: for such a field, solvability of a group scheme is
  solvability of its group of rational points.
- `IsBorelSubgroup.isAdmissible_baseChange`: if `G` is affine over `k` and `i : B ⟶ G` is a
  Borel subgroup, then `i_{k̄}` is admissible in the sense of `BorelExistence.IsAdmissible`:
  a closed subgroup (`IsClosedSubgroup.baseChange`) whose source is smooth, connected
  (`connectedSpace_baseChange_of_smooth_affine`) and solvable (previous lemma).

## Cocharacters

`baseChangeCocharacter_comp`: for `χ : 𝔾_m ⟶ H` and `j : H ⟶ G`, the base change of `χ ≫ j`
is the base change of `χ` followed by `j` base-changed. This is functoriality of base change.

## Passage to the algebraic closure

`exists_cocharacter_algebraicClosurePoints`. Hypotheses:

- `hBC : BorelConjugacyStatement`, `hTC : MaximalTorusConjugacyStatement`;
- `hFE : ConnectedReductiveFieldExtensionStatement` (connected reductive groups stay connected
  reductive after field extension);
- `hMT : MaximalTorusBaseChangeStatement` (a closed torus is maximal exactly when its base
  change is; Milne, Theorem 17.82);
- `G` connected reductive over `k`, `j : T ⟶ G` a maximal torus with `T` split, `i : B ⟶ G` a
  Borel subgroup and `f : T ⟶ B` with `f ≫ i = j`;
- a cocharacter `ν₀` of `T_{k̄}` and a Borel subgroup `i₀ : P₀ ⟶ G_{k̄}` representing
  `Dynamic.parabolic (groupHom ν₀ ≫ j_{k̄})`.

Conclusion: there is a cocharacter `ν` of `T` such that every `k̄`-point of `B` maps under `i`
into `P(ν ≫ j)(pt[k])`, and the group `P(ν ≫ j)(pt[k])` is solvable. These are exactly the
hypotheses `hpt` and `hsol` of `isRegular_isRepresentedBy_of_algebraicClosurePoints` in
`RegularCocharacterDescent`.

Proof:

1. By `hFE`, `G_{k̄}` is connected reductive. By `hMT`, `j_{k̄}` is a maximal torus.
2. `i_{k̄}` is admissible, so the Library theorem
   `BorelExistence.exists_isBorelSubgroup_containing` gives a Borel subgroup `i' : B' ⟶ G_{k̄}`
   and `g : B_{k̄} ⟶ B'` with `g ≫ i' = i_{k̄}`. Then `j_{k̄}` factors through `i'` by
   `f_{k̄} ≫ g`.
3. `exists_isRepresentedBy_parabolic_of_isBorelSubgroup` (module `BorelDynamicConjugacy`)
   gives an automorphism `σ` of `T_{k̄}` such that `i'` represents
   `P((ν₀ ≫ σ) ≫ j_{k̄})`.
4. Since `T` is split, the cocharacter `ν₀ ≫ σ` of `T_{k̄}` is the base change of a cocharacter
   `ν` of `T` (`IsSplitTorus.existsUnique_baseChangeCocharacter`, module
   `Torus.SplitLatticeBaseChange`). By `baseChangeCocharacter_comp` and
   `Dynamic.parabolic_baseChange`, the points of `i'` are the base change of `P(ν ≫ j)`.
5. Containment: a `k̄`-point `x` of `B` is `baseChangePointsEquiv` of a rational point `x'` of
   `B_{k̄}`, and `x ≫ i` corresponds to `x' ≫ i_{k̄} = (x' ≫ g) ≫ i'`, a point of `i'`.
6. Solvability: `B'` is solvable, so by `isSolvableGroupScheme_iff_isSolvable_points` its group of
   rational points is solvable. That group surjects onto the rational points of `i'`, which are
   the rational points of the base change of `P(ν ≫ j)`. These are isomorphic to
   `P(ν ≫ j)(pt[k])` by `SubgroupFunctor.baseChangeCarrierEquiv`.

## The conditional clause 3

`exists_isRegular_isRepresentedBy_of_isBorelSubgroup`. Hypotheses: those of
`exists_cocharacter_algebraicClosurePoints` (without `ν₀` and `i₀`), the hypotheses `hLie`,
`hSm`, `hCo`, `hNeg`, `hobs` of `isRegular_isRepresentedBy_of_algebraicClosurePoints`
(`DynamicLieStatement`, `DynamicSmoothStatement`, `DynamicConnectedStatement`,
`RelativeRootNegationStatement`, `RankOneSolvableObstructionStatement`), and

- `h1`: clause 1 of `RegularCocharacterBorelStatement` over every algebraically closed field
  `K`: for `G` connected reductive over `K`, a maximal torus `j : T ⟶ G` with `T` split, a
  regular cocharacter `ν` of `T` and a closed subgroup `i : B ⟶ G` representing `P(ν ≫ j)`,
  the subgroup `i` is a Borel subgroup.

Conclusion: for `G`, `j`, `i`, `f` as above over an arbitrary field `k`, there is a regular
cocharacter `ν` of `T` (`IsRegularCocharacter j ν`) such that `i` represents
`Dynamic.parabolic (groupHom ν ≫ j)`. This is clause 3 of the target, up to the hypotheses.

Proof: `T_{k̄}` is split (`IsSplitTorus.baseChange`), and its weights in `G_{k̄}` have finite
support (`IsSplitTorus.finite_weightSupport`), so it has a regular cocharacter `ν₀`
(`IsSplitTorus.exists_regularCocharacter`). The closed subgroup
`Dynamic.Affine.parabolicHom` representing `P(ν₀ ≫ j_{k̄})` is a Borel subgroup by `h1` over
`K = k̄`. Then `exists_cocharacter_algebraicClosurePoints` supplies `ν` with `hpt` and `hsol`,
and `isRegular_isRepresentedBy_of_algebraicClosurePoints` concludes.

## Provenance

Milne, *Algebraic Groups* (2017), Theorem 21.32 (statement printed p.434, PDF p.450; proof
printed pp.434–435, PDF pp.450–451), passes from `k` to `k̄`: a Borel subgroup of `G` containing
`T` becomes one of `G_{k̄}` containing `T_{k̄}`, which is `P(λ)` for a regular `λ` by the
algebraically closed case, and the cocharacters of the split torus `T` and of `T_{k̄}` agree.
Milne's Borel subgroups over `k` are those that become Borel subgroups over `k̄`. The published
`IsBorelSubgroup` is maximality among subgroups defined over `k`, so this module does not use
that `B_{k̄}` is itself a Borel subgroup. Instead it places `B_{k̄}` in some Borel subgroup `B'`
of `G_{k̄}`, identifies `B'` with a dynamic parabolic, and leaves the identification of `B`
with `P(ν ≫ j)` to the descent in `RegularCocharacterDescent`, which uses the published
maximality over `k`. The solvability lemmas over algebraically closed fields are elementary
and internal to this module.

`baseChangeCocharacter_comp` reuses the identical `Dynamic.baseChangeCocharacter_comp` from `SplitTorusDynamicDescent`.
