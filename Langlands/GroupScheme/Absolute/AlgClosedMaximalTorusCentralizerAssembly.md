# Self-centralizing maximal tori over an algebraically closed field, from structural inputs

Worker 303. This module reduces the algebraically closed case of Milne
Proposition 17.61(a), `AlgClosedMaximalTorusCentralizerStatement` (module
`Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction`), to three
published propositions that are not yet proved:

- `DynamicCentralizerReductiveStatement` (module
  `Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement`): a closed
  subgroup representing the dynamic centralizer of a cocharacter of a
  connected reductive group is connected reductive;
- `NoTorusUnipotentStatement` (module
  `Langlands.GroupScheme.Torus.NoTorusUnipotentStatement`, Milne 17.81): a
  smooth connected affine group that receives only trivial homomorphisms from
  tori is unipotent;
- `SolvableTorusQuotientStatement` (module
  `Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement`, Milne
  16.33(a),(c)): over an algebraically closed field, a smooth connected
  solvable affine group `H` has a smooth connected normal unipotent closed
  subgroup `U` whose fppf quotient `H/U` is a split torus.

It then combines this reduction with Worker 1391's published
`maximalTorusCentralizer_of_centralMaximalTorusBaseChange` and the Library's
reductions of the central case of Milne 17.82. The result derives the
published target `MaximalTorusCentralizerStatement` (Milne Corollary 17.84)
from the same three propositions. The module proves none of the three, and so
proves neither `AlgClosedMaximalTorusCentralizerStatement` nor
`MaximalTorusCentralizerStatement` unconditionally.

Milne 16.43, in the form `CentralMaximalTorusQuotientStatement`, is used
through its Library proof `centralMaximalTorusQuotientStatement` (module
`Langlands.GroupScheme.Torus.CentralMaximalQuotientProof`) and is not an
assumption.

## Main declarations

All are in namespace `Langlands.GroupScheme`, at an arbitrary universe `u`.

- `isSolvable_points_of_isFppfQuotient`: let `k` be a field, `M`, `Q` group
  schemes over `Spec k`, `T` a commutative group scheme over `Spec k`,
  `s : T ⟶ M`, and `q : M ⟶ Q` with
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q`. If the group of
  points `U ⟶ Q.X` is solvable for a test scheme `U` over `Spec k`, so is
  `U ⟶ M.X`. No algebraic closedness is needed.
- `IsConnectedReductive.isIso_of_isCentral_of_isMaximalTorus`: let `k` be
  algebraically closed, and assume `NoTorusUnipotentStatement.{u}` and
  `SolvableTorusQuotientStatement.{u}`. If `M` is a connected reductive group
  over `Spec k` and `s : T ⟶ M` is a central (`IsCentral s`) maximal torus
  (`IsMaximalTorus s`), then `s` is an isomorphism (`IsIso s`).
- `AlgClosedMaximalTorusCentralizerReductionStatement.{u}`: a `def` of type
  `Prop`, the implication

  ```lean
  DynamicCentralizerReductiveStatement.{u} → NoTorusUnipotentStatement.{u} →
    SolvableTorusQuotientStatement.{u} →
      AlgClosedMaximalTorusCentralizerStatement.{u}
  ```

- `algClosedMaximalTorusCentralizerReduction`: a proof of
  `AlgClosedMaximalTorusCentralizerReductionStatement.{u}`.
- `maximalTorusCentralizer_of_structuralInputs`: from
  `DynamicCentralizerReductiveStatement.{u}`,
  `NoTorusUnipotentStatement.{u}` and
  `SolvableTorusQuotientStatement.{u}`, a proof of the published
  `MaximalTorusCentralizerStatement.{u}`.

## Proof of `isSolvable_points_of_isFppfQuotient`

Postcomposition with `s` and with `q` gives group homomorphisms
`(U ⟶ T.X) → (U ⟶ M.X) → (U ⟶ Q.X)`. A point `x` in the kernel of the
second satisfies `x ≫ q = 1`, so it factors through the scheme kernel of `q`
(`mem_range_kernelι_iff`). The last clause of `IsFppfQuotient` identifies the
range of that kernel with `SubgroupFunctor.range s`, so `x` is in the image of
the first map. The points of the commutative `T` form a commutative, hence
solvable, group. Mathlib's `Group.isSolvable_of_ker_le_range` then shows that
`U ⟶ M.X` is solvable.

## Proof of `IsConnectedReductive.isIso_of_isCentral_of_isMaximalTorus`

1. **The quotient.** `M` is smooth, affine and connected. The range of the
   central `s` is normal (`IsCentral.range_isNormal`), and `s` is a closed
   subgroup. The Library theorem `normalSubgroupQuotient` therefore gives a
   smooth affine group `Q` and an fppf quotient `q : M ⟶ Q` with kernel
   `range s`. `Q` is connected because `q` is surjective and `M` is
   connected.
2. **`Q` is unipotent.** `centralMaximalTorusQuotientStatement` (Milne 16.43,
   proved in the Library) says that every homomorphism from a torus to `Q` is
   trivial. `NoTorusUnipotentStatement` then makes `Q` unipotent.
3. **`M` is solvable.** The points of `Q` over every test scheme form a
   solvable group (`isSolvable_points_of_isUnipotent`, module
   `Langlands.GroupScheme.Absolute.UnipotentPointsSolvable`). By
   `isSolvable_points_of_isFppfQuotient`, so do the points of `M` over
   `algebraicClosurePoint k`. `isSolvableGroupScheme_of_isSolvable_points`
   (module `Langlands.GroupScheme.Absolute.RegularCocharacterSolvable`) gives
   `IsSolvableGroupScheme M`.
4. **`M` is a torus.** `SolvableTorusQuotientStatement` gives a closed
   subgroup `u : U ⟶ M` and an fppf quotient `p : M ⟶ D` by `range u`. Here
   `U` is smooth, connected and unipotent, `range u` is normal, and `D` is a
   split torus. `IsConnectedReductive.hasTrivialUnipotentRadical` (module
   `Langlands.GroupScheme.Reductive.ToPseudoReductive`) gives `range u = ⊥`.
   An fppf quotient by `⊥` is an isomorphism
   (`RelativeRoot.IsFppfQuotient.isoOfBot`), so `M ≅ D` is a split torus
   (`IsSplitTorus.of_iso`), hence a torus.
5. **Conclusion.** A maximal torus of a torus is an isomorphism
   (`IsMaximalTorus.isIso_of_torus`, module
   `Langlands.GroupScheme.Torus.MaximalAmbient`).

## Proof of `algClosedMaximalTorusCentralizerReduction`

Let `k` be algebraically closed, `G` connected reductive over `Spec k`, and
`j : T ⟶ G` a maximal torus.

1. **A generic cocharacter.** `T` splits over the algebraically closed `k`
   (`isSplitTorus_of_finiteGaloisSplitting` with the Library's
   `torusFiniteGaloisSplitting`). `IsSplitTorus.exists_genericCocharacter`
   gives a cocharacter `ν` of `T` that is generic for `j`. A maximal torus
   that is split is a maximal split torus (`IsMaximalTorus.isMaximalSplitTorus`).
   The Library theorem `genericCentralizer` then gives
   `Dynamic.centralizer (ν ≫ j) = torusCentralizer j`.
2. **The centralizer is connected reductive.**
   `fieldCentralizerRepresentability` gives a closed subgroup `c : C ⟶ G`
   representing `torusCentralizer j`, hence representing
   `Dynamic.centralizer (ν ≫ j)`. `DynamicCentralizerReductiveStatement` makes
   `C` connected reductive.
3. **`T` is a central maximal torus of `C`.** `j` factors as `t ≫ c` with
   `t = torusCentralizerFactor j hc` (module
   `Langlands.GroupScheme.Rational.TorusCentralizerFactorization`). `t` is
   central (`isCentral_torusCentralizerFactor`) and a closed subgroup
   (`isClosedSubgroup_torusCentralizerFactor`). It is maximal: a torus
   `i' : T' ⟶ C` through which `t` factors gives the torus `i' ≫ c` of `G`,
   closed because `c` is a closed immersion. `j` factors through it, so
   maximality of `j` applies.
4. **Conclusion.** The central case makes `t` an isomorphism. Hence
   `torusCentralizer j = range c = range (t ≫ c) = range j`, the middle
   equality by `SubgroupFunctor.range_iso_comp`.

## Proof of `maximalTorusCentralizer_of_structuralInputs`

The Library proves `noTorusBaseChangeReduction : NoTorusUnipotentStatement →
NoTorusBaseChangeStatement` (module
`Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction`). It also proves
`centralMaximalTorusBaseChangeReduction`, which derives
`CentralMaximalTorusBaseChangeStatement` from `NormalSubgroupQuotientStatement`,
`CentralMaximalTorusQuotientStatement` and `NoTorusBaseChangeStatement`
(module `Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction`). With
the Library proofs `normalSubgroupQuotient` and
`centralMaximalTorusQuotientStatement`, these give
`CentralMaximalTorusBaseChangeStatement` from `NoTorusUnipotentStatement`.
`maximalTorusCentralizer_of_centralMaximalTorusBaseChange` (module
`Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction`) combines it
with `algClosedMaximalTorusCentralizerReduction`.

All results use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The reduction is derived and internal. No single source states
`AlgClosedMaximalTorusCentralizerReductionStatement`. Sources: Milne,
*Algebraic Groups* (2017), source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

- Proposition 17.61(a), printed p.372 (one-based PDF p.388): "Let G be a
  reductive group. (a) Let T be a torus in G such that T_{k^a} is maximal in
  G_{k^a}. Then C_G(T) = T." Milne's proof uses Borel subgroups (17.38, 17.39
  and 17.56). This module does not follow that proof. It uses the published
  statements listed above instead.
- Corollary 17.59, printed p.371 (one-based PDF p.387): "If G is reductive,
  then so also is G^S. In particular, the centralizer of a torus in a
  reductive group is reductive." Step 2 of
  `algClosedMaximalTorusCentralizerReduction` uses this fact in the Library's
  form `DynamicCentralizerReductiveStatement`, for the torus `ν(𝔾_m)`, whose
  centralizer is `C_G(T)` because `ν` is generic.
- The proof of Theorem 17.82, printed p.379 (one-based PDF p.395), with
  Lemma 16.43, printed p.340 (one-based PDF p.356): `T` "is maximal in
  C_G(T) if and only if C_G(T)/T contains no nontrivial torus (16.43)". This
  is step 2 of the central case.
- Proposition 17.81, printed p.379 (one-based PDF p.395): "A connected group
  variety is unipotent if it contains no nontrivial torus."
- Theorem 16.33(a),(c), printed pp.335–336 (one-based PDF pp.351–352): a
  smooth connected solvable group `G` over a perfect field has a smooth
  connected normal unipotent subgroup `G_u` with `G/G_u` a torus.

The central case uses 16.43, then 17.81, then 16.33(a),(c), then triviality
of the unipotent radical. This is the standard argument that a connected
reductive group whose maximal torus is central is that torus. Its form here
is Worker 303's, except that Worker 1531 suggested step 4 of the central case:
using 16.33(a),(c) and the fppf quotient by `⊥` in place of the semidirect
decomposition 16.33(d). The route through a generic cocharacter replaces Milne's
torus centralizer by a dynamic centralizer, to match the published Library
statements `GenericCentralizerStatement` and
`DynamicCentralizerReductiveStatement`. The Lean proofs are Worker 303's.
