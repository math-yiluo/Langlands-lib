# Proof: anisotropic simply connected groups over local fields are `SL_1(D)`

Author: Worker 160 (Task 5636).

`Langlands.GroupScheme.localAnisotropicSimplyConnectedClassification` proves the
published proposition
`Langlands.GroupScheme.LocalAnisotropicSimplyConnectedClassificationStatement.{u}`
at every universe `u`. That proposition is in the module
`Langlands.GroupScheme.SimplyConnected.LocalAnisotropicClassificationStatement`, and its
Lean/Markdown pair is imported unchanged. The theorem has no premise.

## The proved statement

Let `K : Type u` be a nonarchimedean local field of any characteristic, with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`. Let
`G` be a group scheme over `Spec (CommRingCat.of K)` with `[IsAffineHom G.X.hom]`. If `G`
is simply connected (`IsSimplyConnected G`), absolutely almost simple
(`IsAbsolutelyAlmostSimple G`) and anisotropic (`IsAnisotropic G`, meaning
`splitRank G = 0`), then there is a `D : Type u` with `[DivisionRing D] [Algebra K D]
[FiniteDimensional K D] [Algebra.IsCentral K D]` and
`Nonempty (G ≅ CentralSimpleUnits.normOne K D)`. The isomorphism is an isomorphism of
group schemes over `Spec K`, not only of groups of `K`-points. The characteristic of `K`
and of its residue field is not restricted, so characteristic 2 and residue
characteristic 2 are both included.

This is Bruhat–Tits (1967), §8, Proposition 6, printed p. 35 / PDF p. 41
(`springer-1967-conference-local-fields`), over nonarchimedean local fields. The
statement Markdown explains why local fields satisfy that proposition's hypotheses and why
the conclusion is stated through the algebraic model `SL_1(D)`.

## The implemented proof

The proof is the single term

```text
localAnisotropicSimplyConnectedClassification_of_statements titsIndexExistence
  ⟨localAnisotropicTypeA_of_affineDiagram localAnisotropicAffineDiagram,
    localAnisotropicTypeAInner⟩
  innerTypeANormOne CentralSimpleUnits.matrixNormOneSplitRank
```

It uses seven published theorems, all at the universe `u`:

1. `localAnisotropicSimplyConnectedClassification_of_statements` (module
   `SimplyConnected/LocalAnisotropicClassificationReduction`, Task 5636) derives the
   target from four propositions: `TitsIndexExistenceStatement`,
   `LocalAnisotropicInnerTypeAStatement`, `InnerTypeANormOneStatement` and
   `CentralSimpleUnits.MatrixNormOneSplitRankStatement`. Its argument runs as follows.
   Simple connectedness makes `G` smooth, so `G` is locally of finite type. Actual Tits
   index data `d` therefore exist. The type-`A` input and the inner input together give
   `d.HasInnerTypeA n`. The norm-one presentation gives `G ≅ normOne K A` for a central
   simple algebra `A`. Since `splitRank` is invariant under isomorphism, anisotropy and
   the split rank `m - 1` of `SL_m(D)` force the Wedderburn–Artin matrix size to be
   `m = 1`. So `A` is a central division algebra `D`, up to an algebra isomorphism, and
   the composite isomorphism is the conclusion. That module's Markdown records each step.
2. `titsIndexExistence` (module `Reductive/TitsIndexExistenceProof`, Task 5621) proves
   `TitsIndexExistenceStatement`.
3. `LocalAnisotropicInnerTypeAStatement` is the conjunction of
   `LocalAnisotropicTypeAStatement` and `LocalAnisotropicTypeAInnerStatement` (module
   `SimplyConnected/LocalAnisotropicInnerTypeAStatement`). The anonymous constructor
   supplies the two conjuncts:
   - The first conjunct is `localAnisotropicTypeA_of_affineDiagram`, applied to
     `localAnisotropicAffineDiagram`. The first theorem is in module
     `SimplyConnected/LocalAnisotropicTypeAReduction`, from Task 5972. It derives type
     `A_n` with `n > 0` from `LocalAnisotropicAffineDiagramStatement`, using the
     combinatorial theorem `TitsIndexData.exists_equiv_cartanA_of_transitive_extension`.
     The second theorem is in module `SimplyConnected/LocalAnisotropicAffineDiagramProof`,
     from Task 6205. It proves that affine-diagram statement with no premise. Together they
     give the type-`A` part of Kaletha–Prasad (2023), Theorem 10.3.1, over local fields.
   - The second conjunct is `localAnisotropicTypeAInner` (module
     `SimplyConnected/LocalAnisotropicTypeAInnerProof`, Task 5973). If such a group is
     also simply connected, its star action is trivial.
4. `innerTypeANormOne` (module `SimplyConnected/InnerTypeANormOneProof`, Task 5703) proves
   `InnerTypeANormOneStatement`.
5. `CentralSimpleUnits.matrixNormOneSplitRank` (module
   `SimplyConnected/MatrixNormOneSplitRankProof`, Task 5637) proves
   `CentralSimpleUnits.MatrixNormOneSplitRankStatement`.

Task 5972 also has an accepted candidate that proves `LocalAnisotropicTypeAStatement` as
`localAnisotropicTypeA`. It uses the same composition of the two published theorems. This
proof does not depend on that candidate, because it applies the two theorems directly.

## Excluded inputs

The task forbids `LocalRankOneClassificationStatement`, any local Kneser–Tits statement,
and any result whose planned proof consumes this classification. A private development
check walked every constant reachable from this theorem's type and value, through the
types and values of all reachable Langlands constants: 59,654 Langlands constants in
total. It looked for names containing `KneserTits`, `RankOneClassification`,
`RankOneTitsIndex`, `LocalRankOne` or `LocalAnisotropicSimplyConnected`. The only
matches were the target statement itself, which is the theorem's type, and
`Langlands.LocalGalois.localRankOne`. That second constant is the rank-one valuation
structure on a local field, from `Galois/Local/AbsoluteDefinitions`. It is not a
group-theoretic rank-one result. No Kneser–Tits constant is reachable.

The kernel check reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.
