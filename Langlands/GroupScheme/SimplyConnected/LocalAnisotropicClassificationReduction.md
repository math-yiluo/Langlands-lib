# The local anisotropic classification from actual Tits indices

Author: Worker 160.

This module reduces the published target
`Langlands.GroupScheme.LocalAnisotropicSimplyConnectedClassificationStatement.{u}`
to four published but unproved propositions. They appear as explicit
hypotheses, so this module does not prove the target. Task 5636 owns the
target. The final proof will apply the reduction below once all four inputs
are proved.

## The input bundle

`LocalAnisotropicClassificationInputs.{u}` is the Prop-valued conjunction of
the following four propositions, all at the same universe `u`:

1. `TitsIndexExistenceStatement.{u}` (module
   `Reductive/TitsIndexChoiceStatement`, proof Task 5621). Every affine
   semisimple field group that is locally of finite type has actual
   Tits-index data `TitsIndexData G`.
2. `LocalAnisotropicInnerTypeAStatement.{u}` (module
   `SimplyConnected/LocalAnisotropicInnerTypeAStatement`). This is the
   conjunction of `LocalAnisotropicTypeAStatement` and
   `LocalAnisotropicTypeAInnerStatement`. Over a nonarchimedean local field,
   an anisotropic absolutely almost-simple group has an index of type `A_n`
   with `n > 0`. If the group is also simply connected, the full star action
   on that index is trivial.
3. `InnerTypeANormOneStatement.{u}` (module
   `SimplyConnected/InnerTypeANormOneStatement`, proof Task 5703). A simply
   connected absolutely almost-simple group with `d.HasInnerTypeA n` is
   isomorphic, as a group scheme, to `CentralSimpleUnits.normOne K A` for a
   finite-dimensional central simple `K`-algebra `A` of reduced degree
   `n + 1`.
4. `CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}` (module
   `SimplyConnected/MatrixNormOneSplitRankStatement`, proof Task 5637). For a
   finite-dimensional central division algebra `D` and `m > 0`, the split
   rank of `normOne K (Matrix (Fin m) (Fin m) D)` is `m - 1`.

None of these inputs is the local rank-one classification or a local
Kneser–Tits statement. None of them is planned to consume the anisotropic
classification.

## The algebra step

`CentralSimpleUnits.exists_division_model_of_splitRank_zero` assumes input 4.
It takes `A : Type u` with `[Ring A] [Algebra K A] [FiniteDimensional K A]
[Algebra.IsCentral K A] [IsSimpleRing A]`, over an arbitrary field `K`, and
assumes `splitRank (normOne K A) = 0`. It concludes that there are
`D : Type u` with `[DivisionRing D] [Algebra K D] [FiniteDimensional K D]
[Algebra.IsCentral K D]` and an actual isomorphism
`normOne K A ≅ normOne K D`.

The proof runs as follows:

1. The published Wedderburn–Artin model `exists_matrix_division_model`
   gives `m` with `NeZero m`, a central division algebra `D`, an algebra
   isomorphism `e : A ≃ₐ[K] Matrix (Fin m) (Fin m) D` and a group-scheme
   isomorphism `f` between the two norm-one groups.
2. The published `splitRank_eq_of_iso f` moves split rank zero across `f`.
   Input 4 then gives `((m - 1 : ℕ) : ℕ∞) = 0`. Hence `m - 1 = 0`, and since
   `m ≠ 0`, `m = 1`.
3. With `m = 1`, the proof defines an algebra isomorphism
   `g : Matrix (Fin 1) (Fin 1) D ≃ₐ[K] D` taking a matrix to its only entry.
   Its underlying equivalence is Mathlib's `Matrix.uniqueEquiv`.
   Multiplicativity and compatibility with `algebraMap` are checked by
   `simp`. Mathlib's `Matrix.uniqueAlgEquiv` is not used directly because
   its matrix multiplication uses a different `Fintype (Fin 1)` instance.
4. The published transport `normOneAlgEquivIso (e.trans g)` is the required
   isomorphism `normOne K A ≅ normOne K D`.

## The reduction

`localAnisotropicSimplyConnectedClassification_of_statements` takes the four
inputs separately and concludes the target. Fix a nonarchimedean local field
`K`, an affine group scheme `G` over `Spec K`, and the target hypotheses
`IsSimplyConnected G`, `IsAbsolutelyAlmostSimple G` and `IsAnisotropic G`.
The proof has these steps:

1. Simple connectedness gives semisimplicity, hence connected reductivity
   and smoothness. So `G.X.hom` is locally of finite type, as the index
   interface requires.
2. Input 1 gives actual index data `d : TitsIndexData G`.
3. The first conjunct of input 2 gives `n > 0` and a numbering
   `d.Vertex ≃ Fin n` carrying the Cartan pairings to `CartanMatrix.A n`.
   The second conjunct, applied to the same `d` and `n`, gives a trivial
   star action. Together these are exactly `d.HasInnerTypeA n`.
4. Input 3 gives a central simple algebra `A` and `e : G ≅ normOne K A`.
5. `splitRank_eq_of_iso e` and `IsAnisotropic G`, which means
   `splitRank G = 0`, give `splitRank (normOne K A) = 0`.
6. The algebra step gives `D` and `f : normOne K A ≅ normOne K D`. The
   composite `e ≪≫ f` is the required group-scheme isomorphism.

`localAnisotropicSimplyConnectedClassification_of_inputs` is the same result
with the bundled hypothesis `LocalAnisotropicClassificationInputs.{u}`.

There is no restriction on characteristic, and the universe `u` is
arbitrary. The conclusion is an isomorphism of group schemes over `Spec K`,
not an isomorphism of groups of rational points.

## Provenance

The bundle and the reduction are internal to the project's proof plan for
Task 5636. Their mathematical content is the derivation in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), printed p. 393 / PDF p. 424
(`kaletha-prasad-2023-bruhat-tits-new-approach`). Kaletha–Prasad combine
Theorem 10.3.1, the isotropy of outer type `A_n`, and Weil's description of
anisotropic inner forms of type `A` to conclude that every simply connected
absolutely almost simple anisotropic group over a nonarchimedean local
field is `SL_1(D)`. Bruhat–Tits (1967), §8, Proposition 6, printed p. 35 /
PDF p. 41 (`springer-1967-conference-local-fields`), states the same
conclusion for rational points. Here Weil's description is replaced by
inputs 3 and 4: the published Wedderburn–Artin model, and the split rank
`m - 1` of `SL_m(D)`, which forces `m = 1`.
