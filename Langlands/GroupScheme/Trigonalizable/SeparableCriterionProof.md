# Proof of Milne 16.6: becoming trigonalizable over a separable extension

## `separablyTrigonalizableCriterion`

**Statement.** `Langlands.GroupScheme.separablyTrigonalizableCriterion :
SeparablyTrigonalizableCriterionStatement.{u}`, for every universe `u`. This
is the published statement from
[`SeparableCriterionStatement`](SeparableCriterionStatement.md), with no
extra hypotheses. Let `k` be a field and `G` a group scheme over
`Spec (CommRingCat.of k)` with `LocallyOfFiniteType G.X.hom` and
`IsAffineHom G.X.hom`. The statement has two parts:

1. `G` becomes trigonalizable over some separable field extension `K` of `k`
   if and only if `G` has a normal unipotent closed subgroup `i : U ⟶ G` and
   an fppf quotient `q : G ⟶ M` by `range i` with `M` of multiplicative
   type.
2. For any such `i` and `q`, every closed subgroup `j : V ⟶ G` with `V`
   unipotent satisfies `range j ≤ range i`.

**Proof.** The theorem applies
`SeparableTrigonalization.separablyTrigonalizableCriterion_of_characterization`
from [`SeparableCriterionReduction`](SeparableCriterionReduction.md) to
`trigonalizableCharacterization`, the Library proof of Milne's
Proposition 16.2 (`TrigonalizableCharacterizationStatement`) in
`Langlands.GroupScheme.Trigonalizable.CharacterizationProof`.

The reduction theorem proves the statement from 16.2 as follows:

- **(a) ⇒ (b)** (`exists_unipotent_multiplicativeType_quotient`): 16.2 over
  `K` gives a normal unipotent closed subgroup of `G_K` with diagonalizable
  quotient. Base-change it to the separable closure `Ω` of `k`, into which
  `K` embeds. There it contains every unipotent closed subgroup of `G_Ω`
  (Milne 14.18), so it is invariant under `Aut_k(Ω)` and descends to a
  closed subgroup `U` of `G` (Galois descent, Milne 1.54). Unipotence and
  normality descend to `U`. The affine quotient `G ⟶ G/U` (Milne 5.14)
  becomes isomorphic over `Ω` to the diagonalizable quotient, by uniqueness
  of fppf quotients. So `G/U` is of multiplicative type.
- **(b) ⇒ (a)** (`exists_separable_isTrigonalizable`): `M` splits over a
  finite Galois extension `K` (Milne 12.19). Over `K` the base-changed data
  satisfy condition (d) of 16.2, so `G_K` is trigonalizable.
- **Part 2** (`IsUnipotent.range_le_of_isFppfQuotient`, in
  [`UnipotentKernelMaximal`](UnipotentKernelMaximal.md)): for a unipotent
  closed `j`, the composite `j ≫ q` is trivial (Milne 14.18), so `j` factors
  through the kernel of `q`, which is `range i`.

The helper modules
[`UnipotentKernelMaximal`](UnipotentKernelMaximal.md),
[`GreatestUnipotent`](GreatestUnipotent.md) and
[`SeparableCriterionReduction`](SeparableCriterionReduction.md) give the
details.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, Theorem
16.6 and its proof, pp.325–326 (PDF pp.341–342). Milne's proof of (a) ⇒ (b)
uses a finite Galois extension. The Lean proof uses the separable closure of
`k` instead, which makes no difference to the result.
