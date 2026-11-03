# Standard parabolics on rational points from a Tits-system realization

This module reduces `Langlands.GroupScheme.StandardParabolicPointsStatement` to three
inputs. They are the realization proposition `StandardParabolicTitsRealization`
defined here, the published `StandardParabolicEndpointsStatement`, and the published
`StandardParabolicOrderStatement`. The reduction uses the abstract theory in
`Langlands.Group.TitsSystemBruhat`. It also uses
`IsSplitSubtorus.mk_mem_standardRelativeWeylGroup` from
`Langlands.GroupScheme.Rational.NormalizerParabolicPoints`, which proves that a normalizing
point in `P_J(k)` has its class in `W_J`. The module adds no hypotheses or axioms. It does
not prove the target outright, because none of the three inputs is proved here.

## The realization proposition

`StandardParabolicTitsRealization` is an internal packaging proposition. It is not a
statement from the literature. It quantifies over the same data as the target: a
field `k`, a connected reductive `G`, a maximal split torus `i : T → G`, and a generic
cocharacter `ν`. It asserts that some set `S` of elements of the relative Weyl group
`relativeWeylGroup i` satisfies all of the following.

- `IsTitsSystem (standardParabolicPoints i ν ∅) (normalizerPoints i) π S`, where
  `π` is the quotient map `QuotientGroup.mk'` from `N(k)` onto
  `N(k) / (Z(k) ∩ N(k))`.
- For every `J` contained in the simple relative roots, `standardRelativeWeylGroup i ν J`
  is `Subgroup.closure X` for some `X ⊆ S`.
- Conversely, for every `X ⊆ S`, there is such a `J` with
  `standardRelativeWeylGroup i ν J = Subgroup.closure X`.

Borel–Tits verify the Tits axioms for `(G(k), P(k), N(k))` in 5.15–5.16 (printed
pp. 100–101). They prove `P_θ(k) = P(k) W_θ P(k)` in 5.17 and derive the classification,
self-normalization and double-coset statements in 5.18 and 5.20 (printed pp. 101–102). The three bullets record the parts of that realization that the abstract
theory needs and that are not proved in the imported modules.

## Main theorem

`standardParabolicPointsStatement_of_titsRealization` assumes the realization
proposition, `StandardParabolicEndpointsStatement` and
`StandardParabolicOrderStatement`, and proves `StandardParabolicPointsStatement`.

## Proof

Fix the data and write `B = P_∅(k)`.

- The first endpoint clause, evaluated at rational points, gives
  `Dynamic.parabolic (ν ≫ i)(k) = B`. After rewriting with it, every occurrence of the
  dynamic minimal parabolic in the target becomes `B`.
- The order statement applied to `∅ ⊆ J` gives `B ≤ P_J(k)`. It is used through
  `SubgroupFunctor.le_def`.
- Suppose `W_J = ⟨X⟩`. `IsSplitSubtorus.mk_mem_standardRelativeWeylGroup`, applied to
  the split subtorus underlying the maximal split torus, says that `π` maps
  `N(k) ∩ P_J(k)` into `W_J = ⟨X⟩`. It needs neither genericity of `ν` nor
  `J ⊆ Δ`. Every element of `W_J` is the class of a normalizing point of `L_J(k)`,
  and `L_J(k) ⊆ P_J(k)` by `standardLevi_le_standardParabolic`. So
  `IsTitsSystem.coe_eq_standardParabolic` gives `P_J(k) = B ⟨X⟩ B` as sets.

The four clauses then follow.

1. Bruhat pieces: apply the previous step with `X = W_J`, which is legitimate because
   `Subgroup.closure W_J = W_J`. Unfold `TitsSystem.standardParabolic` and
   `TitsSystem.cell`.
2. Classification: a subgroup `H ⊇ B` equals `B ⟨X⟩ B` for some `X ⊆ S`
   (`exists_eq_standardParabolic`). The converse realization bullet supplies `J` with
   `W_J = ⟨X⟩`, so `H = P_J(k)`. Conversely, each `P_J(k)` contains `B`.
3. Self-normalization: `normalizer_eq_of_le` applied to `B ≤ P_J(k)`.
4. Double cosets: choose `X, Y ⊆ S` with `W_J = ⟨X⟩` and `W_K = ⟨Y⟩`. Then
   `exists_doubleCoset_equiv` applies to `P_J(k) = B ⟨X⟩ B` and `P_K(k) = B ⟨Y⟩ B`.
   It sends the class of `π n` to the class of `n`.
