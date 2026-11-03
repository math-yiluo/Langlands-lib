# Normalized Jacquet exponents along the actual split component

Author: Worker 1507. Module
`Langlands.Representation.Exponents.NormalizedJacquetSplitComponent`, namespace
`Langlands.Aubert.General.RationalPointFamily`.

This file defines the characteristic subspaces `(r^G_P V)_χ`, the normalized
exponents and the set `Exp(A, r^G_P V)` of Renard, *Représentations des groupes
réductifs p-adiques* (French edition dated 9 July 2026), VII.1.1, printed p. 220 /
PDF p. 226. It uses the actual normalized Jacquet module of the standard
rational-point family and the actual split component of a represented standard Levi.
It specializes the generic construction of
`Langlands.Representation.Exponents.SplitComponentWeights` along the point map of
`Langlands.GroupScheme.Rational.SplitComponentLeviPoints`.

## Setting

The field is `k : Type u`, with `[Field k]`. `T` and `G` are a commutative group
scheme and a group scheme over `Spec k`, with `[IsAffineHom G.X.hom]`;
`i : T.toGrp ⟶ G`, `ν : cocharacterLattice T` and `I : Finset (SimpleRoot i ν)`
determine the published standard subgroups `parabolic i ν I`, `levi i ν I` and
`unipotent i ν I` of `RationalPoint k G.X`. These are `P(k) = M(k) U(k)`, with
`levi i ν I = standardLeviPoints i ν (rootSet i ν I)`.

The represented Levi `j : M ⟶ G` with
`hj : (standardLevi i ν (rootSet i ν I)).IsRepresentedBy j` is input data. So is
the homomorphism `a : A.toGrp ⟶ M` from a commutative group scheme `A`, together
with `ha : IsSplitComponent a` wherever centrality or the topology of `A(k)` is
needed. Their existence is not proved here.

The topological inputs are explicit:

- `[TopologicalSpace k]`; the topology of `G(k)` is the published family
  `pointTopology`, which is `rationalPointTopology k G.X`, installed as a local instance;
- `[LocallyCompactSpace (RationalPoint k G.X)]` and
  `[NonarchimedeanGroup (RationalPoint k G.X)]`;
- `h : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I)`
  and `hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))`, the inputs of
  the published `jacquetFunctor h hU`. The published
  `isSemidirectDecomposition_of_dynamic` and
  `isSemidirectDecomposition_of_standardCocharacterStatement`
  (`RationalParabolicDecomposition`) supply `h` from their own hypotheses;
- `hM : IsClosed (levi i ν I : Set (RationalPoint k G.X))`, only for the three
  comparison laws at the end.

`k` is any topological field with these properties. It is not restricted to
`PadicField`, to characteristic zero, or to `GL_n`. A nonarchimedean local field of
any characteristic, with `G(k)` given its canonical topology, is the intended case.
Representations are `π : SmoothRep.{0, u, v} ℂ (RationalPoint k G.X)`: complex
coefficients, the group in the field universe `u`, and the carrier in an
independent universe `v`.

## Point map, centrality and continuity

- `splitComponentPointsMap i ν I j hj a : rationalPoints A.toGrp →* levi i ν I` is the
  abbreviation of `splitComponentLeviPointsMap i ν (rootSet i ν I) j hj a`, which is
  `A(k) → M(k)` followed by `standardLeviRationalPointsEquiv`.
- `splitComponentPointsMap_mem_center ha t`: the values are central in `levi i ν I`.
- `splitComponentPointTopology ha` is the canonical topology
  `rationalPointTopology k A.toGrp.X` of `A(k)`. It is defined using the affineness
  `IsSplitComponent.isAffine ha` and is not a global instance.
- `continuous_splitComponentPointsMap ha`: the map is continuous from
  `splitComponentPointTopology ha` to `levi i ν I` with the subspace topology of
  `pointTopology`. The proof is `continuous_splitComponentLeviPointsMap`, so it uses
  the actual point map of `a ≫ j`, not `StandardLeviPointTopologyComparison`.

## The Jacquet action of the split component

`jacquetFunctor h hU` is the published normalized Jacquet functor
`normalizedJacquetFunctor (unipotent i ν I) (levi i ν I) hU h.levi_le_normalizer`
(`Langlands.Representation.Aubert.General.Parabolic`). Its object at `π` has carrier
the actual coinvariant quotient `V ⧸ span {π(u) v - v}` for `u` in the unipotent
subgroup. The action is twisted by `HaarModulus.closedInverseHalfCharacter`.
`jacquetFunctor_obj_splitComponentPointsMap_apply` specializes the published
`normalizedJacquetFunctor_obj_apply` to the points of `A(k)`:

`r(t) [v] = δ(t)^{-1/2} [π(t) v]`,

where `t` stands for `splitComponentPointsMap i ν I j hj a t` and `δ^{-1/2}` is
`closedInverseHalfCharacter (unipotent i ν I) hU (levi i ν I) h.levi_le_normalizer`.

## Definitions

- `normalizedJacquetWeightSpace i ν I j hj h hU ha π χ` is the subrepresentation
  `generalizedWeightSpace` of `((jacquetFunctor h hU).obj π).representation` along
  `splitComponentPointsMap`, with centrality proof `splitComponentPointsMap_mem_center`.
  Here `χ : rationalPoints A.toGrp →* ℂˣ`. It is Renard's `(r^G_P V)_χ`: the union,
  over compact open `K_M` of `levi i ν I` and powers `d`, of the `K_M`-fixed vectors
  of the Jacquet module killed by `(r(t) − χ(t))^d` for every `t ∈ A(k)`. All the
  generic laws apply: the membership laws, monotonicity in `K_M` and `d`, Levi
  stability, and restriction of intertwiners with its identity and composition laws.
- `IsNormalizedJacquetExponent i ν I j hj h hU ha π χ` is
  `IsGeneralizedWeight` for the same data, with `A(k)` given
  `splitComponentPointTopology ha`. It says that `χ` has open kernel in the canonical
  topology of `A(k)` (Renard's smooth character) and `(r^G_P V)_χ ≠ 0`.
  `isNormalizedJacquetExponent_iff_isOpen_ker_and` states this unfolding (by `Iff.rfl`).
- `normalizedJacquetExponents i ν I j hj h hU ha π` is the set of such `χ`, Renard's
  `Exp(A, r^G_P V)`; `mem_normalizedJacquetExponents` is its membership law (`Iff.rfl`).

## Comparison laws (with `hM`)

With `hM`, the Levi subgroup is locally compact (`hM.locallyCompactSpace`). It is
also a nonarchimedean group by the published subgroup instance, so the generic
locally profinite laws apply. The Jacquet module is smooth (`isSmooth` of the
published `SmoothRep`).

- `mem_normalizedJacquetWeightSpace`: `x ∈ normalizedJacquetWeightSpace … π χ` if and
  only if `∃ d : ℕ, ∀ t, ((r(t) - χ(t) • 1) ^ d) x = 0`. The compact open fixing
  condition holds automatically for the smooth Jacquet module.
- `normalizedJacquetWeightSpace_ne_bot_iff`: `(r^G_P V)_χ ≠ ⊥` if and only if
  `IsGeneralizedEigencharacter (r.comp splitComponentPointsMap) χ`, the generic
  predicate of `Langlands.Representation.Exponents.Jacquet` for the restricted action.
- `isNormalizedJacquetExponent_iff`: `IsNormalizedJacquetExponent … π χ` if and only
  if `IsGeneralizedEigencharacter (r.comp splitComponentPointsMap) χ`. The open-kernel
  condition is automatic: the point map is continuous for the canonical topology of
  `A(k)` (`continuous_splitComponentPointsMap`). A generalized eigencharacter of a
  smooth action restricted along a continuous map has open kernel
  (`isOpen_ker_of_isGeneralizedEigencharacter_comp`).

## Modulus convention (Renard VI.1.2)

Write `δ(m)` for the published Haar modulus
`HaarModulus.closedNormalizerCharacter` of conjugation `u ↦ m u m⁻¹` on the closed
unipotent subgroup. Its scaling convention is `μ(m S m⁻¹) = δ(m) μ(S)`, the
Bernstein–Zelevinsky convention documented in `Group/HaarModulus.md`. The published
`jacquetFunctor` twists the `U`-coinvariants by
`closedInverseHalfCharacter = δ^{-1/2}`, as in `jacquetFunctor_obj_splitComponentPointsMap_apply`.

Renard VI.1.2, printed p. 135 / PDF p. 141, (VI.1.2.2), sets
`r^G_P(π, V) = (π_N ⊗ δ_P^{1/2}, V_N)`. The Remarque on printed p. 136 / PDF p. 142
says that his conventions replace the usual `δ_P` by its inverse, because of his
choice of modular function in II.3.7. So Renard's `δ_P^{1/2}` is the usual
`δ^{-1/2}`, and Renard's `r^G_P` is the published `jacquetFunctor`. This is the same
identification already recorded in `Representation/Aubert/General/Parabolic.md`
(section "Source identification"). The exponents defined here are therefore Renard's
*normalized* exponents.

## Source correspondence (Renard VII.1.1, printed p. 220 / PDF p. 226)

| Renard | Lean |
| --- | --- |
| `P = MN` parabolic with split component `A` | `parabolic`, `levi`, `unipotent` of the standard family; `j`, `hj`; `a`, `ha : IsSplitComponent a` |
| `A ⊂ M` acting on `r^G_P V` | `splitComponentPointsMap`, `splitComponentPointsMap_mem_center`, `jacquetFunctor_obj_splitComponentPointsMap_apply` |
| `r^G_P(π, V)` | `(jacquetFunctor h hU).obj π` |
| `(r^G_P V)^{K_M}_χ` | `fixedGeneralizedCharacterSpace` of the Jacquet representation along `splitComponentPointsMap` (generic file) |
| `(r^G_P V)_χ = ⋃_{K_M} (r^G_P V)^{K_M}_χ` | `normalizedJacquetWeightSpace`, `mem_normalizedJacquetWeightSpace` |
| `χ` a smooth character of `A` | open kernel for `splitComponentPointTopology ha` |
| "exposant normalisé de `π` pour `P = MN`" | `IsNormalizedJacquetExponent` |
| `Exp(A, r^G_P V)` | `normalizedJacquetExponents`, `mem_normalizedJacquetExponents` |

Renard assumes `π` admissible; here `π` is any smooth representation. This is a
domain extension of the definitions only. No admissibility consequence is claimed.

## Retained boundaries

The following parts of VII.1.1 and later sections are not proved or encoded here:

- the decomposition `(r^G_P V)^{K_M} = ⊕_χ (r^G_P V)^{K_M}_χ` and (VII.1.1.1)
  `r^G_P V = ⊕_{χ ∈ Exp} (r^G_P V)_χ`;
- finiteness of `Exp(A, r^G_P V)` for finite length (Schur's lemma, VI.6.4);
- preservation of admissibility (VI.6.1) and of finite length by `r^G_P`;
- the Remark for `P = G` and its comparison with III.1.10;
- the Lemma (i)/(ii) comparing exponents of induced and restricted representations,
  and any induction/Jacquet compatibility theorem;
- Casselman's criterion (VII.1.2), real parts `ℜ(χ)` and chambers, analytic
  temperedness, Langlands data and the Langlands classification;
- the existence of a represented standard Levi or of its split component, the
  closedness of `levi` and `unipotent`, and `StandardLeviPointTopologyComparison`.

- Literature ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
