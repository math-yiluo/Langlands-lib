# Characters of the multiplicative part over an algebraically closed field

Helper module for the proof of
`Langlands.GroupScheme.CommutativeMultiplicativePartCharacterizationStatement`; see
[`MultiplicativePartCharacterizationProof`](MultiplicativePartCharacterizationProof.md).
All declarations are in namespace `Langlands.GroupScheme.MultiplicativePart`. This module
replaces Milne's decomposition `G = G_u × G_s` over `k^a` (Theorem 16.13(b), which is not
yet proved in the Library) by a direct argument with characters. Every character of `S`
extends to a character of `G`. Such an extension is trivial on `S` only if it is trivial.

## Algebraic lemmas

- `eq_one_of_isGroupLikeElem`: let `B` be a bialgebra over a field `K` satisfying the
  Library's `Unipotent.OneMemStable K B` (every nonzero finite-dimensional
  right-translation stable subspace contains `1`). Then its only group-like element is `1`.
  For a group-like `b`, the line `K ∙ b` is stable, since `rightAct f b = f b • b`. So
  `1 = c • b`, and applying the counit gives `c = 1`.
- `eq_one_of_map_isGroupLikeElem`: let `φ : B →ₐc[K] A` be an injective bialgebra map, with
  `B` as above. If `φ b` is group-like then `φ b = 1`. The element `b` is itself group-like,
  because `φ ⊗ φ` is injective (Mathlib's `TensorProduct.map_injective_of_flat_flat`).

## Character lifting

`exists_groupLike_lift`. Let `K` be algebraically closed, and let `G`, `S`, `Q` be group
schemes over `Spec K` with `G.X.left` and `Q.X.left` affine and `G` commutative. Let
`eS0 : S ≅ D_K(N)` for an abelian group `N`. Let `s : S ⟶ G` be a closed subgroup and
`q : G ⟶ Q` an fppf quotient with kernel `range s` and `IsUnipotent Q`. Then for every
`n : N` there is a group-like `g` in `A = AffineCoordinates.hopfAlgebra G` with:

- `g ^ m = 1` whenever `m • n = 0`;
- `g = 1` only if `n = 0`.

Proof. The construction of the Hopf maps `π : A ⟶ K[N]` (from `s`) and
`φ : B ⟶ A` (from `q`, where `B = AffineCoordinates.hopfAlgebra Q`) through
`hopfSpec.fullyFaithful.preimage` copies the published
`CentralExtensionHopfSpec.exists_iso_diagonalizable_of_commutative_extension`. The Library
then gives:

- `π` is surjective (`CentralExtensionHopfSpec.surjective_of_isClosedSubgroup`);
- `φ` is injective (`faithfullyFlat_of_isFppfQuotient`);
- every element of the degree-zero component `GroupAlgebraCoaction.grade π 0` comes from `B`
  (`exists_eq_of_lTensor_comul_eq`, with the rewriting of the published
  `isExtension_diagonalizable`);
- `B` satisfies `OneMemStable`
  (`Unipotent.oneMemStable_of_isUnipotent_cogroup` with `coordinateCogroupIso`).

By the two algebraic lemmas, every group-like element of degree `0` is `1`. Since `A` is
cocommutative (`AffineCoordinates.hopfAlgebra_isCocomm`) and `K` is algebraically closed,
the published `GroupAlgebraCoaction.exists_isGroupLikeElem_mem_grade` (with
`grade_ne_bot_of_surjective`) gives a group-like `g` of degree `n`. Its power `g ^ m` is
group-like of degree `m • n` (`mul_mem_grade`), so it equals `1` when `m • n = 0`. If
`g = 1`, then `1` lies in degree `n` and in degree `0`. The projection formula
`proj_of_mem` then forces `n = 0`, because `1 ≠ 0` in `A`.

## Consequences

- `isReduced_hopfAlgebra`: if `G.X.hom` is smooth, `A` is reduced. `G.X.left` is reduced
  (`SmoothReducedBase.isReduced_of_smooth_over_spec`). It is isomorphic to `Spec A` through
  `AffineCoordinates.hopfSpecIso`, and Mathlib's `affine_isReduced_iff` applies.
- `connectedSpace_primeSpectrum`: if `G.X.left` is connected, so is `PrimeSpectrum A`, through
  the same isomorphism.
- `eq_zero_of_smooth` (same hypotheses as the lifting lemma, plus `Smooth G.X.hom` and
  `ExpChar K p`): if `p • x = 0` in `N` then `x = 0`. Take the lift `g` of `x`, so `g ^ p = 1`.
  In characteristic exponent `p`, `(g - 1) ^ p = g ^ p - 1 = 0` (`sub_pow_expChar`). Since `A`
  is reduced, `g = 1`, hence `x = 0`.
- `exists_pow_nsmul_eq_zero_of_connected` (with `ConnectedSpace G.X.left` instead): every
  torsion `x : N` satisfies `p ^ a • x = 0` for some `a`. Write the order of `x` as `p ^ a * m`
  with `m` nonzero in `K`, and lift `y = p ^ a • x` to `g`, so `g ^ m = 1`. Then
  `e = m⁻¹ • ∑_{i<m} g ^ i` is idempotent, by the Library's
  `Diagonalizable.SmoothConnectedCriteria.isIdempotentElem_geomSum`. So `e = 0` or `e = 1`
  (`eq_zero_or_one_of_connectedSpace`). The counit sends `e` to `1`, so `e = 1`. Then
  `(g - 1) e = 0` (`geomSum_mul_self`) gives `g = 1`, hence `y = 0`.
