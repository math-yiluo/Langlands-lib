# Normalized induction and split-component exponents for represented parabolics

Author: Worker 6. Module `Langlands.Representation.Exponents.ArbitraryParabolicInduction`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.1.1, printed pp.220–221 / PDF pp.226–227. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Normalized induction is VI.1.2, printed p.135 / PDF p.141, with the modular-function remark on printed p.136 / PDF p.142.

VII.1.1 compares three characteristic-space decompositions: that of `r_P^G V` under `A`, that of a Levi representation `W` under `A_M`, and that of a representation of `G` (in particular `i_P^G W`) under `A_G`. The published module `ArbitraryParabolic` already defines the first. This module supplies the other two and the functor `i_P^G` for the same represented parabolic data. It is a definition unit: it states and proves only the structural facts needed to build these objects. No decomposition, finiteness or induction/restriction comparison from VII.1.1 is asserted here.

## Actual objects and hypotheses

The field is `k : Type u`, with `[Field k]`. The objects `G`, `H`, `P`, `M`, `U` are group schemes over `Spec k`; `A` and `AG` are commutative group schemes over `Spec k`. The maps are those of `ArbitraryParabolic`:

- `p : P ⟶ G`, a parabolic (`IsParabolicSubgroup p`) or, for the decomposition theorem, only a closed subgroup (`IsClosedSubgroup p`);
- `l : M ⟶ P`, with `IsRationalLeviSubgroup l` where the induction functor is formed;
- `r : U ⟶ P`, with `hr : LeviSubgroup.IsGeometricUnipotentRadical r`;
- `hmul : IsIso (subgroupMultiplication l r)` for this same pair `l, r`;
- `a : A.toGrp ⟶ M` with `IsSplitComponent a`, Renard's `A_M`, and `aG : AG.toGrp ⟶ G` with `IsSplitComponent aG`, Renard's `A_G`.

No existence of any of these objects is asserted. The Levi hypothesis of `inductionFunctor` is unused in its body and only records which actual parabolic data are meant, exactly as for the published `jacquetFunctor`.

The topology hypotheses are `[TopologicalSpace k]` and `[IsAffineHom G.X.hom]`, with the ambient topology on `rationalPoints G` the published canonical `RationalPointFamily.pointTopology` (installed as the local instance `inductionAmbientPointTopology`, the same instance as `ArbitraryParabolic`'s), and `[NonarchimedeanGroup (rationalPoints G)]`. Induction, the Jacquet comparison and the membership lemma for `V_χ` additionally assume `[LocallyCompactSpace (rationalPoints G)]`; induction and the Jacquet comparison use `[T2Space k]` for closedness of point images. Subgroups carry the induced topology. The split components carry `RationalPointFamily.splitComponentPointTopology`. As in `ArbitraryParabolic`, this covers nonarchimedean local fields of any characteristic and imposes no splitness, `GL_n` or `PadicField` restriction. Representations are `SmoothRep.{0, u, w} ℂ` of the relevant point group, with an independent carrier universe.

## The point-level semidirect decomposition

`pointMap_comp_apply` is functoriality of rational points: `(j ≫ p)(k)(y) = p(k)(j(k)(y))`. `pointImage_comp_le` deduces `pointImage (j ≫ p) ≤ pointImage p`.

`pointImage_le_normalizer_radical p r hr` proves that the whole parabolic image `pointImage p` normalizes the radical image `pointImage (r ≫ p)`. It specializes the radical's all-test normality (`hr.1.isNormal`) at `Spec k` to an arbitrary point `x` of `P` and a point of the range of `r`, and maps the resulting conjugation equality through `p(k)`. No point-level normality is assumed.

`lift_comp_subgroupMultiplication` identifies the multiplication morphism on rational points: `(x, y) ↦ l(k)(x) · r(k)(y)`. From `hmul`:

- `eq_and_eq_of_pointMultiplication` cancels the isomorphism as a monomorphism and compares the two projections, so `l(k)(x) r(k)(y) = l(k)(x') r(k)(y')` forces `x = x'` and `y = y'`;
- `exists_pointMultiplication` writes every `q ∈ P(k)` as `l(k)(x) r(k)(y)`, taking `(x, y) = q ≫ (subgroupMultiplication l r)⁻¹` followed by the projections.

`isSemidirectDecomposition_pointImage p l r hp hr hmul` concludes, for a closed subgroup `p`, the published `IsSemidirectDecomposition (pointImage p) (pointImage (l ≫ p)) (pointImage (r ≫ p))`: both images lie in the parabolic image, the parabolic image normalizes the radical image, and the two images are complements inside it (`Subgroup.isComplement'_of_disjoint_and_mul_eq_univ`). Disjointness uses injectivity of `p(k)`, which follows from the monomorphism underlying the closed immersion, and uniqueness of the factorization. Surjectivity of multiplication uses the existence of the factorization. This is the point-level content of `P = MN` used in VI.1.2; it is derived here from the scheme-level hypotheses rather than assumed.

## Normalized parabolic induction

`inductionFunctor p l r hp hr hl hmul` is an abbreviation for the published

`normalizedInductionFunctor (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul) (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)`,

a functor `SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p)) ⥤ SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`. It inflates along the actual projection of the parabolic image onto the Levi image, twists by the published `inductionCharacter` and takes smooth induction from the parabolic image. Closedness of the radical image is the published `isClosed_pointImage_comp` from `ArbitraryParabolic`.

The twist is the positive square root of the modulus of conjugation by the parabolic image on the closed radical image, taken on the whole parabolic image. The published `Parabolic` documentation records that this agrees with Renard's `i_P^G(τ) = Ind_P^G(τ ⊗ δ_P^{-1/2})` (with his inverted `δ_P`) when the radical image satisfies `IsUnimodularModulus`, which follows from `IsLimitOfCompactSubgroups` (Renard V.5.2(iii) for actual unipotent radicals). That unimodularity is not proved in this module for an arbitrary represented radical. On points of the central split component `A_G`, conjugation is trivial and the twist is `1` with either convention; that is the case used by the VII.1.1 lemma.

## Levi and group exponents

For any `j : M ⟶ G` (in VII.1.1, `j = l ≫ p`), a split component `a`, `ha : IsSplitComponent a`, a smooth `W` of `pointImage j` and `ψ : A(k) →* ℂˣ`:

- `leviWeightSpace j ha W ψ` is the published `generalizedWeightSpace` of `W` for the central point map `splitComponentPointsMap j a` (centrality: `splitComponentPointsMap_mem_center`). It is Renard's `W_ψ`: the union over compact open subgroups of the fixed generalized-character spaces, with a single power uniform in the torus point;
- `IsLeviExponent j ha W ψ` is the published `IsGeneralizedWeight`: `ψ` has open kernel for the canonical topology of `A(k)` and `leviWeightSpace j ha W ψ ≠ ⊥` (`isLeviExponent_iff_isOpen_ker_and`);
- `leviExponents j ha W` is the set of these characters, Renard's `Exp(A_M, W)` (`mem_leviExponents`).

For the whole group, with `aG` and `haG : IsSplitComponent aG`, a smooth `V` of `rationalPoints G` and `χ : AG(k) →* ℂˣ`:

- `groupWeightSpace haG V χ` is `generalizedWeightSpace` for `rationalPoints.map aG`, central by `haG.isCentralSplitTorus.isCentral.map_mem_center`; it is Renard's `V_χ` for the `A_G` action;
- `IsGroupExponent haG V χ` (open kernel and nonzero weight space, `isGroupExponent_iff_isOpen_ker_and`) and `groupExponents haG V`, Renard's `Exp(A_G, V)` (`mem_groupExponents`);
- `mem_groupWeightSpace` (with local compactness) is the published `mem_generalizedWeightSpace_of_isSmooth` specialized to smooth `V`: `x ∈ V_χ` if and only if `∃ d : ℕ, ∀ t, ((V(aG(k)(t)) - χ(t) • 1)^d) x = 0`. The compact-open fixed-vector clause is removed by smoothness; the power remains uniform.

These definitions are stated for all smooth representations; Renard's VII.1.1 uses them for admissible ones. `IsGroupExponent haG ((inductionFunctor p l r hp hr hl hmul).obj W) χ` therefore expresses `(i_P^G W)_χ ≠ {0}` for the actual induced representation.

## Comparison with the published normalized Jacquet exponents

`normalizedJacquetWeightSpace_eq_leviWeightSpace` and `normalizedJacquetExponents_eq_leviExponents` prove by `rfl` that the published `normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ` and `normalizedJacquetExponents ... ha π` are exactly `leviWeightSpace (l ≫ p) ha ((jacquetFunctor p l r hp hr hl hmul).obj π) χ` and `leviExponents (l ≫ p) ha (...)`. Thus Renard's `Exp(A, r_P^G V)` is `Exp(A_M, W)` for the Levi representation `W = r_P^G V`, the identification used in part (ii) of the lemma.

## Source correspondence and provenance

| Renard VII.1.1 / VI.1.2 | Lean declaration |
| --- | --- |
| `P = MN` on points | `isSemidirectDecomposition_pointImage` and its factorization lemmas |
| `i_P^G` | `inductionFunctor` (published `normalizedInductionFunctor`) |
| `W_ψ`, `Exp(A_M, W)` | `leviWeightSpace`, `IsLeviExponent`, `leviExponents` |
| `V_χ`, `Exp(A_G, V)` | `groupWeightSpace`, `IsGroupExponent`, `groupExponents`, `mem_groupWeightSpace` |
| `Exp(A, r_P^G V) = Exp(A_M, r_P^G V)` | `normalizedJacquetExponents_eq_leviExponents` |

The point-level decomposition, the functor wrapper and the two weight-space packagings are derived implementation content, needed to formulate (VII.1.1.1), the `P = G` remark and the lemma for an arbitrary represented parabolic. Their definitions agree with Renard's at admissible inputs and extend them to smooth ones. This unit does not establish admissibility of `i_P^G` or `r_P^G`, the characteristic-space decompositions, finiteness of exponents for finite length, the comparison with III.1.10, the inclusion `A_G ⊂ A_M`, or either part of the lemma. Those are separate statements.
