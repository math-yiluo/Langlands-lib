# Characteristic-space decompositions and exponents under induction and restriction

Author: Worker 6. Module `Langlands.Representation.Exponents.ArbitraryParabolicExponentStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `ArbitraryParabolicExponentStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.1.1, printed pp.220–221 / PDF pp.226–227. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The objects are the published definitions of `ArbitraryParabolic` (normalized Jacquet functor, `normalizedJacquetWeightSpace`, `IsNormalizedJacquetExponent`, `normalizedJacquetExponents`) and `ArbitraryParabolicInduction` (`inductionFunctor`, `leviWeightSpace`, `IsLeviExponent`, `groupWeightSpace`, `IsGroupExponent`, `groupExponents`).

## Ambient setting

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published `NormalizedTemperedLogarithmicComparisonStatement`. Representations are `SmoothRep.{0, u, v} ℂ`, with arbitrary carrier universe `v`; induced representations live in `max u v`. Admissibility is the published `SmoothRep.IsAdmissible` (smooth, with finite-dimensional fixed vectors for every open subgroup) and finite length is `SmoothRep.HasFiniteLength` (finite composition length over the group algebra).

A parabolic `P = MN` with split component `A` is given, as in the published definitions, by `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`, `a : A.toGrp ⟶ M` with `hp : IsParabolicSubgroup p`, `hl : IsRationalLeviSubgroup l`, `hr : LeviSubgroup.IsGeometricUnipotentRadical r`, `hmul : IsIso (subgroupMultiplication l r)` and `ha : IsSplitComponent a`. Every such datum is quantified; no existence is asserted. Renard's `A_G` is `aG : AG.toGrp ⟶ G` with `haG : IsSplitComponent aG`.

The statement is the conjunction of three clauses.

## Clause 1: (VII.1.1.1) and finiteness

For all parabolic data as above and every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with `π.IsAdmissible`:

- `iSupIndep` holds for the family `χ ↦ (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule` indexed by the subtype `normalizedJacquetExponents p l r hp hl hr hmul ha π`;
- the supremum of that family is `⊤`;
- if moreover `π.HasFiniteLength`, the set `normalizedJacquetExponents p l r hp hl hr hmul ha π` is finite.

The first two items say that `r_P^G V` is the internal direct sum of its characteristic spaces `(r_P^G V)_χ` over `χ ∈ Exp(A, r_P^G V)`, which is (VII.1.1.1). They are stated for the underlying subspaces of the carrier, so the direct sum is that of vector spaces, as in the source. The third item is Renard's sentence that `Exp(A, r_P^G V)` is finite when `(π, V)` has finite length. Renard derives (VII.1.1.1) from the admissibility of `r_P^G(π)` (Corollary VI.6.1) and the finiteness from VI.6.4 and Schur's lemma. Those results are not hypotheses or conclusions here; the clause assumes only what VII.1.1 assumes of `π`.

## Clause 2: the remark for `P = G`

For every split component `aG`, `haG` of `G` and every admissible `V : SmoothRep.{0, u, v} ℂ (rationalPoints G)`, the family `χ ↦ (groupWeightSpace haG V χ).toSubmodule` over the subtype `groupExponents haG V` is `iSupIndep` with supremum `⊤`. This is the decomposition `V = ⊕_χ V_χ` of the remark. The remark's parenthetical comparison with Proposition III.1.10 is not formalized.

The remark obtains this decomposition by taking `P = G` in (VII.1.1.1). In this framework the whole group is not presented as a represented parabolic with a trivial radical, so the clause is stated directly with `groupWeightSpace`. It is the same characteristic-space construction for the central action of `A_G(F)` on `V`.

## Clause 3: the lemma

For all parabolic data `p, l, r, a` with their hypotheses, all `aG, haG`, and every monoid homomorphism `e : rationalPoints AG.toGrp →* rationalPoints A.toGrp` such that

`∀ t, ((splitComponentPointsMap (l ≫ p) a (e t) : pointImage (l ≫ p)) : rationalPoints G) = rationalPoints.map aG t`,

the following hold.

**(i)** For every `W : SmoothRep.{0, u, v} ℂ (pointImage (l ≫ p))` and `χ : AG(k) →* ℂˣ`, if `W.IsAdmissible` and `groupWeightSpace haG ((inductionFunctor p l r hp hr hl hmul).obj W) χ ≠ ⊥`, then there is `ψ : A(k) →* ℂˣ` with `IsLeviExponent (l ≫ p) ha W ψ` and `ψ.comp e = χ`.

**(ii)** For every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` and `χ : A(k) →* ℂˣ`, if `π.IsAdmissible` and `IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ`, then `IsGroupExponent haG π (χ.comp e)`.

Here `e` is Renard's inclusion `A_G ⊂ A_M` on points, and the premise says it is compatible with the two inclusions into `G(F)`. The restriction of a character to `A_G` is composition with `e`. Part (i) is Renard's "if `(i_P^G W)_χ ≠ {0}`, then `χ` is the restriction to `A_G` of a character `ψ` of `A_M` with `W_ψ ≠ {0}`". The hypothesis is the literal nonvanishing of the characteristic space. No smoothness of `χ` is assumed, and the conclusion includes the open kernel of `ψ` that `IsLeviExponent` requires. Part (ii) is Renard's "the restriction to `A_G` of a character `χ` of `A_M` appearing in the decomposition of `r_P^G V` appears in the decomposition of `V`". By the published `normalizedJacquetExponents_eq_leviExponents`, its hypothesis is `χ ∈ Exp(A_M, r_P^G V)`. Its conclusion `χ.comp e ∈ Exp(A_G, V)` also asserts the open kernel of `χ.comp e`.

The statement quantifies over every compatible `e` and does not assert that one exists. The existence of the inclusion `A_G ⊂ A_M` for actual Levi subgroups is a separate structural obligation.

## Faithfulness notes

- Renard's proof of (i) evaluates an `A_G`-eigenvector `f` of `i_P^G W` at a point where it is nonzero, using `f(xa) = f(ax) = ρ(a) f(x)`. The twist of `inductionFunctor` is trivial at central points, whichever modulus convention is used, as recorded in `ArbitraryParabolicInduction`. The proof of (ii) uses `δ_P(a) = 1` for `a ∈ A_G`. Both are facts about the published definitions, not added hypotheses.
- All characteristic spaces are the published compact-open unions of uniform generalized character spaces. They are therefore Renard's spaces with the single power `d` uniform in the torus point, as in his displayed definition.
- No hypothesis beyond the source's admissibility and finite length is added. The local-compactness and nonarchimedean-group instances for the canonical topology are standard properties of `G(F)` for a local field. They are quantified, not proved, exactly as in the published exponent statements.

## Provenance

This is a source statement of VII.1.1 for the represented-parabolic interface. It reformulates the source in three ways, each documented above: the internal direct sum is written as `iSupIndep` together with `iSup = ⊤` of the underlying subspaces; the `P = G` remark is stated directly for `A_G`; and the inclusion `A_G ⊂ A_M` is a compatible point homomorphism `e`. Casselman's criterion (VII.1.2) and the existence of `e` remain separate obligations.
