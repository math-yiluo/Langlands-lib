# The centre of a Bernstein block is Noetherian; blocks are indecomposable: statements

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.BernsteinBlockCenterStatements`, namespace `Langlands.CuspidalSupport`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.4, Corollary and Remark 3 after the Theorem, printed p.212 / PDF p.218. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

After proving `ℨ_Ω ≃ ℨ_D^{W(D)}` and the Theorem that the centre of `M(G)_Ω` is the algebra of polynomial functions on the variety `Ω`, Renard states:

- **Corollary.** The centre `ℨ_Ω` of the category `M(G)_Ω` is a Noetherian `ℂ`-algebra, isomorphic to the algebra of regular functions on the quotient of a complex algebraic torus by a finite group.
- **Remark 3.** Corollary VI.4.5 generalizes: the categories `M(G)_Ω` are indecomposable.

## The Lean statements

The module is a statement unit: nothing is proved. Both statements use the published standard-family framework (modules `BernsteinData` and `BernsteinBlock`, Worker 1153). They quantify over:

- a nonarchimedean local field `F : Type uF`;
- `G` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, with `G(F)` locally compact and nonarchimedean in the canonical topology `pointTopology`;
- `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν`;
- a cuspidal datum `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family`.

The component `Ω` is represented by the inertial class `bernsteinInertialClass i ν family a`. `M(G)_Ω` is represented by the published full subcategory `BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)` of smooth representations at the carrier universe `max uF uV`.

- `BernsteinBlockCenterNoetherianStatement`: `IsNoetherianRing (CatCenter M(G)_Ω)`. Mathlib's `CatCenter C` is `End (𝟭 C)`, the centre of the category, with its ring structure from the preadditive structure of the block. This is the same notion as in the published VI.4.5 statement `RationalSummandBlockCenterStatement`. Only Noetherianity is asserted. The parenthetical description as regular functions on a torus quotient is not stated, as it needs the variety structure of `Ω`, which is not available.
- `BernsteinBlockIndecomposableStatement`: for every family `P : Bool → ObjectProperty M(G)_Ω` with `Renard.IsCategoryDecomposition P`, there is `b : Bool` such that every object `X` with `P b X` satisfies `IsZero X`. The published `IsCategoryDecomposition` is Renard's A.IX notion `𝓜 = ∏ᵢ 𝓜ᵢ`: every object is a coproduct of components, and morphisms between distinct components vanish. So one of the two parts is zero, which is indecomposability. The formulation is exactly that of the published VI.4.5 statement `RationalInertiaBlockIndecomposableStatement`, which this remark generalizes.
- `BernsteinBlockCenterStatements` is their conjunction.

## Remarks

- The blocks are defined with the published induction-occurrence support relation. Their comparison with Renard's `M(G)_Ω` is the support-uniqueness obligation recorded in `BernsteinBlock`.
- The VI.10.4 Theorem (`ℨ_Ω` is the algebra of polynomial functions on `Ω`) and `ℨ_Ω ≃ ℨ_D^{W(D)}` are not stated here. They need the variety structure on `Ω(G)` and the action of `W(D)` on `ℨ_D`.
- The proofs are not formalized here.
