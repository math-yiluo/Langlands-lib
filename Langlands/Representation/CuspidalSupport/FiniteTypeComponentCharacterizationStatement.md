# Characterization of representations of finite type: statement

Author: Worker 6. Module `Langlands.Representation.CuspidalSupport.FiniteTypeComponentCharacterizationStatement`, namespace `Langlands.CuspidalSupport`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.10.7, Lemma (printed p.215 / PDF p.221) and Proposition (printed p.216 / PDF p.222, proof continued on printed p.217 / PDF p.223). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

For `(τ, E) ∈ M(G)`, Renard writes `E_𝔰` for the component of `E` in `M(G)_𝔰` (Bernstein decomposition VI.7.2).

- **Lemma.** If `(τ, E)` is of finite type, then `E_𝔰 = 0` except for finitely many `𝔰 ∈ B(G)`.
- **Proposition.** `(τ, E)` is of finite type if and only if it is `ℨ(G)`-admissible and has nonzero components in only finitely many `M(G)_𝔰`.

## The Lean statement

`FiniteTypeComponentCharacterizationStatement` is a statement unit: nothing is proved. It uses the published standard-family framework (modules `BernsteinData` and `BernsteinBlock`, Worker 1153). It quantifies over:

- a nonarchimedean local field `F : Type uF`;
- `G` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, with `G(F)` locally compact and nonarchimedean in the canonical topology `pointTopology`;
- `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν`;
- a smooth representation `τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)`, at the carrier universe of the published blocks.

The conclusion is an equivalence. The left side is `Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) τ.representation.asModule` (finite type). The right side is the conjunction of:

1. **`ℨ(G)`-admissibility.** For every compact open `K : OpenSubgroup (rationalPoints G)`, there are finitely many `K`-fixed vectors `s_j` such that every `K`-fixed vector is `∑ j, SmoothRep.hom ((z j).app τ) (s j)` with `z j ∈ CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))`. This is the formulation of the companion VI.10.7 Theorem statement `FiniteTypeCenterAdmissibleStatement` (Worker 6, candidate `e9b7e8ee-d4da-4c47-a6ad-76d84a3d0e18`).
2. **Finitely many components.** The set of `s : BernsteinInertialClass i ν family` such that some `π` is an actual subquotient of `τ` (published `SmoothRep.IsSubquotient`) with `IsBernsteinInertialSupport i ν family s π` is finite.

### Why condition 2 expresses "finitely many nonzero components"

Bernstein decomposition is not available as a published construction, so the components `E_𝔰` cannot be named. Condition 2 replaces "`E_𝔰 ≠ 0`" by "some irreducible subquotient of `E` has inertial support `𝔰`". These agree given the decomposition. A nonzero `E_𝔰` has an irreducible subquotient, which lies in `M(G)_𝔰`. Conversely, an irreducible subquotient of `E` with support `𝔰` is a subquotient of `E_𝔰`, because the decomposition is a direct product of categories. This identification is not formalized. With it, the forward implication contains the Lemma (and the VI.10.7 Theorem), and the equivalence is the Proposition.

## Remarks

- The published inertial support is the induction-occurrence relation of `BernsteinBlock`. Its comparison with the Jacquet-defined cuspidal support is the support-uniqueness obligation recorded there.
- The proof (the Lemma, the VI.10.7 Theorem, and for sufficiency a compact open `K` as in the VI.10.6 Corollary together with the equivalence of VI.10.6 (ii)) is not formalized here.
