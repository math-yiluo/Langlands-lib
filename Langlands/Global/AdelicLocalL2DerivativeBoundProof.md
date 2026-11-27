# Local `L²` bounds for the archimedean derivatives of `K_∞`- and `𝔷`-finite functions: proof

Module `Langlands.Global.AdelicLocalL2DerivativeBoundProof`, namespace `Langlands.Global`.

| Declaration | Kind |
| --- | --- |
| `adelicIteratedDirectionalValue_mul_ofInfinite` | theorem |
| `exists_lintegral_infiniteSlice_le` | theorem |
| `adelicLocalL2DerivativeBound` | theorem |

```
theorem Langlands.Global.adelicLocalL2DerivativeBound : AdelicLocalL2DerivativeBoundStatement
```

The main theorem proves the Library statement `AdelicLocalL2DerivativeBoundStatement` (module
`Langlands.Global.AdelicLocalL2DerivativeBoundStatement`) with no further hypotheses. It uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`. The statement and its sources are
explained in `AdelicLocalL2DerivativeBoundStatement.md`; the proof below does not use a smooth
reproducing kernel. It uses the elliptic equation behind Harish-Chandra's theorem directly, as
the Library proof of `AdelicReproducingKernelStatement` does.

## Slices

`adelicIteratedDirectionalValue_mul_ofInfinite hsmooth D Φ g t`: for a word `D` of tangent
directions of `G(F_∞)`, a function `Φ` on `G(𝔸)`, `g ∈ G(𝔸)` and `t ∈ G(F_∞)`,

`adelicIteratedDirectionalValue hsmooth D Φ (g · t) = (D_{X₁} ⋯ D_{X_r} u)(t)` with
`u(x) = Φ(g · x)`,

where `D_X = groupDirectionalValue` is the left-invariant derivative along `X` for the smooth
structure `smoothChartedSpace F G hsmooth` and the right side is the right fold of `D` over
`groupDirectionalValue`. *Proof.* Induction on `D`. For `X :: s`, both sides are the derivative at
`1` along `X` of `h ↦ (s-derivative)(g · t · h)`; by the induction hypothesis at `t h` and
`ofInfinite (t h) = ofInfinite t · ofInfinite h`, the two functions of `h` agree.

## From archimedean slices to `G(𝔸)`

`exists_lintegral_infiniteSlice_le F G L hLo hV`: for an open subgroup `L` of `G(𝔸_f)` and a
compact `V ⊆ G(F_∞)` there are a compact `S ⊆ G(𝔸)` and `c ≥ 0` such that every continuous
`φ : G(𝔸) → ℂ` fixed on the right by `L` satisfies, for every `g`,

`∫⁻_V ‖φ(g · x)‖ₑ² dx ≤ c · ∫⁻_S ‖φ(g s)‖ₑ² ds`

for the Haar measures of `G(F_∞)` and `G(𝔸)`.

*Proof.* Let `U = L ∩ K_f` for the Library's compact open subgroup
`FiniteAdelicGroupPoints.compactOpenSubgroup`; `U` is compact, open and of positive finite Haar
measure. Let `e = split F G : G(𝔸) ≃ G(F_∞) × G(𝔸_f)` and `S = e⁻¹(V × U)`, compact. The
pushforward `ν` of the product of the Haar measures under `e⁻¹` is a Haar measure on `G(𝔸)`, so
`ν = c₀ · haar` (`Measure.isMulLeftInvariant_eq_smul`). Changing variables along `e⁻¹`
(`lintegral_map_equiv`), restricting to the rectangle (`Measure.prod_restrict`) and applying
Tonelli (`lintegral_prod`),

`∫⁻_S ‖φ(g s)‖ₑ² dν = ∫⁻_V ∫⁻_U ‖φ(g · x · b)‖ₑ² db dx = μ_f(U) · ∫⁻_V ‖φ(g · x)‖ₑ² dx`,

since `e⁻¹(x, b) = ofInfinite x · ofFinite b` and `φ` is right `U`-invariant. Hence the claim holds
with `c = μ_f(U)⁻¹ c₀`.

## The main theorem

Fix the data of the statement and a word `D`.

1. *The elliptic equation.* As in the Library proof of `AdelicReproducingKernelStatement`:
   `ofRationalSmoothFunction` puts `Φ` in the space of plot-smooth rational functions, the
   finiteness comparisons `isInfiniteSubgroupFiniteFunction_evaluate_iff` and
   `isCenterFiniteFunction_evaluate_iff` give `K_∞`- and `𝔷`-finiteness there, `K_∞` is maximal
   compact in `G(F_∞)` (`IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite`), and
   `exists_elliptic_slice_annihilator` (with `adelicAdaptedCasimir`) gives one elliptic word
   operator `lieWordAction X (Ptop + Plow)` of positive order that annihilates every archimedean
   slice of `Φ`.
2. *The local estimate.* `exists_lieWord_derivative_l2_evaluation` (module
   `Langlands.Geometry.Manifold.LieGroupEllipticDerivativeL2`), for the Haar measure of `G(F_∞)`,
   the directions `i ↦ D.get i` and the word `List.finRange D.length`, gives a compact `V` and
   `C < ∞`.
3. *The slice through `g`.* With `a`, `b` the archimedean and finite components of `g`, the
   function `u(x) = Φ(g · x)` is the left translate by `a` of the slice of `Φ` at `b`; it is smooth
   (`isPlotSmooth_iff_contMDiff`) and solves the equation, because word operators commute with left
   translation (`lieWordAction_leftTranslation`). By the slice lemma at `t = 1` and
   `foldr_groupDirectionalValue_eq_lieWordDerivative`,
   `‖D Φ(g)‖ₑ ≤ C ‖u‖_{L²(V)}`.
4. *Squares and the adelic integral.* `‖u‖_{L²(V)}² = ∫⁻_V ‖Φ(g · x)‖ₑ² dx`
   (`eLpNorm_nnreal_pow_eq_lintegral`), and `exists_lintegral_infiniteSlice_le`, for the open
   subgroup of `G(𝔸_f)` fixing `Φ` given by smoothness, bounds this by `c ∫⁻_S ‖Φ(g s)‖ₑ² ds`.
   Hence `‖D Φ(g)‖ₑ² ≤ C² c ∫⁻_S ‖Φ(g s)‖ₑ² ds`, which is the statement with the constant
   `C.toNNReal² · c` and the compact set `S`.
