# Gluing a deformation from an obstruction-cone cocycle, and extracting the cochain

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityGluing`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`). Everything is proved in the file, with no
hypotheses beyond those in the signatures. Internal construction, the geometric half of the
necessity direction (the converse of the published `Sufficiency.exists_lift`); no
literature statement is formalized.

Setting as in `Sufficiency` (section `Core`): `f : X ⟶ Spec R` separated; an ordered affine
cover `K` of `relSpace f P`; a `P`-algebra `A₀`; units `g` on the pairwise intersections of
`K`; a test `q : A →ₐ[R] B`, `χ : A₀ →ₐ[R] B` with `hqρ : q ∘ (P → A) = χ ∘ (P → A₀)`; an
`A₀`-module `M` with `jM : M →ₗ[P] A` whose range is `ker q` (`hjMr`) and square-zero
products (`hjMsq`); `T = testCover f K A`.

## Ring identities and simplices

- `unitOfSq x hx`: the unit `1 + x` for `x * x = 0`.
- `edge_eq`, `lt_of_idx_one`, `res_cochain_congr₁`: bookkeeping for `1`-simplices.
- `glue_core`: if `x_ab = P_ab I_ab - 1`, `Z = G01 G12 I02 - 1` with `G_ab I_ab = 1`,
  `x12 - x02 + x01 + Z = 0` and the products `x01 x12`, `x01 Z`, `x12 Z` vanish, then
  `P01 P12 = P02`.
- `extract_core`: if `G I = 1`, `a_i R = G (1 + C) a_j`, `(a_i - 1)(R I - 1) = 0` and
  `C (a_j - 1) = 0`, then `C = (a_i - 1) - (a_j - 1) + (R I - 1)`.

## The glued transition functions

For an ideal `I` of `A` with square-zero products and a `1`-cochain `C` of the structure
sheaf on `T` with values in the extension of `I`:

- `corrPair C i j`: for `i < j` the restriction of `C` on the edge `(i, j)` to
  `T.U i ⊓ T.U j`, else `0` (`corrPair_mem`, `corrPair_sq`, `res_corrPair`).
- `corrUnits`: `G i j (1 + corrPair C i j)` for `i < j` (else `1`), where `G` is `g` pushed to
  `T` (`pairUnitsAlong`); `glueUnits := altExt corrUnits` (`AltCocycle`), with
  `glueUnits_of_lt`.
- `cvec_glueUnits`: `cvec f K g (glueUnits …) = C` (`cvec` from `Sufficiency`).
- `compMap_mem`, `glueC c`: the case `I = ker q`, `C = compMap f K jM 1 c` for
  `c ∈ C¹ ⊗ M`.

## The cocycle condition and the deformation

- `glueC_pr_cocycle`: if `d c + φ_* z = 0` with `φ = phiQ …` (the obstruction map of
  `Sufficiency`), the glued units satisfy the cocycle identity on every ordered triple. The
  proof evaluates `compMap` of this identity on a triple (`compMap_dif`, `d_one_apply`,
  `compMap_natural`, `compMap_zObs`), expresses the faces through `res_cvec_face`, and
  applies `glue_core`.
- `isCocycle_glueC`: `glueC c` is a cocycle (`isCocycle_altExt` at `tripleIdx`).
- `glueC_reduction`: for `i < j`, the pullback of `glueC c i j` along `relMap f q` is `g i j`
  pushed along `relMap f χ ≫ relMap f (P → A₀)` (the correction lies in the extension of
  `ker q`, which `ker_appLE_eq_map` identifies with the kernel of the reduction).
- `isTransition_genSec`: the generators `genSec` of a glued sheaf have the cocycle as
  transition functions.
- `exists_deformation`: if `d c + φ_* z = 0`, there are a line bundle `N` on `relSpace f A`
  (the sheaf `CocycleGluing.glued (glueC c)`), frames `fN i` on `T.U i` with transitions
  `glueC c`, and an isomorphism `φ : (relMap f χ)^* L₀ ≅ (relMap f q)^* N` with coordinate
  `1` on each frame (`FrameCoord.HasCoord … 1`), given frames `e` of a line bundle `L₀` on
  `relSpace f A₀` with transitions `g` pushed to `testCover f K A₀` (`hge`). The
  isomorphism comes from `exists_iso_of_gauge` with the gauge `1`, which intertwines the two
  families of transition functions by `glueC_reduction` and
  `LineHom.isGaugeFamily_iff_of_lt`.

## Extraction from a lift

- `exists_derivation_of_lift`: for `χ' : A₀ →ₐ[R] A` with `q ∘ χ' = χ` there is an
  `R`-derivation `δ : P → M` with `jM (δ p) = χ' (π p) - (P → A) p`.
- `exists_b_of_lift` (`f` flat): given the data of `exists_deformation`, a linear map
  `D'' : F → M`, a lift `χ'` with `q ∘ χ' = χ` and `χ' ∘ π = rhoCorr jM hjMsq D'' D`
  (`Sufficiency`), and an isomorphism `ψ : (relMap f χ')^* L₀ ≅ (𝟙)^* N` whose transport
  along `relMap f q` is `φ`, there is `b ∈ C⁰ ⊗ M` with
  `c = (dif 0 ⊗ M) b + D''_* θ`. Proof: the coordinates `a i` of `ψ` with respect to the
  pulled-back frames (`LineHom.frameHomEquiv`) form a gauge family; their reductions are the
  coordinates `1` of `φ` (`HasCoord.tr`, `HasCoord.unique`), so `1 - a i` lies in the
  extension of `ker q` and defines `b` (`exists_compMap_eq_iff`); on each edge the gauge
  relation and `compMap_thetaObs_ev` give, by `extract_core`, the value of `c`; conclude
  with `compMap_injective`.
