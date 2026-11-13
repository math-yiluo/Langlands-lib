# Proof of `MoyPrasadBoundedOpenStatement`

`Langlands.Geometry.Building.moyPrasadBoundedOpen` proves the published statement
`Langlands.Geometry.Building.MoyPrasadBoundedOpenStatement.{u}` (module
`Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement`) at an arbitrary universe `u`.
The hypotheses are unchanged. This is the opening sentence of Kaletha–Prasad Proposition 13.2.5,
restricted to finite depths, for supplied data.

## What is proved

Fix a nonarchimedean local field `F`, a group scheme `G` over `Spec F` with
`IsAffineHom G.X.hom`, supplied building data `P : ParahoricBuildingData G` with
`P.SatisfiesApartmentAxioms`, and a supplied filtration `Zf : P.CentralizerFiltration` with
`Zf.SatisfiesFiltrationAxioms` and `Zf.IsOpenFiltration`. Then for every apartment point `x` and
every `r : ℝ≥0`, the Moy–Prasad subgroup `Zf.moyPrasad x r` is open in `G(F)`, and it is
algebraically bounded in `G(F)` (`IsAlgebraicallyBounded F G.X`). `G(F)` carries the canonical
topology `rationalPointTopology F G.X`.

## The implemented proof

The proof introduces all binders and returns the pair of two published results of
`Langlands.Geometry.Building.MoyPrasadTopology`:

1. **Openness.** `CentralizerFiltration.isOpen_moyPrasad`, applied to
   `hP.topologyCompatible` (axiom V 7, a field of the apartment axioms) and to the openness
   hypothesis `Zf.IsOpenFiltration`. That lemma rewrites
   `Zf.moyPrasad x r = j(Z(F)_r) ⊔ sharpFiltration x r` through
   `KPApartmentData.sharpFiltration_eq_iSup` as `j(Z(F)_r) ⊔ ⨆ a, U_{a,x,r}`. It then applies
   the proved KP Corollary 8.2.6, `RelativeRoot.openRootCentralizerGeneration`, with
   `V a = U_{a,x,r}` and `Z' = Z(F)_r`. Each `U_{a,x,r}` lies in its root group
   (`filtration_le_rootGroup`) and is open there by V 7
   (`ValuationBuildingData.filtrationOpenSubgroup`); `Z(F)_r` is open by `Zf.IsOpenFiltration`.
2. **Boundedness.** `CentralizerFiltration.isAlgebraicallyBounded_moyPrasad`, applied to the
   apartment axioms `hP`. That lemma chains three containments: `P_{x,r} ≤ P_x`
   (`CentralizerFiltration.moyPrasad_le_parahoricAt`), then `P_x ≤ G(F)^1 ∩ G(F)_x`
   (`ParahoricBuildingData.parahoricAt_le_compactStabilizer`, using V 7). The norm-one fixer
   `G(F)^1 ∩ G(F)_x` is bounded by
   `ValuationBuildingData.isAlgebraicallyBounded_compactStabilizer_apartmentMap`. Its inputs
   are the proved KP Corollary 7.3.14 for one point,
   `ValuationBuildingData.sharpFixerBoundedness`, and boundedness of the image of the
   centralizer norm kernel,
   `ValuationBuildingData.isAlgebraicallyBounded_image_centralizerNormKernel`. Monotonicity,
   `IsAlgebraicallyBounded.mono`, then gives boundedness of `P_{x,r}`.

The topology instances agree definitionally. The statement installs
`isAffine_of_isAffineHom G.X.hom` and `rationalPointTopology F G.X` through `letI`, and
`MoyPrasadTopology` uses the same terms as local instances. `Zf.IsOpenFiltration` is passed
unchanged as a proposition.

## Hypotheses not used

The premise `Zf.SatisfiesFiltrationAxioms` (commutator friendliness, normalizer stability,
commutator filtration and root compatibility) is not used. Boundedness also does not use
`Zf.IsOpenFiltration`.

## Checks

`lean_check` compiles the module with no errors or warnings. The theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023)
(`kaletha-prasad-2023-bruhat-tits-new-approach`): Proposition 13.2.5, opening sentence
(printed p.469). The proof route uses the Library's formalizations of Corollary 8.2.6 (printed
p.291) and Corollary 7.3.14 (printed p.251). It is a composition of published Library results
and adds no source assertion.
