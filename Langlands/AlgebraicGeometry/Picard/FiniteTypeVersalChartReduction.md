# Versal Picard charts from formal versality and algebraization

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartReduction`.

Author: Worker 5005, for task `3fa23029-256e-47ed-ad64-e5ea33971b1a`.

This module proves two implications between published statements and
packages the second as a definition. All declarations are in the namespace
`Langlands.AlgebraicGeometry.Picard.PicardGroupoid`, and all schemes are in
one universe `u`. Nothing here proves any of the hypotheses: the statements
`FiniteTypeFormalVersalBundleStatement.{u}`,
`VersalAlgebraizationStatement.{u}` and
`PicardOpennessOfVersalityStatement.{u}` stay explicit hypotheses, so the
target `FiniteTypePicardStackAtlasStatement.{u}` is not proved by this
module.

## Versal charts

`finiteTypeVersalChart_of_formalVersal
(hF : FiniteTypeFormalVersalBundleStatement.{u})
(hA : VersalAlgebraizationStatement.{u}) : FiniteTypeVersalChartStatement.{u}`.

Let `R` be of finite type over `ℤ`, `X` proper and flat over `Spec R`, `K`
a field of finite type over `R` and `L₀` an actual line bundle on
`Spec K ×_R X`.

1. `hF` gives a complete Noetherian local `R`-algebra `A`, a surjective
   `R`-algebra map `ε : A → K`, an actual line bundle `L` on
   `Spec A ×_R X`, a point `p : Spec K ⟶ Spec A` over `Spec R` with
   `p.left = Spec ε`, formal versality of `L` at `p`, and an isomorphism
   `c` from the pullback of `L` along `p` to `L₀`.
2. `hA` applied to exactly these data (`A`, `ε` with its surjectivity, `L`,
   `p` with `p.left = Spec ε`, and the versality of `L` at `p`) gives `U`
   locally of finite type over `Spec R`, an actual line bundle `L'` on
   `U ×_R X`, a point `u₀` with `e : κ(u₀) ≅ K`, a point
   `p' : Spec K ⟶ U` over `Spec R` equal to `Spec e ≫ (Spec κ(u₀) ⟶ U)`,
   formal versality of `L'` at `p'`, and an isomorphism `c'` from the
   pullback of `L'` along `p'` to the pullback of `L` along `p`.
3. The chart is `U`, `L'`, `u₀`, `e`, `p'`, with residue isomorphism the
   composite `c' ≪≫ c` to `L₀`.

## The atlas from the three versality inputs

`finiteTypePicardStackAtlas_of_versalInputs
(hF : FiniteTypeFormalVersalBundleStatement.{u})
(hA : VersalAlgebraizationStatement.{u})
(hO : PicardOpennessOfVersalityStatement.{u}) :
FiniteTypePicardStackAtlasStatement.{u}` composes published reductions:

- `finiteTypeVersalChart_of_formalVersal hF hA` (above) gives
  `FiniteTypeVersalChartStatement.{u}`;
- `versalSmoothNeighbourhood_of_openness hO` (module
  `VersalSmoothNeighbourhoodOfOpenness`) gives
  `VersalSmoothNeighbourhoodStatement.{u}`;
- `finiteTypePointSmoothChart_of_versal` (module
  `FiniteTypePointSmoothChartReduction`) turns the two into
  `FiniteTypePointSmoothChartStatement.{u}`;
- `finiteTypePicardStackAtlas_of_pointSmoothCharts` (module
  `FiniteTypePicardStackAtlasAssembly`) gives the atlas statement.

`finiteTypePicardStackAtlasOfVersalInputs` is the same implication as a
definition of type
`FiniteTypeFormalVersalBundleStatement.{u} → VersalAlgebraizationStatement.{u} →
PicardOpennessOfVersalityStatement.{u} → FiniteTypePicardStackAtlasStatement.{u}`;
its body is the theorem `finiteTypePicardStackAtlas_of_versalInputs`.

## Source

The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, `artin.pdf` (Chapter 98
"Artin's Axioms"). In the proof of Lemma 98.13.8 (Tag 07XY), printed p. 24,
a versal formal object over `x₀` is chosen (Formal Deformation Theory,
Lemma 90.13.4), it is effective by assumption (3) of the lemma, and
Lemma 98.12.7 (Tag 07XH) algebraizes it to an object over a scheme `U` of finite type, versal at a
finite type point `u₀` with residue field `k`, with `x|_{Spec k} ≅ x₀`; then
openness of versality shrinks `U`. The first theorem above is the passage
from the formal object to the algebraized chart, with the two steps given by
the hypotheses `hF` (versal formal object, made effective over the complete
local ring `A`) and `hA` (Lemma 98.12.7 for the Picard stack). The second
theorem chains it with the published formalization of the remaining steps.
