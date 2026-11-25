/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
variable {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
variable (R : Sheaf J CommRingCat.{u})
local notation "C" => tensorResolutionSiteModules R
noncomputable local instance TensorResolutionComparisonFormula_localInst1 : MonoidalCategory C :=
  SheafOfModules.monoidalCategory R

/-- The comparison hom is the four-map zigzag, without unfolding tensor totalizations.

Source: Stacks Tags 06YT and 08DX(2), the specified comparison through a common
K-flat resolution. This is the defining formula: the first and third homology
maps are inverted, and the second and fourth are composed in order.

(blueprint: new-h4-qcoh-tensor-comparison-hom-formula) -/
theorem tensorResolutionComparison_hom
    (E K M F N : CochainComplex C ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (hE : E.IsKFlatTensor) (hK : K.IsKFlatTensor) (hF : F.IsKFlatTensor)
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (tensorResolutionComparison R E K M F N r q s hE hK hF hr hq hs i).hom =
      (let a := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor C) (.up ℤ)
       let b := HomologicalComplex.mapBifunctorMap r (𝟙 F) (curriedTensor C) (.up ℤ)
       let c := HomologicalComplex.mapBifunctorMap q (𝟙 F) (curriedTensor C) (.up ℤ)
       let d := HomologicalComplex.mapBifunctorMap (𝟙 K) s (curriedTensor C) (.up ℤ)
       letI : QuasiIso a := tensorResolution_quasiIso_tensor_left s hs hE
       letI : QuasiIso c := tensorResolution_quasiIso_tensor_right q hq hF
       inv (HomologicalComplex.homologyMap a i) ≫
         HomologicalComplex.homologyMap b i ≫
           inv (HomologicalComplex.homologyMap c i) ≫ HomologicalComplex.homologyMap d i) := by
  unfold tensorResolutionComparison
  rfl

end
end AlgebraicGeometry
