/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonFormula

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionComparisonRestrictionNaturality_localInst1
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionComparisonRestrictionNaturality_localInst2
    (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionComparisonRestrictionNaturality_localInst3 (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionComparisonRestrictionNaturality_localInst4
    (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

private theorem tensorResolution_restriction_tensor_square_id_left
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (E F N : CochainComplex Y.Modules ℤ) (E' F' N' : CochainComplex X.Modules ℤ)
    (s : F ⟶ N) (s' : F' ⟶ N')
    (e : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (f : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (t : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N ⟶ N')
    (hss : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s ≫ t = f ≫ s') :
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor Y.Modules) (.up ℤ)) ≫
      tensorResolutionRestrictionTensorMap j E N E' N' e t =
    tensorResolutionRestrictionTensorMap j E F E' F' e f ≫
      HomologicalComplex.mapBifunctorMap (𝟙 E') s' (curriedTensor X.Modules) (.up ℤ) := by
  simpa only [tensorResolutionRestrictionTensorMap, Category.assoc] using
    tensorResolution_restrictedTensor_square j (𝟙 E) s (𝟙 E') s' e e f t (by simp) hss

private theorem tensorResolution_restriction_tensor_square_id_right
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (E M F : CochainComplex Y.Modules ℤ) (E' M' F' : CochainComplex X.Modules ℤ)
    (r : E ⟶ M) (r' : E' ⟶ M')
    (e : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (m : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj M ⟶ M')
    (f : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (hrr : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map r ≫ m = e ≫ r') :
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap r (𝟙 F) (curriedTensor Y.Modules) (.up ℤ)) ≫
      tensorResolutionRestrictionTensorMap j M F M' F' m f =
    tensorResolutionRestrictionTensorMap j E F E' F' e f ≫
      HomologicalComplex.mapBifunctorMap r' (𝟙 F') (curriedTensor X.Modules) (.up ℤ) := by
  simpa only [tensorResolutionRestrictionTensorMap, Category.assoc] using
    tensorResolution_restrictedTensor_square j r (𝟙 F) r' (𝟙 F') e m f f hrr (by simp)

/-- The common K-flat zigzag respects three compatible restriction squares.

Source: Stacks Tags 06YT and 08DX(2), functoriality of comparison through a common
K-flat resolution. Tensor each of the three squares with the appropriate identity
map to obtain the four squares of the comparison zigzag. K-flatness makes the
first and third legs quasi-isomorphisms on both charts. The exact-restriction
homology comparison carries the four squares to homology; cancel the two pairs
of backward isomorphisms using tensorResolution_homology_zigzag. Finally use the
explicit defining equation of tensorResolutionComparison to identify the result.
No boundedness or invertibility of the five vertical chain maps is required.

(blueprint: new-h4-qcoh-tensor-comparison-restriction-naturality) -/
theorem tensorResolutionComparison_restriction {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E K M F N : CochainComplex Y.Modules ℤ)
    (E' K' M' F' N' : CochainComplex X.Modules ℤ)
    (r : E ⟶ M) (q : K ⟶ M) (s : F ⟶ N)
    (r' : E' ⟶ M') (q' : K' ⟶ M') (s' : F' ⟶ N')
    (hE : CochainComplex.IsKFlatTensor (R := Y.sheaf) E)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hE' : CochainComplex.IsKFlatTensor (R := X.sheaf) E')
    (hK' : CochainComplex.IsKFlatTensor (R := X.sheaf) K')
    (hF' : CochainComplex.IsKFlatTensor (R := X.sheaf) F')
    (hr : QuasiIso r) (hq : QuasiIso q) (hs : QuasiIso s)
    (hr' : QuasiIso r') (hq' : QuasiIso q') (hs' : QuasiIso s')
    (e : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (k : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (m : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj M ⟶ M')
    (f : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (t : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj N ⟶ N')
    (hrr : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map r ≫ m =
      e ≫ r')
    (hqq : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q ≫ m =
      k ≫ q')
    (hss : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s ≫ t =
      f ≫ s') (i : ℤ) :
    (Scheme.Modules.restrictFunctor j).map
        (tensorResolutionComparison Y.sheaf E K M F N r q s hE hK hF hr hq hs i).hom ≫
      (((CochainComplex.mapBifunctor K N (curriedTensor Y.Modules)).sc i).mapHomologyIso
        (Scheme.Modules.restrictFunctor j)).inv ≫
      HomologicalComplex.homologyMap (tensorResolutionRestrictionTensorMap j K N K' N' k t) i =
    (((CochainComplex.mapBifunctor E N (curriedTensor Y.Modules)).sc i).mapHomologyIso
        (Scheme.Modules.restrictFunctor j)).inv ≫
      HomologicalComplex.homologyMap (tensorResolutionRestrictionTensorMap j E N E' N' e t) i ≫
      (tensorResolutionComparison X.sheaf E' K' M' F' N' r' q' s'
        hE' hK' hF' hr' hq' hs' i).hom := by
  let R := Scheme.Modules.restrictFunctor j
  let RC := R.mapHomologicalComplex (.up ℤ)
  let a₀ := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor Y.Modules) (.up ℤ)
  let a₁ := HomologicalComplex.mapBifunctorMap r (𝟙 F) (curriedTensor Y.Modules) (.up ℤ)
  let a₂ := HomologicalComplex.mapBifunctorMap q (𝟙 F) (curriedTensor Y.Modules) (.up ℤ)
  let a₃ := HomologicalComplex.mapBifunctorMap (𝟙 K) s (curriedTensor Y.Modules) (.up ℤ)
  let b₀ := HomologicalComplex.mapBifunctorMap (𝟙 E') s' (curriedTensor X.Modules) (.up ℤ)
  let b₁ := HomologicalComplex.mapBifunctorMap r' (𝟙 F') (curriedTensor X.Modules) (.up ℤ)
  let b₂ := HomologicalComplex.mapBifunctorMap q' (𝟙 F') (curriedTensor X.Modules) (.up ℤ)
  let b₃ := HomologicalComplex.mapBifunctorMap (𝟙 K') s' (curriedTensor X.Modules) (.up ℤ)
  let f₀ := tensorResolutionRestrictionTensorMap j E N E' N' e t
  let f₁ := tensorResolutionRestrictionTensorMap j E F E' F' e f
  let f₂ := tensorResolutionRestrictionTensorMap j M F M' F' m f
  let f₃ := tensorResolutionRestrictionTensorMap j K F K' F' k f
  let f₄ := tensorResolutionRestrictionTensorMap j K N K' N' k t
  have h₀ : RC.map a₀ ≫ f₀ = f₁ ≫ b₀ := by
    dsimp only [a₀, b₀, f₀, f₁]
    exact tensorResolution_restriction_tensor_square_id_left j E F N E' F' N' s s' e f t hss
  have h₁ : RC.map a₁ ≫ f₂ = f₁ ≫ b₁ := by
    dsimp only [a₁, b₁, f₁, f₂]
    exact tensorResolution_restriction_tensor_square_id_right j E M F E' M' F' r r' e m f hrr
  have h₂ : RC.map a₂ ≫ f₂ = f₃ ≫ b₂ := by
    dsimp only [a₂, b₂, f₂, f₃]
    exact tensorResolution_restriction_tensor_square_id_right j K M F K' M' F' q q' k m f hqq
  have h₃ : RC.map a₃ ≫ f₄ = f₃ ≫ b₃ := by
    dsimp only [a₃, b₃, f₃, f₄]
    exact tensorResolution_restriction_tensor_square_id_left j K F N K' F' N' s s' k f t hss
  have : QuasiIso a₀ := tensorResolution_quasiIso_tensor_left s hs hE
  have : QuasiIso a₂ := tensorResolution_quasiIso_tensor_right q hq hF
  have : QuasiIso b₀ := tensorResolution_quasiIso_tensor_left s' hs' hE'
  have : QuasiIso b₂ := tensorResolution_quasiIso_tensor_right q' hq' hF'
  have hz := tensorResolution_homology_zigzag R (.up ℤ) i
    a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ f₀ f₁ f₂ f₃ f₄ h₀ h₁ h₂ h₃
  rw [tensorResolutionComparison_hom, tensorResolutionComparison_hom]
  convert hz using 1 <;> simp only [tensorResolutionSiteModules, Scheme.Modules,
    CochainComplex.mapBifunctor, R, a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, f₀, f₄]

end AlgebraicGeometry
