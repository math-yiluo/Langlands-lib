import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageStatement
import Langlands.BruhatTits.IntegralModels.ConnectedImage.Integers
import Langlands.GroupScheme.Torus.WeilRestrictionGeometricallyConnected
import Langlands.GroupScheme.Torus.WeilRestrictionSplitNorm
import Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel
import Langlands.GroupScheme.Torus.GaloisNormRational

/-! # Proof: the torus Iwahori subgroup is the image of a connected smooth model

Let `K = inertiaFixedField F`, `O = fixedFieldIntegers F`, and let `L / K` be a finite Galois
intermediate field of `F^sep / K` splitting the torus `T`, with `σ : T_L ≅ 𝔾ₘ^I`. Write `O_L`
for the valuation ring of `L`. The source group is `S = Res_{(I → L)/K} 𝔾ₘ`, its model is
`Res_{(I → O_L)/O} 𝔾ₘ`, and the homomorphism `S ⟶ T` is the composite of the map
`S ⟶ Res_{L/K} T_L` given by the split coordinates with the algebraic norm. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace ConnectedImage

section Model

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L]
  (I : Type u) [Fintype I] [DecidableEq I]

/-- `I → O_L` is a projective `O`-module, being free. -/
local instance piIntegersProjective :
    Module.Projective (fixedFieldIntegers F) (I → integers F L) :=
  Module.Projective.of_free

/-- The model `Res_{(I → O_L)/O} 𝔾ₘ` of `Res_{(I → L)/K} 𝔾ₘ`. -/
abbrev model : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) (I → L)) :=
  WeilGm.integralModel (fixedFieldIntegers F) (inertiaFixedField F) (I → integers F L) (I → L)
    (piTensorEquiv F L I)

/-- A rational point of `Res_{(I → L)/K} 𝔾ₘ` is integral for the model exactly when all
coordinates of the corresponding unit of `I → L` have valuation one. -/
theorem mem_model_integralPoints_iff
    (y : rationalPoints (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) (I → L))) :
    y ∈ (model F L I).integralPoints ↔
      ∀ i, intermediateValuation F L
        ((WeilGm.rationalUnitsEquiv (inertiaFixedField F) (I → L) y : I → L) i) = 1 := by
  rw [WeilGm.mem_integralModel_integralPoints_iff]
  constructor
  · rintro ⟨u, hu⟩ i
    rw [hu, piTensorEquiv_tmul, map_one, one_mul]
    exact (isUnit_integers_iff F L _).mp (MulEquiv.piUnits u i).isUnit
  · intro h
    let w : I → integers F L := fun i =>
      ⟨(WeilGm.rationalUnitsEquiv (inertiaFixedField F) (I → L) y : I → L) i,
        (mem_integers_iff F L _).mpr (le_of_eq (h i))⟩
    have hw : ∀ i, IsUnit (w i) := fun i => (isUnit_integers_iff F L (w i)).mpr (h i)
    refine ⟨MulEquiv.piUnits.symm fun i => (hw i).unit, ?_⟩
    funext i
    rw [piTensorEquiv_tmul, map_one, one_mul]
    rfl

end Model

section Points

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [FiniteDimensional (inertiaFixedField F) L] [IsGalois (inertiaFixedField F) L]
  (I : Type u) [Fintype I] [DecidableEq I]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffine T.X.left]
  [IsAffine (baseChanged (inertiaFixedField F) L T.toGrp).X.left]
  [LocallyOfFiniteType (baseChanged (inertiaFixedField F) L T.toGrp).X.hom]
  (σ : baseChanged (inertiaFixedField F) L T.toGrp ≅ splitTorus (Spec (CommRingCat.of L)) I)

/-- The homomorphism `Res_{(I → L)/K} 𝔾ₘ ⟶ T`: split coordinates followed by the norm. -/
def normMap : WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) (I → L) ⟶ T.toGrp :=
  WeilGm.splitWeilHom (inertiaFixedField F) L I (baseChanged (inertiaFixedField F) L T.toGrp) σ ≫
    GaloisNorm.norm (inertiaFixedField F) L T

/-- The point of `T(L)` attached to a rational point of `Res_{(I → L)/K} 𝔾ₘ`: its split
coordinates are the coordinates of the corresponding unit of `I → L`. -/
def splitPoint
    (y : rationalPoints (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) (I → L))) :
    rationalPoints (baseChanged (inertiaFixedField F) L T.toGrp) :=
  rationalPoints.map σ.inv
    ((splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))).symm
      (fun i => Units.map (Pi.evalMonoidHom (fun _ : I => L) i)
        (WeilGm.rationalUnitsEquiv (inertiaFixedField F) (I → L) y)))

omit [DecidableEq I] in
/-- On rational points, the homomorphism is the rational norm of `splitPoint`. -/
theorem map_normMap
    (y : rationalPoints (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) (I → L))) :
    rationalPoints.map (normMap F L I T σ) y =
      rationalNorm (inertiaFixedField F) L T (splitPoint F L I T σ y) := by
  have h : rationalPoints.map (normMap F L I T σ) y =
      rationalPoints.map (GaloisNorm.norm (inertiaFixedField F) L T)
        (rationalPoints.map (WeilGm.splitWeilHom (inertiaFixedField F) L I
          (baseChanged (inertiaFixedField F) L T.toGrp) σ) y) := by
    simp only [normMap, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [h, ← MulEquiv.apply_symm_apply (GaloisNorm.rationalPointsEquiv (inertiaFixedField F) L T)
    (rationalPoints.map _ y), GaloisNorm.norm_rationalPoints]
  congr 1
  simp only [GaloisNorm.rationalPointsEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  exact WeilGm.rationalCoeffEquiv_symm_basePointsEquiv_splitWeilHom _ _ _ _ σ y

omit [IsAffine T.X.left] [IsAffine (baseChanged (inertiaFixedField F) L T.toGrp).X.left]
  [LocallyOfFiniteType (baseChanged (inertiaFixedField F) L T.toGrp).X.hom] in
/-- The image of the integral points under `splitPoint` is the character-valuation kernel. -/
theorem mem_characterValuationKernel_iff_exists (x : rationalPoints
    (baseChanged (inertiaFixedField F) L T.toGrp)) :
    x ∈ characterValuationKernel (intermediateValuation F L)
        (baseChanged (inertiaFixedField F) L T.toGrp) ↔
      ∃ y ∈ (model F L I).integralPoints, splitPoint F L I T σ y = x := by
  constructor
  · intro hx
    rw [WeilGm.mem_characterValuationKernel_iff_of_iso σ] at hx
    let t := splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of L)))
      (rationalPoints.map σ.hom x)
    let y := (WeilGm.rationalUnitsEquiv (inertiaFixedField F) (I → L)).symm
      (MulEquiv.piUnits.symm t)
    have hy : (fun i => Units.map (Pi.evalMonoidHom (fun _ : I => L) i)
        (WeilGm.rationalUnitsEquiv (inertiaFixedField F) (I → L) y)) = t := by
      funext i
      apply Units.ext
      simp only [y, MulEquiv.apply_symm_apply]
      rfl
    refine ⟨y, ?_, ?_⟩
    · rw [mem_model_integralPoints_iff]
      intro i
      simp only [y, MulEquiv.apply_symm_apply]
      exact hx i
    · rw [splitPoint, hy]
      simp only [t, MulEquiv.symm_apply_apply]
      rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc,
        ← Grp.comp_hom_hom, σ.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  · rintro ⟨y, hy, rfl⟩
    rw [splitPoint, WeilGm.map_inv_mem_characterValuationKernel_iff]
    rw [mem_model_integralPoints_iff] at hy
    exact hy

/-- The image of the integral points of the model is the torus Iwahori subgroup. -/
theorem map_model_integralPoints :
    (model F L I).integralPoints.map (rationalPoints.map (normMap F L I T σ)) =
      torusNormIwahori (inertiaFixedField F) L (intermediateValuation F L) T := by
  ext t
  rw [Subgroup.mem_map, mem_torusNormIwahori]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨splitPoint F L I T σ y,
      (mem_characterValuationKernel_iff_exists F L I T σ _).mpr ⟨y, hy, rfl⟩,
      (map_normMap F L I T σ y).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_characterValuationKernel_iff_exists F L I T σ x).mp hx
    exact ⟨y, hy, map_normMap F L I T σ y⟩

end Points

end ConnectedImage

open ConnectedImage in
/-- **KP Lemma B.3.1 and Definition 2.5.13.** The torus Iwahori subgroup `T(K)^0` is the image
of the integral points of the smooth model `Res_{(I → O_L)/O} 𝔾ₘ`, which has geometrically
connected fibres, under split coordinates followed by the norm. -/
theorem unramifiedTorusIwahoriConnectedImage :
    UnramifiedTorusIwahoriConnectedImageStatement.{u} := by
  intro F _ _ _ _ T _ L _ _ hsplit
  classical
  obtain ⟨I, hI, ⟨σ⟩⟩ := hsplit
  let : Fintype I := Fintype.ofFinite I
  have hT : IsSplitTorus (baseChanged (inertiaFixedField F) L T.toGrp) := ⟨I, hI, ⟨σ⟩⟩
  have : IsAffineHom (baseChanged (inertiaFixedField F) L T.toGrp).X.hom := hT.isAffineHom
  have : IsAffine (baseChanged (inertiaFixedField F) L T.toGrp).X.left :=
    isAffine_of_isAffineHom (baseChanged (inertiaFixedField F) L T.toGrp).X.hom
  have := hT.smooth
  have : Module.Projective (fixedFieldIntegers F) (I → integers F L) :=
    Module.Projective.of_free
  refine ⟨WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) (I → L), model F L I,
    normMap F L I T σ, ?_, ?_, map_model_integralPoints F L I T σ⟩
  · exact WeilGm.integralModel_isSmooth _ _ _ _ _
  · exact WeilGm.geometricallyConnected (fixedFieldIntegers F) (I → integers F L)

end Langlands.BruhatTits.IntegralModels
