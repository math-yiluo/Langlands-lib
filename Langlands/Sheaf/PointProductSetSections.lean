import Langlands.Sheaf.PointProductSupport
import Langlands.Sheaf.PointSupportSetMaps

/-! # Natural maps and set sections of actual point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.PointProduct

open CategoryTheory CategoryTheory.Limits Opposite

universe wI w v u wR wM

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → J.Point.{max wI w})
variable {R : Type (max wI w)} [CommRing R]

local instance : HasProducts.{wI} (ModuleCat.{max wI w} R) := by
  let := hasLimitsOfSizeShrink.{wI, wI} (ModuleCat.{max wI w} R)
  infer_instance

variable {M N P : I → ModuleCat.{max wI w} R}

/-- Concrete coordinates of restriction are obtained by reindexing the point fibers. -/
theorem sectionCoordinates_restrict {X Y : C} (f : Y ⟶ X)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X))
    (i : I) (y : (points i).fiber.obj Y) :
    sectionCoordinates points M Y
        ((productSheaf points (ModuleCat R) M).obj.map f.op s) i y =
      sectionCoordinates points M X s i ((points i).fiber.map f y) := by
  have h := ConcreteCategory.congr_hom (sectionCoordinate_restrict points M f i y) s
  change sectionCoordinate points M Y i y
      ((productSheaf points (ModuleCat R) M).obj.map f.op s) =
    sectionCoordinate points M X i ((points i).fiber.map f y) s at h
  simpa only [sectionCoordinates_apply] using h

/-- A map of coefficient sets acts pointwise on all actual product sections. -/
def sectionSetMap (a : ∀ i, M i → N i) (X : C)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X)) :
    (productSheaf points (ModuleCat R) N).obj.obj (op X) :=
  (sectionCoordinates points N X).symm
    (fun i x => a i (sectionCoordinates points M X s i x))

@[simp]
theorem sectionCoordinates_sectionSetMap (a : ∀ i, M i → N i) (X : C)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X))
    (i : I) (x : (points i).fiber.obj X) :
    sectionCoordinates points N X (sectionSetMap points a X s) i x =
      a i (sectionCoordinates points M X s i x) := by
  simp only [sectionSetMap, LinearEquiv.apply_symm_apply]

/-- Arbitrary coefficient set maps are natural on the underlying set presheaves. -/
def setMap (a : ∀ i, M i → N i) :
    (productSheaf points (ModuleCat R) M).obj ⋙ forget (ModuleCat R) ⟶
      (productSheaf points (ModuleCat R) N).obj ⋙ forget (ModuleCat R) where
  app U := ↾(sectionSetMap points a U.unop)
  naturality {U V} f := by
    ext s
    apply (sectionCoordinates points N V.unop).injective
    funext i x
    change sectionCoordinates points N V.unop
        (sectionSetMap points a V.unop
          ((productSheaf points (ModuleCat R) M).obj.map f.unop.op s)) i x =
      sectionCoordinates points N V.unop
        ((productSheaf points (ModuleCat R) N).obj.map f.unop.op
          (sectionSetMap points a U.unop s)) i x
    rw [sectionCoordinates_sectionSetMap]
    rw [sectionCoordinates_restrict, sectionCoordinates_restrict,
      sectionCoordinates_sectionSetMap]

@[simp]
theorem setMap_app_zero (a : ∀ i, M i → N i) (ha : ∀ i, a i 0 = 0) (U : Cᵒᵖ) :
    (setMap points a).app U 0 = 0 := by
  apply (sectionCoordinates points N U.unop).injective
  funext i x
  change sectionCoordinates points N U.unop (sectionSetMap points a U.unop 0) i x = _
  simp only [sectionCoordinates_sectionSetMap, map_zero, Pi.zero_apply, ha]

/-- A coefficientwise right inverse gives a natural set section of the product map. -/
theorem productFunctor_map_setMap (f : M ⟶ N) (a : ∀ i, N i → M i)
    (hfa : ∀ i s, f i (a i s) = s) (U : Cᵒᵖ)
    (s : (productSheaf points (ModuleCat R) N).obj.obj U) :
    ((productFunctor points (ModuleCat R)).map f).hom.app U
        ((setMap points a).app U s) = s := by
  apply (sectionCoordinates points N U.unop).injective
  funext i x
  rw [sectionCoordinates_apply]
  have h := ConcreteCategory.congr_hom (sectionCoordinate_map points M f U.unop i x)
    ((setMap points a).app U s)
  change sectionCoordinate points N U.unop i x
      (((productFunctor points (ModuleCat R)).map f).hom.app U
        ((setMap points a).app U s)) =
    f i (sectionCoordinate points M U.unop i x ((setMap points a).app U s)) at h
  rw [h, ← sectionCoordinates_apply]
  change f i (sectionCoordinates points M U.unop
    (sectionSetMap points a U.unop s) i x) = _
  rw [sectionCoordinates_sectionSetMap, hfa, sectionCoordinates_apply]

/-- A surjective module map admits a section of underlying sets taking zero to zero. -/
def zeroPreservingSection {S : Type wR} [CommRing S] {A B : ModuleCat.{wM} S} (f : A ⟶ B)
    (hf : Function.Surjective f) (s : B) : A := by
  classical
  exact if hs : s = 0 then 0 else (hf s).choose

@[simp]
theorem zeroPreservingSection_zero {S : Type wR} [CommRing S] {A B : ModuleCat.{wM} S} (f : A ⟶ B)
    (hf : Function.Surjective f) : zeroPreservingSection f hf 0 = 0 := by
  simp [zeroPreservingSection]

@[simp]
theorem map_zeroPreservingSection {S : Type wR} [CommRing S] {A B : ModuleCat.{wM} S} (f : A ⟶ B)
    (hf : Function.Surjective f) (s : B) : f (zeroPreservingSection f hf s) = s := by
  classical
  dsimp only [zeroPreservingSection]
  split_ifs with hs
  · exact (map_zero f.hom).trans hs.symm
  · exact (hf s).choose_spec

/-- Coefficientwise surjections of point products have natural zero-preserving set
sections, without any topological assumptions on the point index. -/
def setSection (f : M ⟶ N) (hf : ∀ i, Function.Surjective (f i)) :
    (productSheaf points (ModuleCat R) N).obj ⋙ forget (ModuleCat R) ⟶
      (productSheaf points (ModuleCat R) M).obj ⋙ forget (ModuleCat R) :=
  setMap points (fun i => zeroPreservingSection (f i) (hf i))

@[simp]
theorem setSection_app_zero (f : M ⟶ N) (hf : ∀ i, Function.Surjective (f i))
    (U : Cᵒᵖ) : (setSection points f hf).app U 0 = 0 :=
  setMap_app_zero points _ (fun i => zeroPreservingSection_zero (f i) (hf i)) U

@[simp]
theorem productFunctor_map_setSection (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) (U : Cᵒᵖ)
    (s : (productSheaf points (ModuleCat R) N).obj.obj U) :
    ((productFunctor points (ModuleCat R)).map f).hom.app U
        ((setSection points f hf).app U s) = s :=
  productFunctor_map_setMap points f _ (fun i s => map_zeroPreservingSection (f i) (hf i) s)
    U s

/-- Compact sections of point products lift along coefficientwise surjections on
any topological point family. -/
theorem compactSections_map_surjective_of_coefficients
    [LocallySmall.{max wI w} C] [TopologicalSpace I]
    (f : M ⟶ N) (hf : ∀ i, Function.Surjective (f i)) (X : C) :
    Function.Surjective
      ((PointSupport.sheafCompactSections J points R X).map
        ((productFunctor points (ModuleCat R)).map f)) :=
  PointSupport.sheafCompactSections_map_surjective_of_setSection points
    ((productFunctor points (ModuleCat R)).map f) (setSection points f hf)
    (setSection_app_zero points f hf) (productFunctor_map_setSection points f hf) X

end Langlands.Sheaf.PointProduct
