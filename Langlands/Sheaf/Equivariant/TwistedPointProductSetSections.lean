import Langlands.Sheaf.Equivariant.TwistedInductionUnderlyingMaps
import Langlands.Sheaf.PointProductSetSections

/-! # Set sections and compact lifting for locally discrete induced point products -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite
open LocalActionSystem

universe v u uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasAdmissibleRefinements (twistedTopology ρ J)]
variable {I : Type w} (points : I → J.Point.{w})
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- Apply the actual point product, twisted induction, and locally discrete coreflector. -/
def smoothPointProductFunctor :
    (I → ModuleCat.{w} R) ⥤ L.SmoothSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  PointProduct.productFunctor points (ModuleCat R) ⋙ induction ρ J (ModuleCat R) ⋙
    smoothCoreflector L (twistedTopology ρ J)

/-- Forget the equivariance of the actual locally discrete induced point product. -/
def restrictedSmoothPointProductFunctor : (I → ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  smoothPointProductFunctor ρ J L points R ⋙
    L.smoothSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙ restriction ρ J (ModuleCat R)

variable {R} {M N : I → ModuleCat.{w} R}

/-- A coefficientwise surjection has a natural zero-preserving set section after
actual induction, the locally discrete coreflector, and restriction. -/
def restrictedSmoothPointProductSetSection (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) :
    ((restrictedSmoothPointProductFunctor ρ J L points R).obj N).obj ⋙ forget (ModuleCat R) ⟶
      ((restrictedSmoothPointProductFunctor ρ J L points R).obj M).obj ⋙ forget (ModuleCat R) :=
  Functor.whiskerLeft (ι P ρ).op
    (InductionCoordinates.smoothSheafInductionUnderlyingMap ρ L J
      (PointProduct.setSection points f hf))

@[simp]
theorem restrictedSmoothPointProductSetSection_zero (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) (U : (P.Over ⊤ X)ᵒᵖ) :
    (restrictedSmoothPointProductSetSection ρ J L points f hf).app U 0 = 0 :=
  InductionCoordinates.smoothInductionUnderlyingMap_zero ρ L (twistedTopology ρ J)
    (PointProduct.setSection points f hf) (PointProduct.setSection_app_zero points f hf) _

/-- The constructed natural map is a section of the actual linear composite map. -/
theorem restrictedSmoothPointProduct_map_setSection (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) (U : (P.Over ⊤ X)ᵒᵖ)
    (s : ((restrictedSmoothPointProductFunctor ρ J L points R).obj N).obj.obj U) :
    (((restrictedSmoothPointProductFunctor ρ J L points R).map f).hom.app U)
      ((restrictedSmoothPointProductSetSection ρ J L points f hf).app U s) = s := by
  let φ : PointProduct.productSheaf points (ModuleCat R) M ⟶
      PointProduct.productSheaf points (ModuleCat R) N :=
    (PointProduct.productFunctor points (ModuleCat R)).map f
  let η := Functor.whiskerRight φ.hom (forget (ModuleCat R))
  have hp : PointProduct.setSection points f hf ≫ η = 𝟙 _ := by
    ext V t
    exact PointProduct.productFunctor_map_setSection points f hf V t
  have hs := InductionCoordinates.smoothInductionUnderlyingMap_rightInverse
    ρ L (twistedTopology ρ J) η (PointProduct.setSection points f hf) hp
  change InductionCoordinates.smoothSheafInductionUnderlyingMap ρ L J
      (PointProduct.setSection points f hf) ≫
    InductionCoordinates.smoothSheafInductionUnderlyingMap ρ L J η = 𝟙 _ at hs
  have he := InductionCoordinates.smoothSheafInductionUnderlyingMap_whiskerRight ρ L J φ
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app hs ((ι P ρ).op.obj U)) s
  have hc := ConcreteCategory.congr_hom
    (NatTrans.congr_app he ((ι P ρ).op.obj U))
    ((restrictedSmoothPointProductSetSection ρ J L points f hf).app U s)
  exact hc.symm.trans hv

/-- Every ordinary section lifts along a coefficientwise surjection. -/
theorem restrictedSmoothPointProduct_map_app_surjective (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) (U : (P.Over ⊤ X)ᵒᵖ) :
    Function.Surjective
      (((restrictedSmoothPointProductFunctor ρ J L points R).map f).hom.app U) :=
  fun s => ⟨(restrictedSmoothPointProductSetSection ρ J L points f hf).app U s,
    restrictedSmoothPointProduct_map_setSection ρ J L points f hf U s⟩

variable {I' : Type*} (supportPoints : I' → J.Point.{w}) [TopologicalSpace I']

/-- Compactly supported sections lift for any topological support-point family;
no compatibility between that family and the product's point index is needed. -/
theorem restrictedSmoothPointProduct_compactSections_map_surjective
    [LocallySmall.{w} (P.Over ⊤ X)] (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) (U : P.Over ⊤ X) :
    Function.Surjective
      ((PointSupport.sheafCompactSections J supportPoints R U).map
        ((restrictedSmoothPointProductFunctor ρ J L points R).map f)) :=
  PointSupport.sheafCompactSections_map_surjective_of_setSection supportPoints
    ((restrictedSmoothPointProductFunctor ρ J L points R).map f)
    (restrictedSmoothPointProductSetSection ρ J L points f hf)
    (restrictedSmoothPointProductSetSection_zero ρ J L points f hf)
    (restrictedSmoothPointProduct_map_setSection ρ J L points f hf) U

end Langlands.Sheaf.Equivariant.TwistedOver
