import Langlands.Sheaf.Equivariant.TwistedInductionSmoothCoordinates

/-! # Underlying section maps through induction and local discreteness -/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite
open LocalActionSystem

universe v u uG w

section Smooth

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]
variable {R : Type w} [CommRing R]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)
variable [L.HasAdmissibleRefinements J]
variable {F F' F'' : Tᵒᵖ ⥤ ModuleCat.{w} R}

/-- A natural map of underlying sets restricts to the existing locally discrete parts. -/
def smoothUnderlyingMap
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R)) :
    smoothPresheaf L J F ⋙ forget (ModuleCat R) ⟶
      smoothPresheaf L J F' ⋙ forget (ModuleCat R) where
  app U := TypeCat.ofHom fun s => ⟨η.app U s.val,
    J.superset_covering (L.discreteSieve_le_map η s.val) s.property⟩
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact η.naturality_apply f s.val

@[simp]
theorem smoothUnderlyingMap_val
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (U : Tᵒᵖ) (s : (smoothPresheaf L J F).obj U) :
    ((smoothUnderlyingMap L J η).app U s).val = η.app U s.val := rfl

@[simp]
theorem smoothUnderlyingMap_id : smoothUnderlyingMap L J (𝟙 (F ⋙ forget (ModuleCat R))) =
    𝟙 (smoothPresheaf L J F ⋙ forget (ModuleCat R)) := by
  ext U s
  rfl

@[simp]
theorem smoothUnderlyingMap_comp
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (θ : F' ⋙ forget (ModuleCat R) ⟶ F'' ⋙ forget (ModuleCat R)) :
    smoothUnderlyingMap L J (η ≫ θ) =
      smoothUnderlyingMap L J η ≫ smoothUnderlyingMap L J θ := by
  ext U s
  rfl

/-- A natural set section remains a section on locally discrete parts. -/
theorem smoothUnderlyingMap_rightInverse
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (σ : F' ⋙ forget (ModuleCat R) ⟶ F ⋙ forget (ModuleCat R))
    (h : σ ≫ η = 𝟙 _) :
    smoothUnderlyingMap L J σ ≫ smoothUnderlyingMap L J η = 𝟙 _ := by
  rw [← smoothUnderlyingMap_comp, h, smoothUnderlyingMap_id]

/-- Zero preservation is retained on the locally discrete subpresheaf. -/
theorem smoothUnderlyingMap_zero
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (hη : ∀ U, η.app U 0 = 0) (U : Tᵒᵖ) :
    (smoothUnderlyingMap L J η).app U 0 = 0 := by
  apply Subtype.ext
  exact hη U

/-- The construction agrees with the existing linear map on locally discrete parts. -/
@[simp]
theorem smoothUnderlyingMap_whiskerRight (φ : F ⟶ F') :
    smoothUnderlyingMap L J (Functor.whiskerRight φ (forget (ModuleCat R))) =
      Functor.whiskerRight (smoothPresheafMap L J φ) (forget (ModuleCat R)) := by
  ext U s
  rfl

end Smooth

namespace TwistedOver.InductionCoordinates

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)
variable {R : Type w} [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]
variable {F F' F'' : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R}

/-- Apply an arbitrary underlying natural section map separately in every induction coordinate. -/
def underlyingMapApp
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (U : TwistedOver P ρ) (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    ((ι P ρ).op.ran.obj F').obj (op U) :=
  (moduleCoordinates ρ F' U).symm fun g =>
    η.app (op ((translate P ρ g).obj U.obj)) (moduleCoordinates ρ F U s g)

@[simp]
theorem underlyingMapApp_coordinates
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (U : TwistedOver P ρ) (s : ((ι P ρ).op.ran.obj F).obj (op U)) (g : G) :
    moduleCoordinates ρ F' U (underlyingMapApp ρ η U s) g =
      η.app (op ((translate P ρ g).obj U.obj)) (moduleCoordinates ρ F U s g) := by
  exact congrFun ((moduleCoordinates ρ F' U).apply_symm_apply _) g

/-- The coordinatewise set map is natural for the actual right Kan maps. -/
def inductionUnderlyingMap
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R)) :
    (ι P ρ).op.ran.obj F ⋙ forget (ModuleCat R) ⟶
      (ι P ρ).op.ran.obj F' ⋙ forget (ModuleCat R) where
  app U := TypeCat.ofHom (underlyingMapApp ρ η U.unop)
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply (moduleCoordinates ρ F' V.unop).injective
    funext g
    change moduleCoordinates ρ F' V.unop
        (underlyingMapApp ρ η V.unop (((ι P ρ).op.ran.obj F).map f s)) g =
      moduleCoordinates ρ F' V.unop
        (((ι P ρ).op.ran.obj F').map f (underlyingMapApp ρ η U.unop s)) g
    have hF := congrFun (moduleCoordinates_map ρ F f.unop s) g
    have hF' := congrFun (moduleCoordinates_map ρ F' f.unop
      (underlyingMapApp ρ η U.unop s)) g
    change moduleCoordinates ρ F V.unop (((ι P ρ).op.ran.obj F).map f s) g =
      F.map (transport ρ f.unop g).op
        (moduleCoordinates ρ F U.unop s (g * (Hom.twist f.unop)⁻¹)) at hF
    change moduleCoordinates ρ F' V.unop
        (((ι P ρ).op.ran.obj F').map f (underlyingMapApp ρ η U.unop s)) g =
      F'.map (transport ρ f.unop g).op
        (moduleCoordinates ρ F' U.unop (underlyingMapApp ρ η U.unop s)
          (g * (Hom.twist f.unop)⁻¹)) at hF'
    rw [underlyingMapApp_coordinates, hF, hF', underlyingMapApp_coordinates]
    exact η.naturality_apply (transport ρ f.unop g).op _

@[simp]
theorem inductionUnderlyingMap_id :
    inductionUnderlyingMap ρ (𝟙 (F ⋙ forget (ModuleCat R))) =
      𝟙 ((ι P ρ).op.ran.obj F ⋙ forget (ModuleCat R)) := by
  ext U s
  apply (moduleCoordinates ρ F U.unop).injective
  funext g
  exact underlyingMapApp_coordinates ρ (𝟙 _) U.unop s g

@[simp]
theorem inductionUnderlyingMap_comp
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (θ : F' ⋙ forget (ModuleCat R) ⟶ F'' ⋙ forget (ModuleCat R)) :
    inductionUnderlyingMap ρ (η ≫ θ) =
      inductionUnderlyingMap ρ η ≫ inductionUnderlyingMap ρ θ := by
  ext U s
  apply (moduleCoordinates ρ F'' U.unop).injective
  funext g
  change moduleCoordinates ρ F'' U.unop (underlyingMapApp ρ (η ≫ θ) U.unop s) g =
    moduleCoordinates ρ F'' U.unop
      (underlyingMapApp ρ θ U.unop (underlyingMapApp ρ η U.unop s)) g
  rw [underlyingMapApp_coordinates, underlyingMapApp_coordinates, underlyingMapApp_coordinates]
  rfl

/-- A zero-preserving underlying section map remains zero-preserving after induction. -/
theorem inductionUnderlyingMap_zero
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (hη : ∀ U, η.app U 0 = 0) (U : (TwistedOver P ρ)ᵒᵖ) :
    (inductionUnderlyingMap ρ η).app U 0 = 0 := by
  apply (moduleCoordinates ρ F' U.unop).injective
  funext g
  simp only [inductionUnderlyingMap, TypeCat.ofHom_apply, underlyingMapApp_coordinates, map_zero,
    Pi.zero_apply]
  exact hη _

/-- Coordinate projections commute with the actual right Kan map of a linear transformation. -/
@[reassoc]
theorem ranMap_projection (φ : F ⟶ F') (U : TwistedOver P ρ) (g : G) :
    ((ι P ρ).op.ran.map φ).app (op U) ≫ projection ρ F' U g =
      projection ρ F U g ≫ φ.app (op ((translate P ρ g).obj U.obj)) := by
  dsimp only [projection, objects]
  rw [← Category.assoc, ← NatTrans.naturality, Category.assoc]
  have h := NatTrans.congr_app ((ι P ρ).op.ranCounit.naturality φ)
    (op ((translate P ρ g).obj U.obj))
  change ((ι P ρ).op.ran.map φ).app (op ((ι P ρ).obj ((translate P ρ g).obj U.obj))) ≫
      ((ι P ρ).op.ranCounit.app F').app (op ((translate P ρ g).obj U.obj)) =
    ((ι P ρ).op.ranCounit.app F).app (op ((translate P ρ g).obj U.obj)) ≫
      φ.app (op ((translate P ρ g).obj U.obj)) at h
  rw [h, Category.assoc]

/-- Underlying natural-map induction agrees with the actual linear right Kan map. -/
@[simp]
theorem inductionUnderlyingMap_whiskerRight (φ : F ⟶ F') :
    inductionUnderlyingMap ρ (Functor.whiskerRight φ (forget (ModuleCat R))) =
      Functor.whiskerRight ((ι P ρ).op.ran.map φ) (forget (ModuleCat R)) := by
  ext U s
  apply (moduleCoordinates ρ F' U.unop).injective
  funext g
  change moduleCoordinates ρ F' U.unop
      (underlyingMapApp ρ (Functor.whiskerRight φ (forget (ModuleCat R))) U.unop s) g =
    projection ρ F' U.unop g (((ι P ρ).op.ran.map φ).app U s)
  rw [underlyingMapApp_coordinates]
  exact (congrArg (fun k => k.hom s) (ranMap_projection ρ φ U.unop g)).symm

/-- A natural set section remains a section after the actual right Kan induction. -/
theorem inductionUnderlyingMap_rightInverse
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (σ : F' ⋙ forget (ModuleCat R) ⟶ F ⋙ forget (ModuleCat R))
    (h : σ ≫ η = 𝟙 _) :
    inductionUnderlyingMap ρ σ ≫ inductionUnderlyingMap ρ η = 𝟙 _ := by
  rw [← inductionUnderlyingMap_comp, h, inductionUnderlyingMap_id]

section SmoothInduction

variable [TopologicalSpace G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable (J : GrothendieckTopology (TwistedOver P ρ)) [L.HasAdmissibleRefinements J]

/-- Transport underlying natural section maps through induction and the actual smooth part. -/
def smoothInductionUnderlyingMap
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R)) :
    smoothPresheaf L J ((ι P ρ).op.ran.obj F) ⋙ forget (ModuleCat R) ⟶
      smoothPresheaf L J ((ι P ρ).op.ran.obj F') ⋙ forget (ModuleCat R) :=
  smoothUnderlyingMap L J (inductionUnderlyingMap ρ η)

@[simp]
theorem smoothInductionUnderlyingMap_id :
    smoothInductionUnderlyingMap ρ L J (𝟙 (F ⋙ forget (ModuleCat R))) = 𝟙 _ := by
  simp only [smoothInductionUnderlyingMap, inductionUnderlyingMap_id, smoothUnderlyingMap_id]

@[simp]
theorem smoothInductionUnderlyingMap_comp
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (θ : F' ⋙ forget (ModuleCat R) ⟶ F'' ⋙ forget (ModuleCat R)) :
    smoothInductionUnderlyingMap ρ L J (η ≫ θ) =
      smoothInductionUnderlyingMap ρ L J η ≫ smoothInductionUnderlyingMap ρ L J θ := by
  simp only [smoothInductionUnderlyingMap, inductionUnderlyingMap_comp, smoothUnderlyingMap_comp]

/-- A zero-preserving set map stays zero-preserving through induction and local discreteness. -/
theorem smoothInductionUnderlyingMap_zero
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (hη : ∀ U, η.app U 0 = 0) (U : (TwistedOver P ρ)ᵒᵖ) :
    (smoothInductionUnderlyingMap ρ L J η).app U 0 = 0 :=
  smoothUnderlyingMap_zero L J _ (inductionUnderlyingMap_zero ρ η hη) U

/-- The transported map is the underlying map of the actual linear smooth-induction map. -/
@[simp]
theorem smoothInductionUnderlyingMap_whiskerRight (φ : F ⟶ F') :
    smoothInductionUnderlyingMap ρ L J (Functor.whiskerRight φ (forget (ModuleCat R))) =
      Functor.whiskerRight (smoothPresheafMap L J ((ι P ρ).op.ran.map φ))
        (forget (ModuleCat R)) := by
  simp only [smoothInductionUnderlyingMap, inductionUnderlyingMap_whiskerRight,
    smoothUnderlyingMap_whiskerRight]

/-- A natural set section remains a section after induction and the actual smooth part. -/
theorem smoothInductionUnderlyingMap_rightInverse
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    (σ : F' ⋙ forget (ModuleCat R) ⟶ F ⋙ forget (ModuleCat R))
    (h : σ ≫ η = 𝟙 _) :
    smoothInductionUnderlyingMap ρ L J σ ≫ smoothInductionUnderlyingMap ρ L J η = 𝟙 _ := by
  rw [← smoothInductionUnderlyingMap_comp, h, smoothInductionUnderlyingMap_id]

section Sheaf

variable (J₀ : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J₀]
variable [L.HasAdmissibleRefinements (twistedTopology ρ J₀)]
variable {A B : Sheaf J₀ (ModuleCat.{w} R)}

/-- Specialization to the underlying presheaves of the actual induced sheaf coreflector. -/
def smoothSheafInductionUnderlyingMap
    (η : A.obj ⋙ forget (ModuleCat R) ⟶ B.obj ⋙ forget (ModuleCat R)) :
    (((smoothCoreflector L (twistedTopology ρ J₀)).obj
      ((induction ρ J₀ (ModuleCat.{w} R)).obj A)).obj.obj) ⋙ forget (ModuleCat R) ⟶
    (((smoothCoreflector L (twistedTopology ρ J₀)).obj
      ((induction ρ J₀ (ModuleCat.{w} R)).obj B)).obj.obj) ⋙ forget (ModuleCat R) :=
  smoothInductionUnderlyingMap ρ L (twistedTopology ρ J₀) η

/-- The sheaf specialization agrees with the existing induced smooth linear sheaf map. -/
@[simp]
theorem smoothSheafInductionUnderlyingMap_whiskerRight (φ : A ⟶ B) :
    smoothSheafInductionUnderlyingMap ρ L J₀
        (Functor.whiskerRight φ.hom (forget (ModuleCat R))) =
      Functor.whiskerRight
        ((((induction ρ J₀ (ModuleCat.{w} R)) ⋙
          smoothCoreflector L (twistedTopology ρ J₀)).map φ).hom.hom)
        (forget (ModuleCat R)) :=
  smoothInductionUnderlyingMap_whiskerRight ρ L (twistedTopology ρ J₀) φ.hom

end Sheaf

end SmoothInduction

end TwistedOver.InductionCoordinates

end Langlands.Sheaf.Equivariant
