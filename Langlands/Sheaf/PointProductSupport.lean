import Langlands.Sheaf.PointProduct
import Langlands.Sheaf.PointSupport

/-! # Coefficients and germ supports of actual point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace Langlands.Sheaf.PointProduct

open CategoryTheory CategoryTheory.Limits Opposite

universe wI w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → J.Point.{max wI w})
variable {R : Type (max wI w)} [CommRing R]
local instance : HasProducts.{wI} (ModuleCat.{max wI w} R) := by
  let := hasLimitsOfSizeShrink.{wI, wI} (ModuleCat.{max wI w} R)
  infer_instance

variable (M : I → ModuleCat.{max wI w} R)

/-- Evaluation at a point and an element of its fiber over a site object. -/
def sectionCoordinate (X : C) (i : I) (x : (points i).fiber.obj X) :
    (productSheaf points (ModuleCat R) M).obj.obj (op X) ⟶ M i :=
  (projection points (ModuleCat R) M i).hom.app (op X) ≫ Pi.π _ x

@[reassoc (attr := simp)]
theorem sectionsIso_hom_π (X : C) (i : I) :
    (sectionsIso points (ModuleCat R) M X).hom ≫ Pi.π _ i =
      (projection points (ModuleCat R) M i).hom.app (op X) := by
  exact piComparison_comp_π
    (sheafToPresheaf J (ModuleCat R) ⋙ (evaluation Cᵒᵖ (ModuleCat R)).obj (op X))
    (fun i => (points i).skyscraperSheaf (M i)) i

/-- Actual module sections are arbitrary coefficient families on the point fibers. -/
def sectionCoordinatesIso (X : C) :
    (productSheaf points (ModuleCat R) M).obj.obj (op X) ≅
      ModuleCat.of R (∀ i, (points i).fiber.obj X → M i) :=
  sectionsIso points (ModuleCat R) M X ≪≫
    Pi.mapIso (fun i => ModuleCat.piIsoPi (fun (_ : (points i).fiber.obj X) => M i)) ≪≫
      ModuleCat.piIsoPi _

/-- The concrete linear equivalence underlying the section formula. -/
def sectionCoordinates (X : C) :
    (productSheaf points (ModuleCat R) M).obj.obj (op X) ≃ₗ[R]
      (∀ i, (points i).fiber.obj X → M i) :=
  (sectionCoordinatesIso points M X).toLinearEquiv

@[simp]
theorem sectionCoordinates_apply (X : C)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X))
    (i : I) (x : (points i).fiber.obj X) :
    sectionCoordinates points M X s i x = sectionCoordinate points M X i x s := by
  have h :
      (sectionCoordinatesIso points M X).hom ≫
          ModuleCat.ofHom (LinearMap.proj i) ≫ ModuleCat.ofHom (LinearMap.proj x) =
        sectionCoordinate points M X i x := by
    simp only [sectionCoordinatesIso, Iso.trans_hom, Category.assoc,
      reassoc_of% ModuleCat.piIsoPi_hom_ker_subtype, ModuleCat.piIsoPi_hom_ker_subtype,
      Pi.mapIso_hom_π_assoc, sectionCoordinate]
    exact congrArg (fun f => f ≫ Pi.π _ x)
      (sectionsIso_hom_π points M X i)
  exact ConcreteCategory.congr_hom h s

@[simp]
theorem sectionCoordinate_sectionCoordinates_symm (X : C)
    (s : ∀ i, (points i).fiber.obj X → M i) (i : I) (x : (points i).fiber.obj X) :
    sectionCoordinate points M X i x ((sectionCoordinates points M X).symm s) = s i x := by
  rw [← sectionCoordinates_apply, LinearEquiv.apply_symm_apply]

@[reassoc (attr := simp)]
theorem sectionCoordinate_restrict {X Y : C} (f : Y ⟶ X)
    (i : I) (y : (points i).fiber.obj Y) :
    (productSheaf points (ModuleCat R) M).obj.map f.op ≫
        sectionCoordinate points M Y i y =
      sectionCoordinate points M X i ((points i).fiber.map f y) := by
  unfold sectionCoordinate
  rw [← Category.assoc, (projection points (ModuleCat R) M i).hom.naturality f.op,
    Category.assoc]
  dsimp
  simp

@[reassoc (attr := simp)]
theorem sectionCoordinate_map {N : I → ModuleCat.{max wI w} R} (f : M ⟶ N)
    (X : C) (i : I) (x : (points i).fiber.obj X) :
    ((productFunctor points (ModuleCat R)).map f).hom.app (op X) ≫
        sectionCoordinate points N X i x =
      sectionCoordinate points M X i x ≫ f i := by
  unfold sectionCoordinate
  rw [← Category.assoc]
  change (((productFunctor points (ModuleCat R)).map f ≫
      projection points (ModuleCat R) N i).hom.app (op X)) ≫ Pi.π _ x = _
  rw [productFunctor_map_projection]
  dsimp
  simp

/-- The diagonal adjunction map from the fiber of the product to its coefficient. -/
def coefficientRetraction (i : I) :
    (points i).presheafFiber.obj (productSheaf points (ModuleCat R) M).obj ⟶ M i :=
  (points i).skyscraperPresheafHomEquiv.symm
    (projection points (ModuleCat R) M i).hom

@[reassoc (attr := simp)]
theorem germ_coefficientRetraction (X : C) (i : I) (x : (points i).fiber.obj X) :
    (points i).toPresheafFiber X x (productSheaf points (ModuleCat R) M).obj ≫
        coefficientRetraction points M i =
      sectionCoordinate points M X i x := by
  exact (points i).toPresheafFiber_skyscraperPresheafHomEquiv_symm _ X x

/-- A nonzero coordinate forces a nonzero germ at the same point. -/
theorem mem_support_of_sectionCoordinate_ne_zero {X : C}
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X))
    (i : I) (x : (points i).fiber.obj X)
    (hs : sectionCoordinate points M X i x s ≠ 0) :
    i ∈ PointSupport.support points (productSheaf points (ModuleCat R) M).obj s := by
  refine ⟨x, fun hz => hs ?_⟩
  have h := ConcreteCategory.congr_hom (germ_coefficientRetraction points M X i x) s
  change coefficientRetraction points M i
      ((points i).toPresheafFiber X x (productSheaf points (ModuleCat R) M).obj s) =
    sectionCoordinate points M X i x s at h
  rw [hz, map_zero] at h
  exact h.symm

/-- Site neighborhoods of a point outside `K` can avoid all indices in `K`. -/
def SeparatesComplement (X : C) (K : Set I) : Prop :=
  ∀ (i : I) (x : (points i).fiber.obj X), i ∉ K →
    ∃ (Y : C) (f : Y ⟶ X) (y : (points i).fiber.obj Y),
      (points i).fiber.map f y = x ∧
        ∀ j : I, Nonempty ((points j).fiber.obj Y) → j ∉ K

/-- Vanishing of the coefficients outside a set bounds the actual germ support,
provided site neighborhoods separate its complement. -/
theorem support_subset_of_sectionCoordinates_zero {X : C} {K : Set I}
    (hK : SeparatesComplement points X K)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X))
    (hs : ∀ i, i ∉ K → ∀ x : (points i).fiber.obj X,
      sectionCoordinate points M X i x s = 0) :
    PointSupport.support points (productSheaf points (ModuleCat R) M).obj s ⊆ K := by
  intro i hi
  by_contra hiK
  obtain ⟨x, hx⟩ := hi
  obtain ⟨Y, f, y, hy, hY⟩ := hK i x hiK
  have hz : (productSheaf points (ModuleCat R) M).obj.map f.op s = 0 := by
    apply (sectionCoordinates points M Y).injective
    funext j z
    simp only [sectionCoordinates_apply, map_zero]
    have h := ConcreteCategory.congr_hom (sectionCoordinate_restrict points M f j z) s
    exact h.trans (hs j (hY j ⟨z⟩) _)
  apply hx
  rw [← hy, ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hz, map_zero]

variable [LocallySmall.{max wI w} C]

/-- At a terminal object, concrete global sections are arbitrary coefficients. -/
def globalCoordinates (X : C) (hX : IsTerminal X) :
    (productSheaf points (ModuleCat R) M).obj.obj (op X) ≃ₗ[R] (∀ i, M i) :=
  (sectionCoordinates points M X).trans (LinearEquiv.piCongrRight fun i =>
    letI := (points i).uniqueFiberObj X hX
    LinearEquiv.funUnique _ R (M i))

theorem globalCoordinates_apply (X : C) (hX : IsTerminal X)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X))
    (i : I) (x : (points i).fiber.obj X) :
    globalCoordinates points M X hX s i = sectionCoordinate points M X i x s := by
  let := (points i).uniqueFiberObj X hX
  change sectionCoordinates points M X s i default = _
  rw [sectionCoordinates_apply, Subsingleton.elim (default : (points i).fiber.obj X) x]

@[simp]
theorem sectionCoordinate_globalCoordinates_symm (X : C) (hX : IsTerminal X)
    (s : ∀ i, M i) (i : I) (x : (points i).fiber.obj X) :
    sectionCoordinate points M X i x ((globalCoordinates points M X hX).symm s) = s i := by
  rw [← globalCoordinates_apply points M X hX, LinearEquiv.apply_symm_apply]

/-- The nonzero coefficient set is contained in actual germ support. -/
theorem coefficientSupport_subset_support (X : C) (hX : IsTerminal X)
    (s : (productSheaf points (ModuleCat R) M).obj.obj (op X)) :
    {i | globalCoordinates points M X hX s i ≠ 0} ⊆
      PointSupport.support points (productSheaf points (ModuleCat R) M).obj s := by
  intro i hi
  let x := ((points i).uniqueFiberObj X hX).default
  apply mem_support_of_sectionCoordinate_ne_zero points M s i x
  rwa [← globalCoordinates_apply points M X hX]

/-- A coefficientwise surjection lifts a section without enlarging any support
bound whose complement is separated by site neighborhoods. -/
theorem exists_lift_with_support {N : I → ModuleCat.{max wI w} R} (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f i)) (X : C) (hX : IsTerminal X)
    {K : Set I} (hK : SeparatesComplement points X K)
    (s : (productSheaf points (ModuleCat R) N).obj.obj (op X))
    (hs : PointSupport.support points (productSheaf points (ModuleCat R) N).obj s ⊆ K) :
    ∃ t : (productSheaf points (ModuleCat R) M).obj.obj (op X),
      ((productFunctor points (ModuleCat R)).map f).hom.app (op X) t = s ∧
        PointSupport.support points (productSheaf points (ModuleCat R) M).obj t ⊆ K := by
  classical
  let a := globalCoordinates points N X hX s
  let b : ∀ i, M i := fun i => if ha : a i = 0 then 0 else (hf i (a i)).choose
  have hb (i : I) : f i (b i) = a i := by
    dsimp [b]
    split_ifs with ha
    · simpa only [map_zero] using ha.symm
    · exact (hf i (a i)).choose_spec
  let t := (globalCoordinates points M X hX).symm b
  refine ⟨t, ?_, ?_⟩
  · apply (sectionCoordinates points N X).injective
    funext i x
    simp only [sectionCoordinates_apply]
    have h := ConcreteCategory.congr_hom (sectionCoordinate_map points M f X i x) t
    change sectionCoordinate points N X i x
        (((productFunctor points (ModuleCat R)).map f).hom.app (op X) t) =
      f i (sectionCoordinate points M X i x t) at h
    rw [h]
    dsimp only [t]
    rw [sectionCoordinate_globalCoordinates_symm, hb]
    exact globalCoordinates_apply points N X hX s i x
  · apply support_subset_of_sectionCoordinates_zero points M hK
    intro i hi x
    dsimp only [t]
    rw [sectionCoordinate_globalCoordinates_symm]
    have ha : a i = 0 := by
      by_contra hn
      exact hi (hs (coefficientSupport_subset_support points N X hX s hn))
    simp only [b, dite_eq_left ha]

variable [TopologicalSpace I]

/-- Every compact coefficient bound has a compact enlargement whose complement
is separated by site neighborhoods. -/
def HasCompactSeparatingBounds (X : C) : Prop :=
  ∀ (K : Set I), IsCompact K →
    ∃ K' : Set I, IsCompact K' ∧ K ⊆ K' ∧ SeparatesComplement points X K'

/-- Compact sections of point products lift along coefficientwise surjections
when compact coefficient bounds admit separating compact enlargements. -/
theorem compactSections_map_surjective
    (X : C) (hX : IsTerminal X) (hbound : HasCompactSeparatingBounds points X)
    {N : I → ModuleCat.{max wI w} R} (f : M ⟶ N) (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective
      ((PointSupport.sheafCompactSections J points R X).map
        ((productFunctor points (ModuleCat R)).map f)) := by
  intro s
  obtain ⟨K, hK, hsK⟩ := s.property
  obtain ⟨K', hK', hKK', hsep⟩ := hbound K hK
  obtain ⟨t, ht, htK⟩ :=
    exists_lift_with_support points M f hf X hX hsep s.val (hsK.trans hKK')
  exact ⟨⟨t, K', hK', htK⟩, Subtype.ext ht⟩

end Langlands.Sheaf.PointProduct
