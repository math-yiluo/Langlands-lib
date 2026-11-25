/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction

/-! # The ordered Čech fibre on the ideal complement

Source: Stacks Project, Tag 099D(d), and Cohomology, ordered Čech complexes.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section

/-- The principal-open family on the complement of the ideal's zero locus. -/
def ringComplexPrincipalCover (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) : Fin r → (ringComplexOpen A I).toScheme.Opens :=
  fun i ↦ (ringComplexOpen A I).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)

/-- A generating family covers the ideal complement, also for the empty list. -/
theorem ringComplexPrincipalCover_iSup (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    iSup (ringComplexPrincipalCover A I f) = ⊤ := by
  classical
  apply top_unique
  intro x _
  have hx : ¬ I ≤ x.val.asIdeal := x.property
  have hy : ¬ Ideal.span (Set.range f) ≤ x.val.asIdeal := by simpa only [hf] using hx
  rw [Ideal.span_le, Set.range_subset_iff] at hy
  obtain ⟨i, hi⟩ := not_forall.mp hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

/-- Exact change of coefficients from sections on the complement to the ring site. -/
def ringComplexSectionScalars (A : CommRingCat.{u}) (I : Ideal A) :
    ModuleCat.{u} Γ((ringComplexOpen A I).toScheme, ⊤) ⥤ RingSiteModules A :=
  ModuleCat.restrictScalars (ringComplexOpenRingMap A I) ⋙ ringComplexConstant A

instance ringComplexSectionScalars_additive (A : CommRingCat.{u}) (I : Ideal A) :
    (ringComplexSectionScalars A I).Additive := by
  unfold ringComplexSectionScalars
  infer_instance

/-- The coefficient restriction before applying a resolution or a Čech augmentation. -/
def ringComplexStructureRestriction (A : CommRingCat.{u}) (I : Ideal A) :
    ringComplexUnit A ⟶ (ringComplexOpenSections A I).obj
      (SheafOfModules.unit (moduleRings (ringComplexOpen A I).toScheme.toRingedSpace)) :=
by
  let X := (ringComplexOpen A I).toScheme
  let F := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let ρ := ringComplexOpenRingMap A I
  let v : A →ₗ[A] ((ModuleCat.restrictScalars ρ).obj
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F)) :=
    { toFun := ρ
      map_add' := ρ.map_add
      map_smul' := by intro a b; exact ρ.map_mul a b }
  exact (ringComplexConstant A).map (ModuleCat.ofHom v)

/-- The unaugmented ordered Čech sections of the structure module, with A-scalars. -/
def ringComplexOrderedCechSections (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) : CochainComplex (RingSiteModules A) ℤ :=
  ((ringComplexSectionScalars A I).mapHomologicalComplex (.up ℤ)).obj
    ((alternatingCechModuleFunctor (ringComplexPrincipalCover A I f)).obj
      (SheafOfModules.unit (moduleRings (ringComplexOpen A I).toScheme.toRingedSpace)))

private theorem orderedZero_closed {X : Scheme.{u}} {r : ℕ} (V : Fin r → X.Opens)
    (F : X.Modules) :
    alternatingCechZero V F ≫ ((alternatingCechModuleFunctor V).obj F).d 0 1 = 0 := by
  classical
  let P := (alternatingCechModulePresheaf (X := X)).obj F
  have h : alternatingCechPresheafZero V P ≫ (alternatingCechComplex V P).d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
      (P.map (homOfLE (alternatingCechIntersection_face_le V 0 t j)).op).hom
        ((P.map (homOfLE (le_top (a := alternatingCechIntersection V
          ((Fin.succAboveOrderEmb j).trans t)))).op).hom x)) = 0
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_smul, neg_smul, add_neg_eq_zero]
    change ((P.map _ ≫ P.map _).hom x) = ((P.map _ ≫ P.map _).hom x)
    rw [← P.map_comp, ← P.map_comp]
    congr 2
  unfold alternatingCechZero
  change _ ≫ ((alternatingCechComplex V P).extend ComplexShape.embeddingUpNat).d 0 1 = 0
  erw [HomologicalComplex.extend_d_eq _ _ (i := 0) (j := 1) rfl rfl]
  dsimp only [P] at h ⊢
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [← Category.assoc (alternatingCechPresheafZero V P)
    ((alternatingCechComplex V P).d 0 1), h]
  simp only [zero_comp, comp_zero]

/-- The degree-zero restriction into ordered Čech sections. -/
def ringComplexOrderedCechFirst (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :
    ringComplexUnit A ⟶ (ringComplexOrderedCechSections A I f).X 0 :=
  ringComplexStructureRestriction A I ≫ (ringComplexSectionScalars A I).map
    (alternatingCechZero (ringComplexPrincipalCover A I f)
      (SheafOfModules.unit (moduleRings (ringComplexOpen A I).toScheme.toRingedSpace)))

/-- The first restriction is killed by the alternating restriction differential. -/
theorem ringComplexOrderedCechFirst_closed (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    ringComplexOrderedCechFirst A I f ≫ (ringComplexOrderedCechSections A I f).d 0 k = 0 := by
  have : k = 1 := by simpa using hk.symm
  subst k
  unfold ringComplexOrderedCechFirst ringComplexOrderedCechSections
  change (_ ≫ (ringComplexSectionScalars A I).map _) ≫
    (ringComplexSectionScalars A I).map _ = 0
  rw [Category.assoc, ← Functor.map_comp]
  erw [orderedZero_closed]
  rw [Functor.map_zero, comp_zero]

/-- The ordered Čech restriction map from A[0]. -/
def ringComplexOrderedCechRestriction (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) :
    ringComplexSingle A ⟶ ringComplexOrderedCechSections A I f :=
  HomologicalComplex.mkHomFromSingle (ringComplexOrderedCechFirst A I f)
    (ringComplexOrderedCechFirst_closed A I f)

/-- The ordered Čech mapping fibre, with the same inverse-rotation convention as Godement. -/
def ringComplexOrderedCech (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) : CochainComplex (RingSiteModules A) ℤ :=
  (CochainComplex.mappingCone.triangle (ringComplexOrderedCechRestriction A I f)).invRotate.obj₁

/-- Projection of the ordered Čech fibre to A[0]. -/
def ringComplexOrderedCechAugmentation (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) : ringComplexOrderedCech A I f ⟶ ringComplexSingle A :=
  (CochainComplex.mappingCone.triangle (ringComplexOrderedCechRestriction A I f)).invRotate.mor₁

end
end AlgebraicGeometry
