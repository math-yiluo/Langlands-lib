import Langlands.Cohomology.AdditiveAdjunction
import Langlands.Cohomology.PerfectModuleComplexHomotopy
import Langlands.Cohomology.PerfectScalarAdjunctionStatement
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe uC vC wC uD vD wD u

section General

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- Homotopy classes from a K-projective complex are the actual derived morphisms. -/
def kProjectiveDerivedHomEquiv (K L : CochainComplex C ℤ) [K.IsKProjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  (Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective K _)).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
      ((DerivedCategory.quotientCompQhIso C).app L))

@[simp]
lemma kProjectiveDerivedHomEquiv_quotient_map
    (K L : CochainComplex C ℤ) [K.IsKProjective] (f : K ⟶ L) :
    kProjectiveDerivedHomEquiv K L ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  dsimp [kProjectiveDerivedHomEquiv, Iso.homCongr]
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality f
  simp only [Functor.comp_map] at h
  rw [h]
  simp

@[simp]
lemma kProjectiveDerivedHomEquiv_symm_Q_map
    (K L : CochainComplex C ℤ) [K.IsKProjective] (f : K ⟶ L) :
    (kProjectiveDerivedHomEquiv K L).symm (DerivedCategory.Q.map f) =
      (HomotopyCategory.quotient C (.up ℤ)).map f := by
  apply (kProjectiveDerivedHomEquiv K L).injective
  simp

variable {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G)

/-- The canonical derived unit obtained using the exact right adjoint only. -/
def derivedComplexAdjunctionUnit (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj K ⟶ G.mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) :=
  DerivedCategory.Q.map ((complexAdjunction adj (.up ℤ)).unit.app K) ≫
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K)

/-- The Hom adjunction transported through K-projective sources. -/
def kProjectiveDerivedAdjunctionHomEquiv
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    [K.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj L) ≃
      (DerivedCategory.Q.obj K ⟶ G.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) :=
  (kProjectiveDerivedHomEquiv ((F.mapHomologicalComplex (.up ℤ)).obj K) L).symm.trans
    (((homotopyAdjunction adj (.up ℤ)).homEquiv
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient D (.up ℤ)).obj L)).trans
      ((kProjectiveDerivedHomEquiv K ((G.mapHomologicalComplex (.up ℤ)).obj L)).trans
        (Iso.homCongr (Iso.refl _) (G.mapDerivedCategoryFactors.symm.app L))))

lemma kProjectiveDerivedAdjunctionHomEquiv_Q_map
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    [K.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K)]
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    kProjectiveDerivedAdjunctionHomEquiv adj K L (DerivedCategory.Q.map f) =
      derivedComplexAdjunctionUnit adj K ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map f) := by
  simp only [kProjectiveDerivedAdjunctionHomEquiv, Equiv.trans_apply,
    kProjectiveDerivedHomEquiv_symm_Q_map, Adjunction.homEquiv_apply,
    homotopyAdjunction_unit_app_quotient, Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp, kProjectiveDerivedHomEquiv_quotient_map]
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
    derivedComplexAdjunctionUnit]
  have h := G.mapDerivedCategoryFactors.inv.naturality f
  simp only [Functor.comp_map] at h
  rw [h]

lemma kProjectiveDerivedAdjunctionHomEquiv_apply
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    [K.IsKProjective] [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K)]
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj L) :
    kProjectiveDerivedAdjunctionHomEquiv adj K L f =
      derivedComplexAdjunctionUnit adj K ≫ G.mapDerivedCategory.map f := by
  obtain ⟨g, hg⟩ :=
    (kProjectiveDerivedHomEquiv ((F.mapHomologicalComplex (.up ℤ)).obj K) L).surjective f
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient D (.up ℤ)).map_surjective g
  rw [kProjectiveDerivedHomEquiv_quotient_map] at hg
  subst f
  exact kProjectiveDerivedAdjunctionHomEquiv_Q_map adj K L g

end General

namespace ModuleComplex

variable {R S : Type u} [CommRing R] [CommRing S]

lemma isKProjective_baseChange_of_isStrictlyPerfect
    (φ : R →+* S) {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) :
    CochainComplex.IsKProjective ((baseChange φ).obj K) := by
  obtain ⟨a, b, _, hb⟩ := hK.1
  let := hb
  let : ∀ n : ℤ, Module.Projective R (K.X n) := fun n => (hK.2 n).2
  let : ∀ n : ℤ, Projective (K.X n) := fun n => inferInstance
  let : ∀ n : ℤ, Projective (((baseChange φ).obj K).X n) := fun n =>
    (ModuleCat.extendRestrictScalarsAdj φ).map_projective (K.X n) inferInstance
  let : CochainComplex.IsStrictlyLE ((baseChange φ).obj K) b := by
    change CochainComplex.IsStrictlyLE
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) b
    infer_instance
  exact CochainComplex.isKProjective_of_projective ((baseChange φ).obj K) b

variable [HasDerivedCategory.{wC} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wD} (ModuleCat.{u} S)]

/-- Actual derived Hom adjunction for ordinary scalar extension of a perfect source. -/
def perfectScalarDerivedHomEquiv
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (L : CochainComplex (ModuleCat.{u} S) ℤ) :
    (DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ DerivedCategory.Q.obj L) ≃
      (DerivedCategory.Q.obj K ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
        (DerivedCategory.Q.obj L)) := by
  letI := isKProjective_of_isStrictlyPerfect hK
  letI : CochainComplex.IsKProjective
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) :=
    isKProjective_baseChange_of_isStrictlyPerfect φ hK
  exact kProjectiveDerivedAdjunctionHomEquiv (ModuleCat.extendRestrictScalarsAdj φ) K L

lemma perfectScalarDerivedHomEquiv_apply
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (f : DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ DerivedCategory.Q.obj L) :
    perfectScalarDerivedHomEquiv φ K hK L f =
      derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ) K ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map f := by
  let := isKProjective_of_isStrictlyPerfect hK
  let : CochainComplex.IsKProjective
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) :=
    isKProjective_baseChange_of_isStrictlyPerfect φ hK
  exact kProjectiveDerivedAdjunctionHomEquiv_apply (ModuleCat.extendRestrictScalarsAdj φ) K L f

attribute [local instance] HasDerivedCategory.standard in
theorem perfectScalarAdjunction : PerfectScalarAdjunctionStatement.{u} := by
  intro R S _ _ φ K hK L
  convert (perfectScalarDerivedHomEquiv φ K hK L).bijective using 1
  funext f
  exact (perfectScalarDerivedHomEquiv_apply φ K hK L f).symm

end ModuleComplex

end Langlands.Cohomology
