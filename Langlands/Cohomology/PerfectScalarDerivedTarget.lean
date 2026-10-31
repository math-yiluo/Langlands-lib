import Langlands.Cohomology.PerfectScalarAdjunctionProof

/-! # Perfect-source Hom adjunction with arbitrary derived targets -/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe uC vC wC uD vD wD u

section General

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G)
  (K : CochainComplex C ℤ) [K.IsKProjective]
  [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K)]

/-- The canonical unit map is bijective on Hom for every derived target. -/
lemma kProjectiveDerivedTargetHom_bijective (Y : DerivedCategory D) :
    Function.Bijective (fun f :
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ Y) =>
        derivedComplexAdjunctionUnit adj K ≫ G.mapDerivedCategory.map f) := by
  let L := (DerivedCategory.Q (C := D)).objPreimage Y
  let e : DerivedCategory.Q.obj L ≅ Y :=
    (DerivedCategory.Q (C := D)).objObjPreimageIso Y
  let E := (Iso.homCongr (Iso.refl _) e).symm.trans
    ((kProjectiveDerivedAdjunctionHomEquiv adj K L).trans
      (Iso.homCongr (Iso.refl _) (G.mapDerivedCategory.mapIso e)))
  convert E.bijective using 1
  funext f
  dsimp [E]
  rw [kProjectiveDerivedAdjunctionHomEquiv_apply]
  simp [Iso.homCongr_apply, Category.assoc, ← Functor.map_comp]

/-- Hom adjunction for a K-projective source and an arbitrary derived target.
Its forward function is the canonical unit followed by the exact right adjoint. -/
def kProjectiveDerivedTargetHomEquiv (Y : DerivedCategory D) :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ Y) ≃
      (DerivedCategory.Q.obj K ⟶ G.mapDerivedCategory.obj Y) :=
  Equiv.ofBijective _ (kProjectiveDerivedTargetHom_bijective adj K Y)

@[simp]
lemma kProjectiveDerivedTargetHomEquiv_apply (Y : DerivedCategory D)
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ Y) :
    kProjectiveDerivedTargetHomEquiv adj K Y f =
      derivedComplexAdjunctionUnit adj K ≫ G.mapDerivedCategory.map f := rfl

lemma kProjectiveDerivedTargetHomEquiv_naturality
    {Y Z : DerivedCategory D}
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ Y)
    (g : Y ⟶ Z) :
    kProjectiveDerivedTargetHomEquiv adj K Z (f ≫ g) =
      kProjectiveDerivedTargetHomEquiv adj K Y f ≫ G.mapDerivedCategory.map g := by
  simp [Functor.map_comp, Category.assoc]

lemma kProjectiveDerivedTargetHomEquiv_symm_apply_eq_iff (Y : DerivedCategory D)
    (g : DerivedCategory.Q.obj K ⟶ G.mapDerivedCategory.obj Y)
    (f : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ Y) :
    (kProjectiveDerivedTargetHomEquiv adj K Y).symm g = f ↔
      derivedComplexAdjunctionUnit adj K ≫ G.mapDerivedCategory.map f = g := by
  rw [Equiv.symm_apply_eq]
  exact eq_comm

lemma kProjectiveDerivedTargetHomEquiv_Q_obj (L : CochainComplex D ℤ) :
    kProjectiveDerivedTargetHomEquiv adj K (DerivedCategory.Q.obj L) =
      kProjectiveDerivedAdjunctionHomEquiv adj K L := by
  ext f
  exact (kProjectiveDerivedAdjunctionHomEquiv_apply adj K L f).symm

end General

namespace ModuleComplex

variable {R S : Type u} [CommRing R] [CommRing S]
  [HasDerivedCategory.{wC} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wD} (ModuleCat.{u} S)]

/-- Perfect-source scalar adjunction with any actual derived target, for every
ring map, using ordinary termwise extension of the source. -/
def perfectScalarDerivedTargetHomEquiv
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (Y : DerivedCategory (ModuleCat.{u} S)) :
    (DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ Y) ≃
      (DerivedCategory.Q.obj K ⟶
        (ModuleCat.restrictScalars φ).mapDerivedCategory.obj Y) := by
  letI := isKProjective_of_isStrictlyPerfect hK
  letI : CochainComplex.IsKProjective
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) :=
    isKProjective_baseChange_of_isStrictlyPerfect φ hK
  exact kProjectiveDerivedTargetHomEquiv (ModuleCat.extendRestrictScalarsAdj φ) K Y

@[simp]
lemma perfectScalarDerivedTargetHomEquiv_apply
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (Y : DerivedCategory (ModuleCat.{u} S))
    (f : DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ Y) :
    perfectScalarDerivedTargetHomEquiv φ K hK Y f =
      derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ) K ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map f := rfl

lemma perfectScalarDerivedTargetHomEquiv_naturality
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) {Y Z : DerivedCategory (ModuleCat.{u} S)}
    (f : DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ Y) (g : Y ⟶ Z) :
    perfectScalarDerivedTargetHomEquiv φ K hK Z (f ≫ g) =
      perfectScalarDerivedTargetHomEquiv φ K hK Y f ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map g := by
  simp only [perfectScalarDerivedTargetHomEquiv_apply]
  erw [Functor.map_comp, Category.assoc]
  simp only [derivedComplexAdjunctionUnit, Category.assoc]

lemma perfectScalarDerivedTargetHomEquiv_symm_apply_eq_iff
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (Y : DerivedCategory (ModuleCat.{u} S))
    (g : DerivedCategory.Q.obj K ⟶
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj Y)
    (f : DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ Y) :
    (perfectScalarDerivedTargetHomEquiv φ K hK Y).symm g = f ↔
      derivedComplexAdjunctionUnit (ModuleCat.extendRestrictScalarsAdj φ) K ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map f = g := by
  rw [Equiv.symm_apply_eq]
  exact eq_comm

lemma perfectScalarDerivedTargetHomEquiv_Q_obj
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) (L : CochainComplex (ModuleCat.{u} S) ℤ) :
    perfectScalarDerivedTargetHomEquiv φ K hK (DerivedCategory.Q.obj L) =
      perfectScalarDerivedHomEquiv φ K hK L := by
  ext f
  exact (perfectScalarDerivedHomEquiv_apply φ K hK L f).symm

end ModuleComplex

end Langlands.Cohomology
