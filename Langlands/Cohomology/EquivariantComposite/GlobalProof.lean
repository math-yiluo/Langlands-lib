import Langlands.Cohomology.EquivariantComposite.Statement
import Langlands.Cohomology.EquivariantComposite.ConstantAdjunction
import Langlands.Cohomology.EquivariantComposite.KInjectiveHomology
import Langlands.Cohomology.EquivariantComposite.InvariantsHom
import Langlands.Cohomology.AcyclicResolution.DerivedComparison

/-! # The global equivariant composite comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology.EquivariantComposite

section Resolution

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] (T : C ⥤ D) [T.Additive]

/-- Integer-indexed resolution homology computes the ordinary right derived functor. -/
def resolutionRightDerivedIso {A : C} (I : InjectiveResolution A) (n : ℕ) :
    ((T.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ) ≅
      (T.rightDerived n).obj A :=
  HomologicalComplex.homologyMapIso
    (DerivedPlus.mapExtendIso T I.cocomplex ComplexShape.embeddingUpNat).symm (n : ℤ) ≪≫
    ((T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    (I.isoRightDerivedObj T n).symm

/-- The resolution-homology comparison commutes with every lifted coefficient map. -/
@[reassoc]
lemma resolutionRightDerivedIso_hom_naturality {A B : C} {f : A ⟶ B}
    {I : InjectiveResolution A} {J : InjectiveResolution B}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫
        (resolutionRightDerivedIso T J n).hom =
      (resolutionRightDerivedIso T I n).hom ≫ (T.rightDerived n).map f := by
  have comm : I.ι.f 0 ≫ φ.hom.f 0 = f ≫ J.ι.f 0 :=
    φ.ι_f_zero_comp_hom_f_zero.trans (by rw [CochainComplex.single₀_map_f_zero])
  have h₂ := extendMapIso_hom_naturality ComplexShape.embeddingUpNat T φ.hom
  have h₃ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((T.mapHomologicalComplex (.up ℕ)).map φ.hom) ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  have h₄ := InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ.hom comm T n
  have h₅ : HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso T J.cocomplex ComplexShape.embeddingUpNat).inv (n : ℤ) =
      HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso T I.cocomplex ComplexShape.embeddingUpNat).inv (n : ℤ) ≫
        HomologicalComplex.homologyMap (HomologicalComplex.extendMap
          ((T.mapHomologicalComplex (.up ℕ)).map φ.hom)
            ComplexShape.embeddingUpNat) (n : ℤ) :=
    (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ)) h₂).trans
        (HomologicalComplex.homologyMap_comp _ _ _))
  simp only [resolutionRightDerivedIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, Category.assoc]
  rw [reassoc_of% h₅, reassoc_of% h₃, h₄]
  rfl

end Resolution

universe w w' u

variable (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]
  [HasDerivedCategory.{w} (TopologicalSheaf G X (ModuleCat.{u} R))]
  [HasDerivedCategory.{w'} (Rep.{u} R G)]

/-- Sections of an extended injective resolution form a K-injective representation complex. -/
instance sectionResolution_isKInjective {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (I : InjectiveResolution F) :
    CochainComplex.IsKInjective
      (((sectionRepresentation R G X).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) := by
  have (n : ℤ) : Injective
      ((((sectionRepresentation R G X).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).X n) := (sectionRepresentation R G X).injective_obj_of_injective
      (inferInstanceAs (Injective (I.cochainComplex.X n)))
  exact CochainComplex.isKInjective_of_injective _ 0

/-- The global composite comparison computed using a specified injective resolution. -/
def globalComparisonOfResolution {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (I : InjectiveResolution F) (n : ℕ) :
    (EquivariantDerivedSections.invariantGlobalDerived R G X n).obj F ≃+
      ShiftedHom ((DerivedCategory.singleFunctor (Rep.{u} R G) 0).obj (Rep.trivial R G R))
        (DerivedCategory.Plus.ι.obj ((EquivariantDerivedComplex.globalComplex R G X).obj F))
        (n : ℤ) :=
  (((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapIso
    (resolutionRightDerivedIso (EquivariantDerivedSections.invariantGlobalSections R G X)
      I n).symm).addCommGroupIsoToAddEquiv).trans
    (((invariantsHomologyIso R G (.up ℤ) (n : ℤ)).app
      (((sectionRepresentation R G X).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex)).addCommGroupIsoToAddEquiv.trans
      ((homologyDerivedAddEquiv (Rep.trivial R G R)
        (((sectionRepresentation R G X).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex) (n : ℤ)).trans
        { toEquiv := ((shiftFunctor (DerivedCategory (Rep.{u} R G)) (n : ℤ)).mapIso
            (AcyclicResolution.derivedResolutionIso (sectionRepresentation R G X) I).symm).homToEquiv
          map_add' := fun _ _ => CategoryTheory.Preadditive.add_comp _ _ _ _ _ _ }))

/-- The comparison is natural with respect to a map of injective resolutions. -/
lemma globalComparisonOfResolution_naturality
    {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} {f : F ⟶ F'}
    {I : InjectiveResolution F} {J : InjectiveResolution F'}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ)
    (x : (EquivariantDerivedSections.invariantGlobalDerived R G X n).obj F) :
    globalComparisonOfResolution R G X J n
        ((EquivariantDerivedSections.invariantGlobalDerived R G X n).map f x) =
      globalComparisonOfResolution R G X I n x ≫ (DerivedCategory.Plus.ι.map
        ((EquivariantDerivedComplex.globalComplex R G X).map f))⟦(n : ℤ)⟧' := by
  let T := EquivariantDerivedSections.invariantGlobalSections R G X
  let S := sectionRepresentation R G X
  let K := (S.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L := (S.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let g := (S.mapHomologicalComplex (.up ℤ)).map φ.hom'
  have h₁ : (T.rightDerived n).map f ≫ (resolutionRightDerivedIso T J n).inv =
      (resolutionRightDerivedIso T I n).inv ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map φ.hom')
          (n : ℤ) := by
    rw [← cancel_epi (resolutionRightDerivedIso T I n).hom, ← Category.assoc,
      ← resolutionRightDerivedIso_hom_naturality T φ n, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have h₂ := (invariantsHomologyIso R G (.up ℤ) (n : ℤ)).hom.naturality g
  have h₃ : DerivedCategory.Q.map g ≫
        (AcyclicResolution.derivedResolutionIso S J).inv =
      (AcyclicResolution.derivedResolutionIso S I).inv ≫
        (DerivedPlus.derivedComplex S ⋙ DerivedCategory.Plus.ι).map f := by
    rw [← cancel_mono (AcyclicResolution.derivedResolutionIso S J).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [AcyclicResolution.derivedResolutionIso_hom_naturality S φ,
      Iso.inv_hom_id_assoc]
    rfl
  have h₁x := ConcreteCategory.congr_hom h₁ x
  have h₂x := ConcreteCategory.congr_hom h₂ ((resolutionRightDerivedIso T I n).inv x)
  change homologyDerivedAddEquiv (Rep.trivial R G R) L (n : ℤ)
      ((invariantsHomologyIso R G (.up ℤ) (n : ℤ)).hom.app L
        ((resolutionRightDerivedIso T J n).inv ((T.rightDerived n).map f x))) ≫
        (AcyclicResolution.derivedResolutionIso S J).inv⟦(n : ℤ)⟧' =
    (homologyDerivedAddEquiv (Rep.trivial R G R) K (n : ℤ)
      ((invariantsHomologyIso R G (.up ℤ) (n : ℤ)).hom.app K
        ((resolutionRightDerivedIso T I n).inv x)) ≫
        (AcyclicResolution.derivedResolutionIso S I).inv⟦(n : ℤ)⟧') ≫
      ((DerivedPlus.derivedComplex S ⋙ DerivedCategory.Plus.ι).map f)⟦(n : ℤ)⟧'
  erw [h₁x, h₂x, homologyDerivedAddEquiv_naturality (Rep.trivial R G R) g (n : ℤ)]
  rw [Category.assoc, ← Functor.map_comp, h₃, Functor.map_comp, ← Category.assoc]
  rfl

/-- The unchanged global equivariant composite statement, at independent universes. -/
theorem equivariantGlobalComposite : EquivariantGlobalCompositeStatement.{w, w', u} := by
  intro R G X _ _ _ _ _ _ _ n
  refine ⟨fun F => globalComparisonOfResolution R G X (injectiveResolution F) n, ?_⟩
  intro F F' f x
  exact globalComparisonOfResolution_naturality R G X
    (DerivedPlus.descHom f (injectiveResolution F) (injectiveResolution F')) n x

end Langlands.Cohomology.EquivariantComposite
