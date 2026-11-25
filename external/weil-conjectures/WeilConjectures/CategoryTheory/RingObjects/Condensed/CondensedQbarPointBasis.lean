/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! Finite-support coordinates for the condensed algebraic closure.

Source: the finite-subextension-valued section model of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`, and the
finite-basis template `continuousBasisSheafIso` in Colimit/Compatibility.lean.
(blueprint: lem-weil-pbc-condensed-qbar-point-basis) -/

-- After dropping the copy of upstream's declaration, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u v w

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod
section MapCopower
open MonObj
variable {C : Type w} [Category.{v} C] [MonoidalCategory C]
  {D : Type*} [Category.{v} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]

private noncomputable def mapRegularIso :
    (F.mapMod R).obj (regular R) ≅ regular (F.obj R) :=
  isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])

private noncomputable def mapRestrictedRegularIso :
    (F.mapMod R).obj ((comap a).obj (regular S)) ≅
      (comap (F.map a)).obj (regular (F.obj S)) :=
  (F.mapModComapIso a).app (regular S) ≪≫
    (comap (F.map a)).mapIso (mapRegularIso F)

variable {I : Type v} [HasCoproductsOfShape I (Mod C R)]
  [HasCoproductsOfShape I (Mod D (F.obj R))]
  [PreservesColimitsOfShape (Discrete I) (F.mapMod R)]

private noncomputable def mapCopowerIso
    (e : (∐ fun _ : I ↦ regular R) ≅ (comap a).obj (regular S)) :
    (∐ fun _ : I ↦ regular (F.obj R)) ≅ (comap (F.map a)).obj (regular (F.obj S)) :=
  Sigma.mapIso (fun _ ↦ (mapRegularIso F).symm) ≪≫
    asIso (sigmaComparison (F.mapMod R) (fun _ : I ↦ regular R)) ≪≫
    (F.mapMod R).mapIso e ≪≫ mapRestrictedRegularIso F a

end MapCopower
end CategoryTheory.Mod

namespace CategoryTheory.Mod
open MonObj
section RingIso
variable {C : Type w} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S]
private noncomputable def regularRingIso (r : R ≅ S) [IsMonHom r.hom] :
    (comap r.inv).obj (regular R) ≅ regular S :=
  isoMk r (by
    change (r.inv ▷ R ≫ μ[R]) ≫ r.hom = S ◁ r.hom ≫ μ[S]
    rw [Category.assoc, IsMonHom.mul_hom]
    rw [MonoidalCategory.tensorHom_def]
    rw [Category.assoc, ← comp_whiskerRight_assoc, r.inv_hom_id,
      id_whiskerRight, Category.id_comp])
variable {R' S' : C} [MonObj R'] [MonObj S']
private noncomputable def restrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a) :
    (comap a').obj (regular S') ≅
      (comap r.inv).obj ((comap a).obj (regular S)) := by
  let es := regularRingIso s
  exact (comap a').mapIso es.symm ≪≫
    ((comapComp a' s.inv).symm ≪≫ comapCongr h ≪≫ comapComp r.inv a).app _
variable {I : Type v} [HasCoproductsOfShape I (Mod C R)]
  [HasCoproductsOfShape I (Mod C R')]
private noncomputable def comapCopowerIso (r : R ≅ R') [IsMonHom r.hom]
    [PreservesColimitsOfShape (Discrete I) (comap (D := C) r.inv)] :
    (comap r.inv).obj (∐ fun _ : I ↦ regular R) ≅ (∐ fun _ : I ↦ regular R') :=
  (asIso (sigmaComparison (comap r.inv) (fun _ : I ↦ regular R))).symm ≪≫
    Sigma.mapIso (fun _ ↦ regularRingIso r)
end RingIso
end CategoryTheory.Mod

namespace Profinite
open IntermediateField

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

private lemma coord_continuous_on_field {I : Type v} (b : Module.Basis I E (PadicAlgCl ℓ))
    (i : I) (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    Continuous (fun x : F ↦ b.coord i (x : PadicAlgCl ℓ)) := by
  let l := ((b.coord i).restrictScalars ℚ_[ℓ]).comp F.1.val.toLinearMap
  exact l.continuous_of_finiteDimensional

private lemma field_uniform_support {I : Type v} (b : Module.Basis I E (PadicAlgCl ℓ))
    (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ t : Finset I, ∀ x : F, (b.repr (x : PadicAlgCl ℓ)).support ⊆ t := by
  classical
  let c := Module.finBasis ℚ_[ℓ] F
  let t := Finset.univ.biUnion (fun j ↦ (b.repr (c j : PadicAlgCl ℓ)).support)
  refine ⟨t, fun x i hi ↦ ?_⟩
  by_contra hit
  have hz (j : Fin (Module.finrank ℚ_[ℓ] F)) : b.coord i (c j : PadicAlgCl ℓ) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hij
    exact hit (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩)
  have hzero : b.coord i (x : PadicAlgCl ℓ) = 0 := by
    rw [← c.sum_repr x]
    change (((b.coord i).restrictScalars ℚ_[ℓ]).comp F.1.val.toLinearMap)
      (∑ j, c.repr x j • c j) = 0
    simp only [map_sum, map_smul, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply]
    apply Finset.sum_eq_zero
    intro j _
    change _ • b.coord i (c j : PadicAlgCl ℓ) = 0
    rw [hz, smul_zero]
  exact (Finsupp.mem_support_iff.mp hi) hzero

private lemma section_coord_continuous {I : Type v} (b : Module.Basis I E (PadicAlgCl ℓ))
    (U : Profinite.{u}) (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) (i : I) :
    Continuous (fun x : U ↦ b.coord i ((f : C(U, PadicAlgCl ℓ)) x)) := by
  obtain ⟨F, hF, hf⟩ := f.property
  exact (coord_continuous_on_field ℓ E b i ⟨F, hF⟩).comp
    ((f : C(U, PadicAlgCl ℓ)).continuous.subtype_mk hf)

private noncomputable def sectionCoordinates {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u})
    (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) : I →₀ C(U, E) :=
  Finsupp.ofSupportFinite
    (fun i ↦ ⟨fun x ↦ b.coord i ((f : C(U, PadicAlgCl ℓ)) x),
      section_coord_continuous ℓ E b U f i⟩) (by
        classical
        obtain ⟨F, hF, hf⟩ := f.property
        obtain ⟨t, ht⟩ := field_uniform_support ℓ E b ⟨F, hF⟩
        apply t.finite_toSet.subset
        intro i hi
        by_contra hit
        apply hi
        apply ContinuousMap.ext
        intro x
        exact Finsupp.notMem_support_iff.mp
          (fun hm ↦ hit (ht ⟨(f : C(U, PadicAlgCl ℓ)) x, hf x⟩ hm)))

@[simp] private lemma sectionCoordinates_apply {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u})
    (f : PadicAlgCl.finiteIntermediateFieldValued ℓ U) (i : I) (t : U) :
    sectionCoordinates ℓ E b U f i t = b.coord i ((f : C(U, PadicAlgCl ℓ)) t) := by
  simp only [sectionCoordinates, Finsupp.ofSupportFinite_coe, ContinuousMap.coe_mk]

private noncomputable def scalarSection (U : Profinite.{u}) (x : PadicAlgCl ℓ)
    (f : C(U, E)) : PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
  ⟨⟨fun t ↦ (f t : PadicAlgCl ℓ) * x,
    (continuous_subtype_val.comp f.continuous).mul_const x⟩, by
      have hx : FiniteDimensional ℚ_[ℓ] ℚ_[ℓ]⟮x⟯ :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
      refine ⟨E.1 ⊔ ℚ_[ℓ]⟮x⟯, inferInstance, fun t ↦ ?_⟩
      exact mul_mem (IsConcreteLE.le_iff.mp le_sup_left (f t).property)
        (IsConcreteLE.le_iff.mp le_sup_right (IntermediateField.mem_adjoin_simple_self _ _))⟩

private noncomputable def scalarSectionHom (U : Profinite.{u}) (x : PadicAlgCl ℓ) :
    C(U, E) →+ PadicAlgCl.finiteIntermediateFieldValued ℓ U where
  toFun := scalarSection ℓ E U x
  map_zero' := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change (0 : PadicAlgCl ℓ) * x = 0
    exact zero_mul x
  map_add' f g := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change ((f t : PadicAlgCl ℓ) + g t) * x = (f t : PadicAlgCl ℓ) * x + g t * x
    exact add_mul _ _ _

private noncomputable def sectionCoordinatesHom {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    PadicAlgCl.finiteIntermediateFieldValued ℓ U →+ (I →₀ C(U, E)) where
  toFun := sectionCoordinates ℓ E b U
  map_zero' := by
    apply Finsupp.ext
    intro i
    apply ContinuousMap.ext
    intro t
    simp only [sectionCoordinates_apply, Finsupp.zero_apply, ContinuousMap.zero_apply]
    exact map_zero (b.coord i)
  map_add' f g := by
    apply Finsupp.ext
    intro i
    apply ContinuousMap.ext
    intro t
    simp only [sectionCoordinates_apply, Finsupp.add_apply, ContinuousMap.add_apply]
    exact map_add (b.coord i) _ _

private lemma sectionCoordinates_injective {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    Function.Injective (sectionCoordinatesHom ℓ E b U) := by
  intro f g h
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have he := congrArg (fun a : I →₀ C(U, E) ↦ a i t) h
  simpa only [sectionCoordinatesHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sectionCoordinates_apply, Module.Basis.coord_apply] using he

private lemma sectionCoordinates_scalarSection {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) (i : I) (f : C(U, E)) :
    sectionCoordinatesHom ℓ E b U (scalarSection ℓ E U (b i) f) = Finsupp.single i f := by
  classical
  apply Finsupp.ext
  intro j
  apply ContinuousMap.ext
  intro t
  simp only [sectionCoordinatesHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    sectionCoordinates_apply]
  change b.coord j ((f t : PadicAlgCl ℓ) * b i) = (Finsupp.single i f) j t
  change b.coord j ((algebraMap E (PadicAlgCl ℓ)) (f t) * b i) = _
  rw [← Algebra.smul_def, map_smul]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Module.Basis.coord_apply, Ne.symm hij]

private noncomputable def sectionSum {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    (I →₀ C(U, E)) →+ PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
  Finsupp.liftAddHom (fun i ↦ scalarSectionHom ℓ E U (b i))

private lemma sectionCoordinates_sectionSum {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    (sectionCoordinatesHom ℓ E b U).comp (sectionSum ℓ E b U) = AddMonoidHom.id _ := by
  apply Finsupp.addHom_ext
  intro i f
  change sectionCoordinatesHom ℓ E b U (sectionSum ℓ E b U (Finsupp.single i f)) = _
  simpa only [sectionSum, Finsupp.liftAddHom_apply_single, scalarSectionHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.id_apply] using
      sectionCoordinates_scalarSection ℓ E b U i f

private noncomputable def sectionBasisEquiv {I : Type v}
    (b : Module.Basis I E (PadicAlgCl ℓ)) (U : Profinite.{u}) :
    (I →₀ C(U, E)) ≃+ PadicAlgCl.finiteIntermediateFieldValued ℓ U :=
  AddEquiv.ofBijective (sectionSum ℓ E b U) (by
    have h := sectionCoordinates_sectionSum ℓ E b U
    have hf : Function.LeftInverse (sectionCoordinatesHom ℓ E b U) (sectionSum ℓ E b U) :=
      DFunLike.congr_fun h
    refine ⟨hf.injective, fun f ↦ ⟨sectionCoordinatesHom ℓ E b U f, ?_⟩⟩
    apply sectionCoordinates_injective ℓ E b U
    exact hf _)

private noncomputable abbrev pointRPresheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  continuousMapRingPresheaf E ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}

private noncomputable abbrev pointSPresheaf : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  padicAlgClRingPresheaf ℓ ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}

private noncomputable def scalarPresheaf (x : PadicAlgCl ℓ) :
    pointRPresheaf.{u} ℓ E ⟶ pointSPresheaf ℓ where
  app U := AddCommGrpCat.ofHom
    (ULift.ringEquiv.symm.toAddMonoidHom.comp
      ((scalarSectionHom ℓ E U.unop x).comp ULift.ringEquiv.toAddMonoidHom))
  naturality _ _ _ := rfl

private noncomputable abbrev pointMapPresheaf :
    pointRPresheaf.{u} ℓ E ⟶ pointSPresheaf ℓ :=
  Functor.whiskerRight (padicSubfieldToPadicAlgClRingPresheaf ℓ E)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})

private noncomputable def scalarModulePresheaf (x : PadicAlgCl ℓ) :
    Mod.regular (pointRPresheaf.{u} ℓ E) ⟶
      (Mod.comap (pointMapPresheaf ℓ E)).obj (Mod.regular (pointSPresheaf ℓ)) :=
  Mod.homMk (scalarPresheaf ℓ E x) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up _ = ULift.up _
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change ((r.down t : PadicAlgCl ℓ) * s.down t) * x =
      (r.down t : PadicAlgCl ℓ) * ((s.down t : PadicAlgCl ℓ) * x)
    exact mul_assoc _ _ _)

private noncomputable def basisPresheafCofan {I : Type (u + 1)}
    (b : Module.Basis I E (PadicAlgCl ℓ)) :
    Cofan (fun _ : I ↦ Mod.regular (pointRPresheaf.{u} ℓ E)) :=
  Cofan.mk ((Mod.comap (pointMapPresheaf ℓ E)).obj (Mod.regular (pointSPresheaf ℓ)))
    (fun i ↦ scalarModulePresheaf ℓ E (b i))

private theorem pointR_preservesCoproducts (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (tensorLeft (pointRPresheaf.{u} ℓ E)) := by
  apply preservesColimitsOfShape_of_evaluation
  intro U
  let ev := (evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj U
  have e : tensorLeft (pointRPresheaf ℓ E) ⋙ ev ≅
      ev ⋙ tensorLeft ((pointRPresheaf ℓ E).obj U) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact preservesColimitsOfShape_of_natIso e.symm

private noncomputable def basisPresheafCofanIsColimit {I : Type (u + 1)}
    (b : Module.Basis I E (PadicAlgCl ℓ)) : IsColimit (basisPresheafCofan ℓ E b) := by
  have := pointR_preservesCoproducts ℓ E I
  have : ReflectsColimitsOfShape (Discrete I)
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (pointRPresheaf ℓ E)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (pointRPresheaf ℓ E))
  apply evaluationJointlyReflectsColimits
  intro U
  let A := ULift.{u + 1} C(U.unop, E)
  let d := ModuleCat.finsuppCocone ℤ A I
  let hd := isColimitOfPreserves (forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1})
    (ModuleCat.finsuppCoconeIsColimit ℤ A I)
  let e : (I →₀ A) ≃+ ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ U.unop) :=
    (Finsupp.mapRange.addEquiv ULift.ringEquiv.toAddEquiv).trans
      ((sectionBasisEquiv ℓ E b U.unop).trans ULift.ringEquiv.symm.toAddEquiv)
  apply IsColimit.ofIsoColimit hd
  refine Cocone.ext (e.toAddCommGrpIso) ?_
  intro i
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  change e (Finsupp.single i.as f) = ULift.up (scalarSection ℓ E U.unop (b i.as) f.down)
  simp only [e, AddEquiv.trans_apply, Finsupp.mapRange.addEquiv_apply,
    Finsupp.mapRange_single]
  change ULift.up (sectionSum ℓ E b U.unop (Finsupp.single i.as f.down)) = _
  simp only [sectionSum, Finsupp.liftAddHom_apply_single]
  rfl

end Profinite
