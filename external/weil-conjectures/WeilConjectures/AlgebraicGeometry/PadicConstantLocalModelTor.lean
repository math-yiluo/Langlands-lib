/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.AlgebraicGeometry.LocalModelTorBoundDescent
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint

set_option linter.privateModule false

/-! # Tor intervals for finite constant p-adic scalar models -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj ZeroObject TensorProduct
open Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] constantScalarSheaf_laxBraided

attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso Functor.mapDerivedCategorySingleFunctor
  _root_.DerivedCategory.instMonoidalCategory

private theorem tor_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (K : _root_.DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (a b : ℤ)
    (hK : ∀ i, _root_.DerivedCategory.torAmplitudeIn _ a b
      ((CondensedRing.upperStar Λ (U.f i)).mapDerivedCategory.obj K)) :
    _root_.DerivedCategory.torAmplitudeIn _ a b K := by
  intro M
  let T := K ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj M
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj T) := by
    apply coverHomologyZero (Mon.mk Λ) X U T q
    intro i
    let F := CondensedRing.upperStar Λ (U.f i)
    let e := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (U.f i)
    let t := ((CondensedRing.leftDerivedUpperStarTensorIso Λ (U.f i)).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M)
    let d := transportTensorIso F.mapDerivedCategory _ e K
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M)
      (F.mapDerivedCategory.obj K) ((_root_.DerivedCategory.singleFunctor _ 0).obj (F.obj M))
      (Iso.refl _) ((F.mapDerivedCategorySingleFunctor 0).app M) t
    have ht := (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      d.symm (hK i (F.obj M))
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff _ a).mp ht.1 q hq
    · exact (_root_.DerivedCategory.isLE_iff _ b).mp ht.2 q hq
  exact ⟨(_root_.DerivedCategory.isGE_iff T a).mpr (fun q hq ↦ hz q (Or.inl hq)),
    (_root_.DerivedCategory.isLE_iff T b).mpr (fun q hq ↦ hz q (Or.inr hq))⟩

private noncomputable def ringFreeCoordinates
    {K : Type (u + 1)} [CommRing K]
    {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
    (R : D) (F : D ⥤ ModuleCat.{u + 1} K) [F.Additive]
    (e : F.obj R ≃ₗ[K] K) (n : ℕ) :
    F.obj (⨁ fun _ : Fin n ↦ R) ≃ₗ[K] (Fin n → K) :=
  ((F.mapBiproduct (fun _ : Fin n ↦ R)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ F.obj R)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

private noncomputable def continuousScalarEquiv
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    ULift.{u + 1} A ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A) where
  toFun a := ULift.up (ContinuousMap.const _ a.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext x
    exact congrArg f.down (Subsingleton.elim PUnit.unit x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

section CounitScalar

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (S : D) [MonObj S] [IsCommMonObj (F.obj (G.obj S))]

/-- Extending constant scalar modules along the counit is left adjoint to sections.
Source: blueprint local boundary duality, Step 5, scalar extension adjunction.
Proof: compose the module lift of the monoidal adjunction with extension/restriction
of scalars. The resulting restriction is along the unit followed by the image of
its counit; the right triangle identity identifies this with restriction along the
identity. This also applies to the zero algebra and the zero module.
(blueprint: lem-a1-condensed-point-scalar-adjunction) -/
def counitScalarAdjunction :
    F.mapMod (G.obj S) ⋙ Mod.extendScalars (adj.counitAlgHom S) ⊣ G.mapMod S := by
  let a := (adj.mapModAdjunction (G.obj S)).comp
    (Mod.extendRestrictAdjunction (adj.counitAlgHom S))
  refine a.ofNatIsoRight ?_
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (adj.counitAlgHom S)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (G.mapMod S)
      ((Mod.comapComp (adj.unitAlgHom (G.obj S)) (G.map (adj.counitAlgHom S))).symm ≪≫
        Mod.comapCongr (adj.right_triangle_components S) ≪≫ Mod.comapId (G.obj S)) ≪≫
    Functor.rightUnitor (G.mapMod S)

end CounitScalar

private instance constantScalarSheaf_laxBraided :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided := by
  letI : (Functor.const Profinite.{u}ᵒᵖ :
      Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}).LaxBraided :=
    { braided := by intros; ext; simp [Functor.LaxMonoidal.μ]; rfl }
  exact inferInstanceAs (Functor.const Profinite.{u}ᵒᵖ ⋙
    presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided

private noncomputable abbrev scalarCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (scalarRingObj Λ) ⟶ Λ :=
  (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit).counit.app Λ

private instance scalarCounit_mon
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsMonHom (scalarCounit Λ) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := scalarSections.{u}
  let adj : C ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  exact adj.isMonHom_counitAlgHom Λ

private instance counitSource_comm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (scalarRingObj Λ)) := Functor.isCommMonObj_obj

attribute [local irreducible] Mod.extendScalars Mod.extendScalarsComp
  Mod.extendScalarsIsoOfEq Mod.extendScalarsIsoComapInv
  Mod.extendRestrictAdjunction Mod.regularExtensionIso
  scalarCoefficientHom finiteConstantScalarExtension

private noncomputable def pointExtensionMapIso
    (X : Scheme.{u})
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    (upperStarFromPoint X).mapMod R ⋙
        Mod.extendScalars ((upperStarFromPoint X).map f) ≅
      Mod.extendScalars f ⋙ (upperStarFromPoint X).mapMod S := by
  let F := upperStarFromPoint X
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction (F.map f)) (Mod.extendRestrictAdjunction f)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso _ (F.map f) f
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality f))

private noncomputable def compositionExtensionIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [HasCoequalizers E] [HasEqualizers E] [BraidedCategory E] [MonoidalClosed E]
    [∀ Z : E, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : E, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (τ : F ⋙ G ≅ H) [NatTrans.IsMonoidal τ.hom]
    (R : C) [MonObj R]
    [IsCommMonObj (G.obj (F.obj R))] [IsCommMonObj (H.obj R)]
    (S : E) [MonObj S]
    (f : G.obj (F.obj R) ⟶ S) [IsMonHom f]
    (φ : H.obj R ⟶ S) [IsMonHom φ]
    (he : inv (Functor.compAlgHom F G τ.hom R) ≫ f = φ) :
    H.mapMod R ⋙ Mod.extendScalars φ ≅
      (F.mapMod R ⋙ G.mapMod (F.obj R)) ⋙ Mod.extendScalars f := by
  let α := Functor.compAlgHom F G τ.hom R
  let i : Mod.comap α ≅ Mod.extendScalars (inv α) :=
    (Mod.comapCongr (IsIso.inv_inv (f := α))).symm ≪≫
      (Mod.extendScalarsIsoComapInv (inv α)).symm
  let j : Mod.comap α ⋙ Mod.extendScalars f ≅ Mod.extendScalars φ :=
    Functor.isoWhiskerRight i (Mod.extendScalars f) ≪≫
      (Mod.extendScalarsComp (inv α) f).symm ≪≫ Mod.extendScalarsIsoOfEq he
  exact Functor.isoWhiskerLeft (H.mapMod R) j.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso F G τ.hom R).symm
      (Mod.extendScalars f)

private noncomputable def constantExtensionCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    finiteConstantScalarExtension Λ X ≅
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod (scalarRingObj Λ) ⋙
        Mod.extendScalars (scalarCounit Λ) ⋙ (upperStarFromPoint X).mapMod Λ := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let F := upperStarFromPoint X
  let R := scalarRingObj Λ
  let ε := scalarCounit Λ
  let τ : C ⋙ F ≅ scalarConstant X := Iso.refl _
  have hτ : NatTrans.IsMonoidal τ.hom := by
    constructor
    · simp only [τ, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
      rfl
    · intro A B
      simp only [τ, Iso.refl_hom, NatTrans.id_app, tensorHom_id,
        id_whiskerRight, Category.id_comp, Category.comp_id]
      rfl
  let α := Functor.compAlgHom C F τ.hom R
  have he : inv α ≫ F.map ε = scalarCoefficientHom Λ X := by
    apply (cancel_epi α).mp
    rw [IsIso.hom_inv_id_assoc]
    change F.map ε = 𝟙 _ ≫ scalarCoefficientHom Λ X
    rw [Category.id_comp]
    unfold scalarCoefficientHom
    rfl
  unfold finiteConstantScalarExtension
  exact compositionExtensionIso C F (scalarConstant X) τ R _
      (F.map ε) (scalarCoefficientHom Λ X) he ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (C.mapMod R) (pointExtensionMapIso X _ _ ε) ≪≫
    (Functor.associator _ _ _).symm

section PointAdjunction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k : Type u) [Field k] [IsSepClosed k]

/-- The scalar module sections transported along the geometric-point equivalence.
Source: blueprint local boundary duality, Step 5, sections adjunction
(blueprint: lem-a1-condensed-point-scalar-adjunction). -/
def pointInternalScalarSections :=
  (((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).inverse ⋙
    scalarSections.mapMod Λ

/-- The finite-constant-model scalar extension is left adjoint to point scalar sections.
Source: blueprint local boundary duality, Step 5, scalar extension adjunction.
Proof: factor scalar realization into constant sheaf, extension along the counit,
and the point inverse image. The preceding monoidal scalar adjunction supplies the
first two factors, and the point inverse image is an equivalence. Transport the
composed adjunction through the canonical scalar realization factorization.
(blueprint: lem-a1-condensed-point-scalar-adjunction) -/
theorem finiteConstantPointAdjunction :
    Nonempty (finiteConstantScalarExtension Λ (Spec (.of k)) ⊣
      pointInternalScalarSections Λ k) := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let G := scalarSections.{u}
  let : C.LaxBraided := by
    letI : (Functor.const Profinite.{u}ᵒᵖ :
        Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}).LaxBraided :=
      { braided := by intros; ext; simp [Functor.LaxMonoidal.μ]; rfl }
    exact inferInstanceAs (Functor.const Profinite.{u}ᵒᵖ ⋙
      presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).LaxBraided
  have : IsCommMonObj (C.obj (G.obj Λ)) :=
    Functor.isCommMonObj_obj (F := C) (M := scalarRingObj Λ)
  let a : C ⊣ G := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let E := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  exact ⟨((counitScalarAdjunction a Λ).comp E.toAdjunction).ofNatIsoLeft
    (constantExtensionCompIso Λ (Spec (.of k))).symm⟩


end PointAdjunction

attribute [local irreducible] scalarConstant pointExtensionMapIso constantExtensionCompIso

private theorem scalarExtension_leftExact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit Λ))) (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteConstantScalarExtension Λ X) := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteLimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars (scalarCounit Λ)) := h
  have : PreservesFiniteLimits
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (scalarRingObj Λ)) := inferInstance
  have : PreservesFiniteLimits ((upperStarFromPoint X).mapMod Λ) := inferInstance
  exact preservesFiniteLimits_of_natIso (constantExtensionCompIso Λ X).symm

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_pid_kernel_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (n : ℕ) (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (g : Mod.finiteFree (scalarRingObj Λ) n ⟶ P) :
    Mod.IsFree (scalarRingObj Λ) (kernel g) := by
  classical
  let R := scalarRingObj Λ
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular R) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular R) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans (internalRegularCoordinates K)
  let e (m : ℕ) := ringFreeCoordinates (Mod.regular R) Q b m
  let kg : Q.obj (kernel g) ≅ ModuleCat.of K (LinearMap.ker (Q.map g).hom) :=
    PreservesKernel.iso Q g ≪≫ ModuleCat.kernelIsoKer (Q.map g)
  have : Module.Finite K (Q.obj (Mod.finiteFree R n)) :=
    Module.Finite.of_injective (e n).toLinearMap (e n).injective
  have : Module.Free K (Q.obj (Mod.finiteFree R n)) := Module.Free.of_equiv (e n).symm
  have : Module.Finite K (Q.obj (kernel g)) :=
    Module.Finite.equiv kg.toLinearEquiv.symm
  have : Module.Free K (Q.obj (kernel g)) := Module.Free.of_equiv kg.toLinearEquiv.symm
  let B := Module.Free.chooseBasis K (Q.obj (kernel g))
  let d := Fintype.card (Module.Free.ChooseBasisIndex K (Q.obj (kernel g)))
  let B' := B.reindex (Fintype.equivFin _)
  exact ⟨d, ⟨Q.preimageIso ((B'.equivFun.trans (e d).symm).toModuleIso)⟩⟩

private theorem tor_of_free_shortExact
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    _root_.DerivedCategory.torAmplitudeIn C (-1) 0
      ((_root_.DerivedCategory.singleFunctor C 0).obj S.X₃) := by
  let S' := S.map (HomologicalComplex.single C (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  exact (_root_.DerivedCategory.torAmplitudeIn C (-1) 0).prop_of_iso
    (asIso (_root_.DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
      ((_root_.DerivedCategory.singleFunctorIsoCompQ C 0).app S.X₃).symm)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0 (fun n ↦
      (_root_.DerivedCategory.isDualizable_mappingCone_single_X h₁ h₂ S'.f n).flat))

private theorem scalar_pid_model_tor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (X : Scheme.{u}) [PreservesFiniteLimits (finiteConstantScalarExtension Λ X)]
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P) :
    _root_.DerivedCategory.torAmplitudeIn _ (-1) 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((finiteConstantScalarExtension Λ X).obj P)) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hP
  let g := cokernel.π f ≫ e.inv
  have : Epi g := by dsimp only [g]; infer_instance
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hs : S.ShortExact := ⟨ShortComplex.exact_kernel g⟩
  let F := finiteConstantScalarExtension Λ X
  obtain ⟨a, ⟨ea⟩⟩ := scalar_pid_kernel_free Λ K φ n P g
  have h₁ : IsDualizable (F.obj S.X₁) :=
    (CategoryTheory.isDualizable_biproduct_unit a).of_iso
      (F.mapIso ea ≪≫ scalarFreeIso Λ X a).symm
  have h₂ : IsDualizable (F.obj S.X₂) :=
    (CategoryTheory.isDualizable_biproduct_unit n).of_iso (scalarFreeIso Λ X n).symm
  exact tor_of_free_shortExact (S.map F) (hs.map_of_exact F) h₁ h₂

-- The Type-0 coefficient version of constantToContinuous_preservesFiniteLimits.
-- Its sectionwise proof does not require the scalar carrier to have the site's universe.
private theorem extension_equivalence
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R]
    (f : R ⟶ S) [IsMonHom f] [IsIso f] :
    (Mod.extendScalars f).IsEquivalence := by
  have : (Mod.comap (asIso f).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (asIso f).inv).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv f).symm

end AlgebraicGeometry.ProEtale
