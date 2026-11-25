/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteScalarConstantModels
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundTorsion
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.RegularScalarExtensionMultiplication
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! # The rank-one normalized ordinary quotient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def mapRegular {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    (S : C) [MonObj S] :
    (F.mapMod S).obj (Mod.regular S) ≅ Mod.regular (F.obj S) :=
  Mod.isoMk (Iso.refl _) (by simp)

private lemma mapRegular_lift {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    (S : C) [MonObj S] (t : 𝟙_ C ⟶ S) :
    (F.mapMod S).map (Mod.regularLift (Mod.regular S) t) ≫ (mapRegular F S).hom =
      (mapRegular F S).hom ≫ Mod.regularLift (Mod.regular (F.obj S))
        (Functor.LaxMonoidal.ε F ≫ F.map t) := by
  apply Mod.regular_hom_ext
  change (MonObj.one : 𝟙_ _ ⟶ F.obj S) ≫
      (F.map (Mod.regularLift (Mod.regular S) t).hom ≫ 𝟙 _) =
    (MonObj.one : 𝟙_ _ ⟶ F.obj S) ≫ (𝟙 _ ≫ _)
  simp only [Category.comp_id, Category.id_comp]
  rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
    ← F.map_comp, Mod.one_comp_regularLift]

private lemma extendRegular_lift {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {S B : C} [MonObj S] [MonObj B] [IsCommMonObj S]
    (φ : S ⟶ B) [IsMonHom φ] (t : 𝟙_ C ⟶ S) :
    (Mod.extendScalars φ).map (Mod.regularLift (Mod.regular S) t) ≫
        (Mod.regularExtensionIso φ).hom =
      (Mod.regularExtensionIso φ).hom ≫ Mod.regularLift (Mod.regular B) (t ≫ φ) := by
  apply Mod.regularExtensionIso_naturality
  have h : Mod.regularLift (Mod.regular S) t ≫ Mod.regularCoefficientMap φ =
      Mod.regularCoefficientMap φ ≫ (Mod.comap φ).map
        (Mod.regularLift (Mod.regular B) (t ≫ φ)) := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ C ⟶ S) ≫
        ((Mod.regularLift (Mod.regular S) t).hom ≫ φ) =
      (MonObj.one : 𝟙_ C ⟶ S) ≫
        (φ ≫ (Mod.regularLift (Mod.regular B) (t ≫ φ)).hom)
    rw [← Category.assoc, Mod.one_comp_regularLift, ← Category.assoc,
      IsMonHom.one_hom φ, Mod.one_comp_regularLift]
  exact congrArg Mod.Hom.hom h

private def integralRegular (T : Scheme.{u}) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (FiniteConstantModel.modelFunctor (A l E) T).obj
        (ModuleCat.of (A l E) (ULift.{u + 1} (A l E))) ≅
      Mod.regular (AdicCompletion.ring l E T) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let S := AddCommGrpCat.of (ULift.{u + 1} (A l E))
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let H := (upperStarFromPoint T).mapMod (Profinite.continuousCoefficientRingObj (A l E))
  exact H.mapIso ((Mod.extendScalars (FiniteConstantModel.scalarToContinuous (A l E))).mapIso
      ((F.mapMod S).mapIso (FiniteConstantModel.scalarRegularIso (A l E)) ≪≫
        mapRegular F S) ≪≫ Mod.regularExtensionIso
          (FiniteConstantModel.scalarToContinuous (A l E))) ≪≫
    mapRegular (upperStarFromPoint T) _

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  apply QuotientAddGroup.discreteTopology
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  have hb := (Padic.coefficientExtension_integers_coset_basis l E 0).mem_of_mem
    (i := n) trivial
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _ at hb
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _
  rw [← hti]
  have he : {y : Padic.coefficientExtensionIntegers l E |
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) 0} =
      (Padic.coefficientExtensionIdeal l E (n + 1)).toAddSubgroup := by
    ext y
    change _ = _ ↔ y ∈ Padic.coefficientExtensionIdeal l E (n + 1)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rw [he] at hb
  exact hb

private def quotientRegularEncoded (T : Scheme.{u}) (n : ℕ) (e : Encoding l E n T) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (e.ordinary.trans e.fixed).functor.obj
        (Mod.regular (AdicCompletion.finiteRing l E T n)) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (ModuleCat.of (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have : Finite (R l E n) := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : DiscreteTopology (R l E n) := finiteTopology_discrete l E n
  let B := R l E n
  let S := scalarRingObj (FiniteDiscreteOrdinary.coefficient B)
  exact (e.ordinary.trans e.fixed).functor.mapIso
      (AlgebraicGeometry.ProEtale.scalarRegularIso
        (FiniteDiscreteOrdinary.coefficient B) T).symm ≪≫
    FiniteDiscreteOrdinary.scalarConstantEncodedIso B T e (Mod.regular S) ≪≫
    (constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} B))).mapIso
        (FiniteDiscreteOrdinary.scalarRegularCoordinates B).toModuleIso

private lemma constant_scalar (T : Scheme.{u}) (n : ℕ)
    (P : ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) (b : ULift.{u + 1} (R l E n)) :
    let G := constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
    G.map (ModuleCat.ofHom (LinearMap.lsmul _ P b)) = (torsionFixedScalar (G.obj P) b).asHom := by
  let J := Scheme.ProEt.topology T
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((constantSheaf J _).obj P).property
  change toSheafify J ((Functor.const T.ProEtᵒᵖ).obj P) ≫
      sheafifyMap J ((Functor.const T.ProEtᵒᵖ).map
        (ModuleCat.ofHom (LinearMap.lsmul _ P b))) = _
  rw [← toSheafify_naturality]
  ext V m
  exact ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj P)).app V).hom.map_smul b m

private lemma scalarRegular_lift (x : A l E) :
    (FiniteConstantModel.scalarModules (A l E)).map
        (ModuleCat.ofHom (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) x)) ≫
      (FiniteConstantModel.scalarRegularIso (A l E)).hom =
    (FiniteConstantModel.scalarRegularIso (A l E)).hom ≫
      Mod.regularLift (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} (A l E))))
        (scalarIntegerMap (A l E) x) := by
  apply Mod.hom_ext
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro y
  change ULift.up (x * y.down) = ULift.up (y.down * (1 • x))
  simp [mul_comm]

private lemma point_integral_scalar (x : A l E) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (scalarIntegerMap (A l E) x) ≫ FiniteConstantModel.scalarToContinuous (A l E) =
      MonObj.one ≫ (torsionIntegerMultiply l E x).asHom := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let J := coherentTopology Profinite.{u}
  let U := sheafToPresheaf J Ab.{u + 1}
  let g := scalarIntegerMap (A l E) x
  have hc : Functor.LaxMonoidal.ε (constantSheaf J Ab.{u + 1}) = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  rw [hc, Category.id_comp]
  apply ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).injective
  change (sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _
    ((presheafToSheaf J Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map g) ≫
        FiniteConstantModel.scalarToContinuous (A l E)) = _
  rw [Adjunction.homEquiv_naturality_left]
  dsimp only [FiniteConstantModel.scalarToContinuous]
  rw [Equiv.apply_symm_apply]
  change _ = Functor.LaxMonoidal.ε U ≫ U.map
    (MonObj.one ≫ (torsionIntegerMultiply l E x).asHom)
  rw [U.map_comp, ← Category.assoc]
  erw [Sheaf.ε_sheafToPresheaf_comp_map_one_sheafCompose]
  ext S z
  apply ULift.ext
  apply ContinuousMap.ext
  intro y
  simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply]
  dsimp only [g, scalarIntegerMap, FiniteConstantModel.constantFunctions,
    torsionIntegerMultiply]
  rw [Functor.one_compForget₂_app]
  erw [AddCommGrpCat.ringMonObj_one_apply]
  change z.down • x = x * (z.down : A l E)
  simp [zsmul_eq_mul, mul_comm]

private lemma square_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {p : X ⟶ X} {q : Y ⟶ Y} (i : X ≅ Y)
    (h : p ≫ i.hom = i.hom ≫ q) :
    F.map p ≫ (F.mapIso i).hom = (F.mapIso i).hom ≫ F.map q := by
  simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg F.map h

private lemma square_trans {C : Type*} [Category* C] {X Y Z : C}
    {p : X ⟶ X} {q : Y ⟶ Y} {r : Z ⟶ Z} (i : X ≅ Y) (j : Y ≅ Z)
    (h : p ≫ i.hom = i.hom ≫ q) (h' : q ≫ j.hom = j.hom ≫ r) :
    p ≫ (i ≪≫ j).hom = (i ≪≫ j).hom ≫ r := by
  simp only [Iso.trans_hom, ← Category.assoc]
  rw [h, Category.assoc, h', ← Category.assoc]

private lemma integralRegular_scalar (T : Scheme.{u}) (x : A l E) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    (FiniteConstantModel.modelFunctor (A l E) T).map
        (ModuleCat.ofHom (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) x)) ≫
      (integralRegular l E T).hom =
    (integralRegular l E T).hom ≫ Mod.regularLift
      (Mod.regular (AdicCompletion.ring l E T))
      (MonObj.one ≫ (upperStarFromPoint T).map (torsionIntegerMultiply l E x).asHom) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let S := AddCommGrpCat.of (ULift.{u + 1} (A l E))
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let K := Mod.extendScalars (FiniteConstantModel.scalarToContinuous (A l E))
  let U := upperStarFromPoint T
  let H := U.mapMod (Profinite.continuousCoefficientRingObj (A l E))
  let t := scalarIntegerMap (A l E) x
  let t' := Functor.LaxMonoidal.ε F ≫ F.map t
  let t'' := t' ≫ FiniteConstantModel.scalarToContinuous (A l E)
  have h₀ := square_map (F.mapMod S) (FiniteConstantModel.scalarRegularIso (A l E))
    (scalarRegular_lift l E x)
  have h₁ := square_trans _ _ h₀ (mapRegular_lift F S t)
  have h₂ := square_trans _ _ (square_map K _ h₁)
    (extendRegular_lift (FiniteConstantModel.scalarToContinuous (A l E)) t')
  have h₃ := square_trans _ _ (square_map H _ h₂)
    (mapRegular_lift U (Profinite.continuousCoefficientRingObj (A l E)) t'')
  have ht : Functor.LaxMonoidal.ε U ≫ U.map t'' =
      MonObj.one ≫ U.map (torsionIntegerMultiply l E x).asHom := by
    dsimp only [t'', t', t, F]
    rw [Category.assoc, point_integral_scalar l E x, U.map_comp, ← Category.assoc]
    rfl
  rw [ht] at h₃
  exact h₃

private lemma encoded_regular_scalar (T : Scheme.{u}) (n : ℕ)
    (e : Encoding l E n T) (x : A l E) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let H := (e.ordinary.trans e.fixed).functor
    H.map (Mod.regularLift (Mod.regular (AdicCompletion.finiteRing l E T n))
        ((MonObj.one ≫ (upperStarFromPoint T).map (torsionIntegerMultiply l E x).asHom) ≫
          AdicCompletion.quotient l E T n)) =
      (torsionFixedScalar (H.obj (Mod.regular (AdicCompletion.finiteRing l E T n)))
        (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x))).asHom := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let M := Mod.regular (AdicCompletion.finiteRing l E T n)
  let p := Mod.regularLift M
    ((MonObj.one ≫ (upperStarFromPoint T).map (torsionIntegerMultiply l E x).asHom) ≫
      AdicCompletion.quotient l E T n)
  let b : ULift.{u + 1} (R l E n) :=
    ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x)
  have aux : ∀ H : FiniteDiscreteOrdinary.Internal (R l E n) T ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))),
      H = (FiniteDiscreteOrdinary.sectionEncoding (R l E n) T e.ringIso ⋙
        FiniteDiscreteOrdinary.fixedRestriction (R l E n) T) →
      H.map p = (torsionFixedScalar (H.obj M) b).asHom := by
    intro H hH
    subst H
    apply (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) Ab.{u + 1})).map_injective
    change p.hom = _
    dsimp only [p]
    rw [regularLift_eq]
    have h := scalar_encoded l E T (n + 1) e M x
    dsimp only [torsionScalar, Mod.act_comap_obj] at h
    change ((λ_ (AdicCompletion.finiteRing l E T n)).inv ≫
      (MonObj.one ≫ (upperStarFromPoint T).map (torsionIntegerMultiply l E x).asHom) ▷
        AdicCompletion.finiteRing l E T n ≫
      (AdicCompletion.quotient l E T n) ▷ AdicCompletion.finiteRing l E T n ≫
        MonObj.mul) = _ at h
    simpa only [torsionScalar, Mod.act_comap_obj, MonoidalCategory.comp_whiskerRight,
      Category.assoc] using h
  apply aux
  change e.ordinary.functor ⋙ e.fixed.functor = _
  rw [e.ordinary_functor, e.fixed_functor]

/-- The quotient of the integral regular model, with its scalar endomorphisms, in the
specified normalized coordinates.

Source: blueprint latest, integral ctf-equals-bc, Local models; Stacks 03EK, 093M.
(blueprint: lem-sfb-finite-model-ordinary-scalar).

Proof: the scalar regular module is the internal regular module on the lifted ring.
The constant-sheaf and inverse-image monoidal functors preserve regular modules.
Apply regularExtensionIso first to scalarToContinuous and then to the actual quotient.
The resulting object is the quotient regular module. The normalized ring isomorphism
in e identifies its section action with the ordinary constant ring action; restriction
to constant scalars gives the constant regular module. Naturality of regularExtensionIso
identifies multiplication by x with multiplication by its actual quotient. Normalization
identifies that residue with the same constant scalar section, proving the equation.
-/
theorem ordinary_scalar (T : Scheme.{u}) (n : ℕ) (e : Encoding l E n T) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let F := FiniteConstantModel.modelFunctor (A l E) T ⋙
      Mod.extendScalars (AdicCompletion.quotient l E T n) ⋙
      (e.ordinary.trans e.fixed).functor
    let G := constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
    ∃ i : F.obj (ModuleCat.of (A l E) (ULift.{u + 1} (A l E))) ≅
        G.obj (ModuleCat.of (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n))),
      ∀ x : A l E,
        F.map (ModuleCat.ofHom (LinearMap.lsmul (A l E) (ULift.{u + 1} (A l E)) x)) ≫
            i.hom =
          i.hom ≫ G.map (ModuleCat.ofHom
            (LinearMap.lsmul (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n))
              (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
                x)))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let H := (e.ordinary.trans e.fixed).functor
  let Q := Mod.extendScalars (AdicCompletion.quotient l E T n)
  let j := Q.mapIso (integralRegular l E T) ≪≫
    Mod.regularExtensionIso (AdicCompletion.quotient l E T n)
  let k := quotientRegularEncoded l E T n e
  refine ⟨H.mapIso j ≪≫ k, fun x ↦ ?_⟩
  have hj := square_trans _ _
    (square_map Q (integralRegular l E T) (integralRegular_scalar l E T x))
    (extendRegular_lift (AdicCompletion.quotient l E T n)
      (MonObj.one ≫ (upperStarFromPoint T).map (torsionIntegerMultiply l E x).asHom))
  have hh := square_map H j hj
  rw [encoded_regular_scalar l E T n e x] at hh
  apply square_trans _ _ hh
  rw [constant_scalar l E T n
    (ModuleCat.of (ULift.{u + 1} (R l E n)) (ULift.{u + 1} (R l E n)))
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x))]
  ext V m
  exact (k.hom.hom.app V).hom.map_smul _ _

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
