/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNative
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Evaluation-normalized closedness of the ringed-site derived tensor

Source: Stacks Project, Tag 08J9, with Tags 0A90 and 0A8Z.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w a b
open CategoryTheory WeilConjectures
namespace CategoryTheory.RingedDerivedNative

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

open CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.ZeroClassAux

-- Keep this cache transparent: opaque proofs leave the coefficient universe unresolved.
set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose [EssentiallySmall.{a} C] :
    J.HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a}) := by
  exact (equivSmallModel.{a} C).hasSheafCompose J
    ((equivSmallModel.{a} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{a} RingCat.{a})

attribute [local instance 1000001] cachedCompose

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local irreducible] tensorHomEquiv homComplexFunctor
  SheafOfModules.monoidalCategory

section GenericChains

variable {D : Type a} [Category.{b} D] [Preadditive D] [HasZeroObject D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
  [SymmetricCategory D] [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
  [∀ (X Y : GradedObject ℤ D), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

private noncomputable def chainEquivalenceGeneric
    (P L M K : CochainComplex D ℤ) (e : K ≅ CochainComplex.internalHomObj L M) :
    (P ⊗ L ⟶ M) ≃ (P ⟶ K) :=
  (β_ P L).homFromEquiv.trans
    ((CochainComplex.internalHomEquiv L M P).trans e.symm.homToEquiv)

set_option linter.unusedSectionVars false in
private theorem chainEquivalenceGeneric_symm_component
    (P L M K : CochainComplex D ℤ) (e : K ≅ CochainComplex.internalHomObj L M)
    (π : ∀ (n p q : ℤ), p + n = q → (K.X n ⟶ (ihom (L.X p)).obj (M.X q)))
    (he : ∀ (n p q : ℤ) (h : p + n = q),
      e.hom.f n ≫ CochainComplex.internalHomπ L M n p q h =
        (p * n).negOnePow • π n p q h)
    (φ : P ⟶ K) (p q k : ℤ) (h : p + q = k) :
    HomologicalComplex.ιTensorObj P L p q k h ≫
        ((chainEquivalenceGeneric P L M K e).symm φ).f k =
      (β_ (P.X p) (L.X q)).hom ≫
        MonoidalClosed.uncurry (φ.f p ≫ π p q k (by omega)) := by
  change _ ≫ ((β_ P L).hom ≫
    (CochainComplex.internalHomEquiv L M P).symm (φ ≫ e.hom)).f k = _
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  change (HomologicalComplex.ιTensorObj P L p q k h ≫
    (CochainComplex.Monoidal.braiding P L).hom.f k) ≫ _ = _
  rw [CochainComplex.Monoidal.ι_braiding_hom, Preadditive.zsmul_comp, Category.assoc,
    CochainComplex.ιTensorObj_internalHomEquiv_symm_f]
  rw [HomologicalComplex.comp_f, Category.assoc, he,
    Linear.comp_units_smul, MonoidalClosed.uncurry_units_smul,
    Linear.comp_units_smul, mul_comm q p]
  simp only [Units.smul_def, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
    one_smul]

set_option linter.unusedSectionVars false in
private theorem tensorMap_naturality
    (P P' L L' M M' : CochainComplex D ℤ)
    (f : P' ⟶ P) (g : L' ⟶ L) (h : M ⟶ M')
    (ψ' : P' ⊗ L' ⟶ M') (ψ : P ⊗ L ⟶ M)
    (hψ : ∀ (p q k : ℤ) (hpq : p + q = k),
      HomologicalComplex.ιTensorObj P' L' p q k hpq ≫ ψ'.f k =
        (f.f p ⊗ₘ g.f q) ≫
          HomologicalComplex.ιTensorObj P L p q k hpq ≫ ψ.f k ≫ h.f k) :
    ψ' = (f ⊗ₘ g) ≫ ψ ≫ h := by
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  change HomologicalComplex.ιTensorObj P' L' p q k hpq ≫ _ = _
  simp only [HomologicalComplex.comp_f]
  have ht := HomologicalComplex.ι_mapBifunctorMap f g
    (curriedTensor D) (.up ℤ) p q k hpq
  change HomologicalComplex.ιTensorObj P' L' p q k hpq ≫ (f ⊗ₘ g).f k =
    (f.f p ▷ L'.X q) ≫ (P.X p ◁ g.f q) ≫
      HomologicalComplex.ιTensorObj P L p q k hpq at ht
  rw [← Category.assoc, ← tensorHom_def] at ht
  rw [← Category.assoc (HomologicalComplex.ιTensorObj _ _ _ _ _ _) _, ht]
  simpa only [Category.assoc] using hψ p q k hpq

end GenericChains

namespace GenericHomotopy

variable {D : Type a} [Category.{b} D] [Preadditive D] [HasZeroObject D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
  [SymmetricCategory D] [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
  [∀ (X Y : GradedObject ℤ D), X.HasTensor Y]
  [∀ (W X Y Z : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

private noncomputable def homotopyEquivGeneric
    (P L M K : CochainComplex D ℤ)
    (e : K ≅ CochainComplex.internalHomObj L M) :
    ((HomotopyCategory.quotient _ _).obj (P ⊗ L) ⟶
        (HomotopyCategory.quotient _ _).obj M) ≃
      ((HomotopyCategory.quotient _ _).obj P ⟶
        (HomotopyCategory.quotient _ _).obj (K)) :=
  ((HomotopyCategory.quotient _ _).mapIso (β_ P L)).homFromEquiv.trans
    (((HomotopyCategory.tensorHomAdjunction
        ((HomotopyCategory.quotient _ _).obj L)).homEquiv
          ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj M)).trans
      ((HomotopyCategory.quotient _ _).mapIso (e)).symm.homToEquiv)

set_option linter.unusedSectionVars false in
private theorem homotopyEquivGeneric_map
    (P L M K : CochainComplex D ℤ)
    (e : K ≅ CochainComplex.internalHomObj L M) (ψ : P ⊗ L ⟶ M) :
    homotopyEquivGeneric P L M K e ((HomotopyCategory.quotient _ _).map ψ) =
      (HomotopyCategory.quotient _ _).map (chainEquivalenceGeneric P L M K e ψ) := by
  let q := HomotopyCategory.quotient (D) (.up ℤ)
  have hc (g : L ⊗ P ⟶ M) :
      (HomotopyCategory.tensorHomAdjunction (q.obj L)).homEquiv (q.obj P) (q.obj M)
          (q.map g) = q.map (CochainComplex.internalHomEquiv L M P g) := by
    rw [Adjunction.homEquiv_unit, HomotopyCategory.tensorHomAdjunction_unit_app]
    change q.map ((CochainComplex.tensorHomAdjunction L).unit.app P) ≫
      q.map ((CochainComplex.internalHom L).map g) = _
    rw [← q.map_comp, ← CochainComplex.tensorHomAdjunction_homEquiv]
    rfl
  change ((HomotopyCategory.tensorHomAdjunction (q.obj L)).homEquiv (q.obj P) (q.obj M)
    (q.map (β_ P L).inv ≫ q.map ψ)) ≫ q.map (e).inv = _
  rw [← q.map_comp, hc, ← q.map_comp]
  unfold chainEquivalenceGeneric
  rfl

private theorem homotopyEquivGeneric_symm_map
    (P L M K : CochainComplex D ℤ)
    (e : K ≅ CochainComplex.internalHomObj L M)
    (φ : P ⟶ K) :
    (homotopyEquivGeneric P L M K e).symm ((HomotopyCategory.quotient _ _).map φ) =
      (HomotopyCategory.quotient _ _).map ((chainEquivalenceGeneric P L M K e).symm φ) := by
  apply (homotopyEquivGeneric P L M K e).injective
  rw [Equiv.apply_symm_apply, homotopyEquivGeneric_map, Equiv.apply_symm_apply]

end GenericHomotopy

namespace GenericDerived

variable {D : Type a} [Category.{b} D] [Abelian D] [HasDerivedCategory.{w} D]

private noncomputable def qHomMap
    (P I : CochainComplex D ℤ)
    (f : (HomotopyCategory.quotient _ _).obj P ⟶ (HomotopyCategory.quotient _ _).obj I) :
    DerivedCategory.Q.{w}.obj P ⟶ DerivedCategory.Q.obj I :=
  (DerivedCategory.quotientCompQhIso (D)).inv.app P ≫
    DerivedCategory.Qh.map f ≫
      (DerivedCategory.quotientCompQhIso (D)).hom.app I

private theorem qHomMap_map (P I : CochainComplex D ℤ) (f : P ⟶ I) :
    qHomMap P I ((HomotopyCategory.quotient _ _).map f) =
      DerivedCategory.Q.map f := by
  unfold qHomMap
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

private noncomputable def qHomEquiv
    (P I : CochainComplex D ℤ) [I.IsKInjective] :
    ((HomotopyCategory.quotient _ _).obj P ⟶ (HomotopyCategory.quotient _ _).obj I) ≃
      (DerivedCategory.Q.{w}.obj P ⟶ DerivedCategory.Q.obj I) :=
  (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective _ I)).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso _).app P)
      ((DerivedCategory.quotientCompQhIso _).app I))

private theorem qHomEquiv_map
    (P I : CochainComplex D ℤ) [I.IsKInjective] (f : P ⟶ I) :
    qHomEquiv P I ((HomotopyCategory.quotient _ _).map f) =
      DerivedCategory.Q.map f := qHomMap_map P I f

end GenericDerived

namespace GenericNaturality

variable {D : Type a} [Category.{b} D]

private theorem uncurry_naturality_of_comparison
    {A A' X X' B B' Y Y' : D}
    (c : A ≅ X) (c' : A' ≅ X') (t : A' ⟶ A) (td : X' ⟶ X)
    (u : A ⟶ B) (u' : A' ⟶ B') (r : B ⟶ Y) (r' : B' ⟶ Y')
    (b : B ⟶ B') (h : Y ⟶ Y') (v : X ⟶ Y) (v' : X' ⟶ Y')
    (hc : c'.hom ≫ td = t ≫ c.hom)
    (hu : u' = t ≫ u ≫ b) (hr : b ≫ r' = r ≫ h)
    (hv : c.hom ≫ v = u ≫ r) (hv' : c'.hom ≫ v' = u' ≫ r') :
    v' = td ≫ v ≫ h := by
  apply (cancel_epi c'.hom).1
  rw [hv', hu]
  simp only [Category.assoc]
  rw [hr, ← Category.assoc c'.hom td, hc]
  simp only [Category.assoc]
  simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ k ≫ h) hv.symm

end GenericNaturality

namespace GenericClosed

variable {D : Type a} [Category.{b} D] [MonoidalCategory D]
private noncomputable def tensorHoms :
    (D)ᵒᵖ ×
      ((D)ᵒᵖ × D) ⥤
        Type b where
  obj X := (X.1.unop ⊗ X.2.1.unop ⟶ X.2.2)
  map f := ↾fun ψ ↦ (f.1.unop ⊗ₘ f.2.1.unop) ≫ ψ ≫ f.2.2
  map_id X := by
    ext ψ
    simp
  map_comp f g := by
    ext ψ
    change ((g.1.unop ≫ f.1.unop) ⊗ₘ (g.2.1.unop ≫ f.2.1.unop)) ≫ ψ ≫
      (f.2.2 ≫ g.2.2) =
        (g.1.unop ⊗ₘ g.2.1.unop) ≫
          ((f.1.unop ⊗ₘ f.2.1.unop) ≫ ψ ≫ f.2.2) ≫ g.2.2
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]

variable (H : Dᵒᵖ × D ⥤ D)

private noncomputable def homHoms :
    (D)ᵒᵖ ×
      ((D)ᵒᵖ × D) ⥤
        Type b where
  obj X := (X.1.unop ⟶ (H).obj
    (X.2.1, X.2.2))
  map f := ↾fun φ ↦ f.1.unop ≫ φ ≫
    (H).map (f.2.1, f.2.2)
  map_id X := by
    ext φ
    change (𝟙 _ ≫ φ ≫ (H).map (𝟙 _)) = φ
    erw [Functor.map_id]
    simp only [Category.id_comp, Category.comp_id]
  map_comp f g := by
    ext φ
    change (g.1.unop ≫ f.1.unop) ≫ φ ≫
      (H).map
        ((f.2.1, f.2.2) ≫ (g.2.1, g.2.2)) =
      g.1.unop ≫ (f.1.unop ≫ φ ≫
        (H).map (f.2.1, f.2.2)) ≫
          (H).map (g.2.1, g.2.2)
    rw [Functor.map_comp]
    simp only [Category.assoc]

private noncomputable def derivedEquiv (e : homHoms H ≅ tensorHoms (D := D))
    (P L M : D) :
    (P ⊗ L ⟶ M) ≃ (P ⟶ (H).obj (op L, M)) :=
  (e.app (op P, (op L, M))).toEquiv.symm

private theorem derivedEquiv_symm_naturality (e : homHoms H ≅ tensorHoms (D := D))
    (P P' L L' M M' : D)
    (f : P' ⟶ P) (g : L' ⟶ L) (h : M ⟶ M')
    (φ : P ⟶ (H).obj (op L, M)) :
    (derivedEquiv H e P' L' M').symm
        (f ≫ φ ≫ (H).map (g.op, h)) =
      (f ⊗ₘ g) ≫ (derivedEquiv H e P L M).symm φ ≫ h := by
  exact congrArg (fun k ↦ k φ)
    (e.hom.naturality
      (X := (op P, (op L, M))) (Y := (op P', (op L', M')))
        (Prod.mkHom f.op (Prod.mkHom g.op h)))

private noncomputable def derivedAdjunction (e : homHoms H ≅ tensorHoms (D := D))
    (L : D) :
    tensorRight L ⊣ Prod.sectR (op L) _ ⋙ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P M ↦ derivedEquiv H e P L M
      homEquiv_naturality_left_symm := fun {P' P M} f φ ↦ by
        change (derivedEquiv H e P' L M).symm (f ≫ φ) =
          (f ▷ L) ≫ (derivedEquiv H e P L M).symm φ
        simpa only [op_id, ← prod_id', Functor.map_id, Category.comp_id,
          tensorHom_id, whiskerRight_id, Category.comp_id] using
            derivedEquiv_symm_naturality H e P P' L L M M f (𝟙 L) (𝟙 M) φ
      homEquiv_naturality_right := fun {P} {M M'} ψ h ↦ by
        apply (derivedEquiv H e P L M').symm.injective
        have hn := derivedEquiv_symm_naturality H e P P L L M M'
          (𝟙 P) (𝟙 L) h (derivedEquiv H e P L M ψ)
        change (derivedEquiv H e P L M').symm
            (derivedEquiv H e P L M' (ψ ≫ h)) =
          (derivedEquiv H e P L M').symm
            (derivedEquiv H e P L M ψ ≫ H.map (𝟙 (op L), h))
        rw [Equiv.symm_apply_apply]
        simpa only [op_id, id_tensorHom_id, Category.id_comp, Equiv.symm_apply_apply]
          using hn.symm }

private noncomputable def closedStructure (e : homHoms H ≅ tensorHoms (D := D)) :
    CoefficientClosedStructure (H) where
  monoidal := inferInstance
  adjunction := derivedAdjunction H e
  evaluation_naturality := by
    intro L L' M g
    let H := H
    have h₁ := derivedEquiv_symm_naturality H e
      (H.obj (op L', M)) (H.obj (op L, M)) L' L' M M
      (H.map (X := (op L, M)) (Y := (op L', M)) (g.op, 𝟙 M)) (𝟙 L') (𝟙 M) (𝟙 _)
    have h₂ := derivedEquiv_symm_naturality H e
      (H.obj (op L, M)) (H.obj (op L, M)) L L' M M
      (𝟙 _) g (𝟙 M) (𝟙 _)
    change (H.map (X := (op L, M)) (Y := (op L', M)) (g.op, 𝟙 M) ▷ L') ≫ _ =
      (H.obj (op L, M) ◁ g) ≫ _
    change (H.map (X := (op L, M)) (Y := (op L', M)) (g.op, 𝟙 M) ▷ L') ≫
        (derivedEquiv H e (H.obj (op L', M)) L' M).symm (𝟙 _) =
      (H.obj (op L, M) ◁ g) ≫
        (derivedEquiv H e (H.obj (op L, M)) L M).symm (𝟙 _)
    simp only [H, op_id, ← prod_id', Functor.map_id, Category.id_comp, Category.comp_id,
      tensorHom_id, id_tensorHom] at h₁ h₂
    exact h₁.symm.trans h₂

private theorem closedStructure_transpose (e : homHoms H ≅ tensorHoms (D := D))
    (P L M : D) :
    (closedStructure H e).transpose P L M = derivedEquiv H e P L M := by
  change (derivedAdjunction H e L).homEquiv P M = _
  rw [derivedAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

private noncomputable def localizedHomIso
    {A : Type c} [Category.{v} A] (L : A ⥤ Dᵒᵖ × (Dᵒᵖ × D))
    (V : MorphismProperty A) [L.IsLocalization V]
    (e : L ⋙ homHoms H ≅ L ⋙ tensorHoms (D := D)) :
    homHoms H ≅ tensorHoms (D := D) :=
  (Localization.fullyFaithfulWhiskeringLeft L V (Type b)).preimageIso e

private theorem localizedHomIso_restrict
    {A : Type c} [Category.{v} A] (L : A ⥤ Dᵒᵖ × (Dᵒᵖ × D))
    (V : MorphismProperty A) [L.IsLocalization V]
    (e : L ⋙ homHoms H ≅ L ⋙ tensorHoms (D := D)) :
    Functor.isoWhiskerLeft L (localizedHomIso H L V e) = e := by
  apply Iso.ext
  exact (Localization.fullyFaithfulWhiskeringLeft L V (Type b)).map_preimage _

private noncomputable def localizedClosed
    {A : Type c} [Category.{v} A] (L : A ⥤ Dᵒᵖ × (Dᵒᵖ × D))
    (V : MorphismProperty A) [L.IsLocalization V]
    (e : L ⋙ homHoms H ≅ L ⋙ tensorHoms (D := D)) :
    CoefficientClosedStructure H :=
  closedStructure H (localizedHomIso H L V e)

private theorem localizedClosed_transpose_symm
    {A : Type c} [Category.{v} A] (L : A ⥤ Dᵒᵖ × (Dᵒᵖ × D))
    (V : MorphismProperty A) [L.IsLocalization V]
    (e : L ⋙ homHoms H ≅ L ⋙ tensorHoms (D := D)) (X : A)
    (ξ : (L ⋙ homHoms H).obj X) :
    ((localizedClosed H L V e).transpose (L.obj X).1.unop
      (L.obj X).2.1.unop (L.obj X).2.2).symm ξ = (e.hom.app X) ξ := by
  change ((closedStructure H (localizedHomIso H L V e)).transpose
    (L.obj X).1.unop (L.obj X).2.1.unop (L.obj X).2.2).symm ξ = _
  rw [closedStructure_transpose]
  exact congrArg (fun k ↦ k ξ)
    (congrArg (fun i ↦ i.hom.app X) (localizedHomIso_restrict H L V e))

end GenericClosed

section SheafificationBraiding

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private abbrev OrdinaryModules := Modules.{c, v, u} J R

section OrdinaryCurry

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric

private theorem ordinaryUncurry_naturality (A A' T T' N N' : OrdinaryModules.{c, v, u} J R)
    (f : T' ⟶ T) (g : A' ⟶ A) (h : N ⟶ N')
    (φ : T ⟶ SheafOfModules.homObj (R := R) A N) :
    (tensorHomEquiv.{u, c, v} R A' T' N').symm
        (f ≫ φ ≫ SheafOfModules.homObjMap (R := R) g h) =
      (g ⊗ₘ f) ≫ (tensorHomEquiv.{u, c, v} R A T N).symm φ ≫ h := by
  let ψ := (tensorHomEquiv.{u, c, v} R A T N).symm φ
  have hc : tensorHomEquiv.{u, c, v} R A' T' N' (((g ⊗ₘ f) ≫ ψ) ≫ h) =
      f ≫ φ ≫ SheafOfModules.homObjMap (R := R) g h := by
    erw [tensorHomEquiv_right.{u, c, v} R A' ((g ⊗ₘ f) ≫ ψ) h]
    rw [tensorHom_def, Category.assoc]
    erw [tensorHomEquiv_pre.{u, c, v} R g ((A ◁ f) ≫ ψ),
      tensorHomEquiv_left.{u, c, v} R A f ψ, Equiv.apply_symm_apply]
    simp only [Category.assoc]
    erw [SheafOfModules.homObjMap_comp_homObjMap (R := R) g (𝟙 A') (𝟙 N) h]
    simp only [Category.id_comp]
  apply (tensorHomEquiv.{u, c, v} R A' T' N').injective
  erw [Equiv.apply_symm_apply]
  simpa only [Category.assoc, ψ] using hc.symm

end OrdinaryCurry

private theorem pure_braiding (A B : OrdinaryModules.{c, v, u} J R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (β_ A B).hom.val.app U
        (SheafOfModules.CochainScalarConstruction.pure R A B U x y) =
      SheafOfModules.CochainScalarConstruction.pure R B A U y x := by
  exact CategoryTheory.CochainPullback.moduleTmul_braiding A B U x y

open SheafOfModules.CochainScalarConstruction in
private theorem uncurry_pure (A T N : OrdinaryModules.{c, v, u} J R)
    (φ : T ⟶ SheafOfModules.homObj (R := R) A N) (U : Cᵒᵖ)
    (x : T.val.obj U) (y : A.val.obj U) :
    ((tensorHomEquiv.{u, c, v} R A T N).symm φ).val.app U
        (SheafOfModules.CochainScalarConstruction.pure R A T U y x) =
      (((φ.val.app U x).app (op (Over.mk (𝟙 U.unop)))) y) := by
  let ψ := (tensorHomEquiv.{u, c, v} R A T N).symm φ
  have he := tensorHomEquiv_val.{u, c, v} R A T N ψ
  have hi := (tensorHomEquiv.{u, c, v} R A T N).apply_symm_apply φ
  rw [hi] at he
  have he' := congrArg (fun k ↦ (k.app U x).app (op (Over.mk (𝟙 U.unop))) y) he
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v u}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)
  change (((φ.val.app U x).app (op (Over.mk (𝟙 U.unop)))) y) =
    (adj.homEquiv _ N ((SheafOfModules.tensorObjIsoSheafification (R := R) A T).inv ≫ ψ)).app
      U (y ⊗ₜ[R.obj.obj U] T.val.map (𝟙 U) x) at he'
  rw [PresheafOfModules.map_id] at he'
  rw [Adjunction.homEquiv_unit] at he'
  exact he'.symm

end SheafificationBraiding

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric

@[instance_reducible]
private noncomputable def baseClosed : MonoidalClosed (Modules.{c, v, u} J R) :=
  moduleMonoidalClosed.{u, c, v} R

attribute [local instance 1000] baseClosed

private theorem nativeUncurry_eq
    (A T N : Modules.{c, v, u} J R) (g : T ⟶ SheafOfModules.homObj (R := R) A N) :
    MonoidalClosed.uncurry g = (tensorHomEquiv.{u, c, v} R A T N).symm g := by
  change ((tensorHomAdjunction.{u, c, v} R A).homEquiv T N).symm g = _
  erw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

set_option linter.unusedSectionVars false in
private theorem baseLimits : HasLimitsOfSize.{0, 0} (Modules.{c, v, u} J R) :=
  hasLimitsOfSizeShrink.{0, 0, max c v u, max c v u} (Modules.{c, v, u} J R)
attribute [local instance 1000] baseLimits

private theorem baseColimits : HasColimitsOfSize.{0, 0} (Modules.{c, v, u} J R) :=
  hasColimitsOfSizeShrink.{0, 0, max c v u, max c v u} (Modules.{c, v, u} J R)

attribute [local instance 1000] baseColimits

private theorem gradedTensor :
    ∀ (X Y : GradedObject ℤ (Modules.{c, v, u} J R)), X.HasTensor Y :=
  fun _ _ ↦ inferInstance
attribute [local instance 1000] gradedTensor

private theorem gradedTensorFour :
    ∀ (W X Y Z : GradedObject ℤ (Modules.{c, v, u} J R)),
      GradedObject.HasTensor₄ObjExt W X Y Z := fun _ _ _ _ ↦ inferInstance
attribute [local instance 1000] gradedTensorFour

private theorem gradedTensorLeft :
    ∀ (X Y Z : GradedObject ℤ (Modules.{c, v, u} J R)),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := fun _ _ _ ↦ inferInstance
attribute [local instance 1000] gradedTensorLeft

private theorem gradedTensorRight :
    ∀ (X Y Z : GradedObject ℤ (Modules.{c, v, u} J R)),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := fun _ _ _ ↦ inferInstance

attribute [local instance 1000] gradedTensorRight

private noncomputable def homIso (L M : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    homComplex.{c, v, max c v u, max c v u} (R := R) L M ≅
      CochainComplex.internalHomObj (C := Modules.{c, v, u} J R) L M :=
  homComplexIsoInternalHomObj.{u, c, v} L M

private theorem homIso_component
    (L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homIso.{c, v, u} J R L M).hom.f n ≫
        CochainComplex.internalHomπ L M n p q h =
      (p * n).negOnePow • homComplexπ L M n p q h := by
  exact SignedHomComparison.homComplexToInternalHomObjX_π
    (D := Modules.{c, v, u} J R) _ _ _ _ _ _ _ _

attribute [local irreducible] homIso

private noncomputable def chainEquiv (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    ((coefficientTotalTensor.{u, c, v} J R).obj (P, L) ⟶ M) ≃ (P ⟶ homComplex (R := R) L M) :=
  chainEquivalenceGeneric P L M _ (homIso.{c, v, u} J R L M)

private theorem chainEquiv_symm_f
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (φ : P ⟶ homComplex (R := R) L M) (p q k : ℤ) (h : p + q = k) :
    HomologicalComplex.ιTensorObj P L p q k h ≫ ((chainEquiv.{c, v, u} J R P L M).symm φ).f k =
      (β_ (P.X p) (L.X q)).hom ≫
        (tensorHomEquiv.{u, c, v} R (L.X q) (P.X p) (M.X k)).symm
          (φ.f p ≫ homComplexπ L M p q k (by omega)) := by
  have he := chainEquivalenceGeneric_symm_component P L M
    (homComplex (R := R) L M) (homIso.{c, v, u} J R L M)
    (fun n p q h ↦ homComplexπ L M n p q h)
    (homIso_component.{c, v, u} J R L M) φ p q k h
  simp only [chainEquiv, nativeUncurry_eq.{c, v, u} J R] at he ⊢
  exact he

attribute [local irreducible] chainEquiv

private theorem totalTensor_map_eq
    (P P' L L' : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (f : P' ⟶ P) (g : L' ⟶ L) :
    (coefficientTotalTensor.{u, c, v} J R).map
        (X := (P', L')) (Y := (P, L)) (f, g) = f ⊗ₘ g := by
  change (f ▷ L' ≫ P ◁ g) = f ⊗ₘ g
  exact (tensorHom_def f g).symm

set_option backward.isDefEq.respectTransparency true in
private theorem chainEquiv_symm_naturality
    (P P' L L' M M' : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (f : P' ⟶ P) (g : L' ⟶ L) (h : M ⟶ M') (φ : P ⟶ homComplex (R := R) L M) :
    (chainEquiv.{c, v, u} J R P' L' M').symm
        (f ≫ φ ≫ ((homComplexFunctor (R := R)).map g.op).app M ≫
          ((homComplexFunctor (R := R)).obj (op L')).map h) =
      (coefficientTotalTensor.{u, c, v} J R).map (X := (P', L')) (Y := (P, L)) (f, g) ≫
        (chainEquiv.{c, v, u} J R P L M).symm φ ≫ h := by
  rw [totalTensor_map_eq]
  apply tensorMap_naturality P P' L L' M M' f g h
  intro p q k hpq
  rw [chainEquiv_symm_f.{c, v, u} J R]
  erw [reassoc_of% chainEquiv_symm_f.{c, v, u} J R P L M φ p q k hpq]
  erw [reassoc_of% BraidedCategory.braiding_naturality (f.f p) (g.f q)]
  apply (cancel_epi (β_ (P'.X p) (L'.X q)).hom).2
  have hc := homComplexFunctor_map_f_π g h p q k (by omega)
  simp only [HomologicalComplex.comp_f] at hc
  have hf := congrArg (fun a ↦ f.f p ≫ φ.f p ≫ a) hc
  simp only [Category.assoc] at hf
  erw [hf]
  exact ordinaryUncurry_naturality.{c, v, u} J R _ _ _ _ _ _ (f.f p) (g.f q) (h.f k)
    (φ.f p ≫ homComplexπ L M p q k (by omega))

private noncomputable def homotopyEquiv
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    ((HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, L)) ⟶
        (HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).obj M) ≃
      ((HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).obj P ⟶
        (HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).obj
          (homComplex (R := R) L M)) :=
  GenericHomotopy.homotopyEquivGeneric P L M _ (homIso.{c, v, u} J R L M)

private theorem homotopyEquiv_symm_map
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (φ : P ⟶ homComplex (R := R) L M) :
    (homotopyEquiv.{c, v, u} J R P L M).symm
        ((HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).map φ) =
      (HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).map
        ((chainEquiv.{c, v, u} J R P L M).symm φ) := by
  have he := GenericHomotopy.homotopyEquivGeneric_symm_map
    P L M _ (homIso.{c, v, u} J R L M) φ
  simp only [homotopyEquiv, chainEquiv] at he ⊢
  exact he

attribute [local irreducible] homotopyEquiv

variable [HasDerivedCategory.{w} (Modules.{c, v, u} J R)]

private noncomputable def qHomEquiv
    (P I : CochainComplex (Modules.{c, v, u} J R) ℤ) [I.IsKInjective] :
    ((HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).obj P ⟶
        (HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).obj I) ≃
      (DerivedCategory.Q.{w}.obj P ⟶ DerivedCategory.Q.obj I) :=
  GenericDerived.qHomEquiv P I

private theorem qHomEquiv_map
    (P I : CochainComplex (Modules.{c, v, u} J R) ℤ) [I.IsKInjective] (f : P ⟶ I) :
    qHomEquiv.{c, v, u, w} J R P I
        ((HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).map f) =
      DerivedCategory.Q.map f := GenericDerived.qHomEquiv_map P I f

set_option linter.unusedSectionVars false in
private theorem baseFlat :
    Abelian.HasFunctorialFlatResolution (Modules.{c, v, u} J R) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi R

attribute [local instance 1000] baseFlat

set_option linter.unusedSectionVars false in
private theorem auxTensorLeftColimits (M : Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits R M

attribute [local instance 1000] auxTensorLeftColimits

set_option linter.unusedSectionVars false in
private theorem auxTensorRightColimits (M : Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits R M

attribute [local instance 1000] auxTensorRightColimits

private theorem kFlatLocalization :
    (coefficientKFlatInclusion.{u, c, v} J R ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso (Modules.{c, v, u} J R) (.up ℤ)).inverseImage
        (coefficientKFlatInclusion.{u, c, v} J R)) := by
  let : MonoidalClosed (Modules.{c, v, u} J R) := moduleMonoidalClosed.{u, c, v} R
  let : Abelian.HasFunctorialFlatResolution (Modules.{c, v, u} J R) :=
    SheafOfModules.hasFunctorialFlatResolution_kfi R
  let : HasLimitsOfSize.{0, 0} (Modules.{c, v, u} J R) := baseLimits.{c, v, u} J R
  let : HasColimitsOfSize.{0, 0} (Modules.{c, v, u} J R) := baseColimits.{c, v, u} J R
  let : ∀ (X Y : GradedObject ℤ (Modules.{c, v, u} J R)), X.HasTensor Y :=
    gradedTensor.{c, v, u} J R
  let : ∀ (W X Y Z : GradedObject ℤ (Modules.{c, v, u} J R)),
      GradedObject.HasTensor₄ObjExt W X Y Z := gradedTensorFour.{c, v, u} J R
  let : ∀ (X Y Z : GradedObject ℤ (Modules.{c, v, u} J R)),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := gradedTensorLeft.{c, v, u} J R
  let : ∀ (X Y Z : GradedObject ℤ (Modules.{c, v, u} J R)),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := gradedTensorRight.{c, v, u} J R
  let (X : Modules.{c, v, u} J R) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    SheafOfModules.cochainTensorLeftPreservesColimits R X
  let (X : Modules.{c, v, u} J R) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    SheafOfModules.cochainTensorRightPreservesColimits R X
  let W := HomologicalComplex.quasiIso (Modules.{c, v, u} J R) (.up ℤ)
  let P : ObjectProperty (CochainComplex (Modules.{c, v, u} J R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  have : HasExactColimitsOfShape ℤ (Modules.{c, v, u} J R) :=
    SheafOfModules.hasExactColimits_int_kfi R
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution
    (Modules.{c, v, u} J R)).some.reduced
  have flat (K : CochainComplex (Modules.{c, v, u} J R) ℤ) (hK : W.kFlat K) : P K := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at hK
    intro Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (Z ⊗ K)).mp
        (hK _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  let B := ObjectProperty.lift P Λ.resolutionFunctor
    (fun K ↦ flat _ (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K))
  let Φ : LocalizerMorphism (W.inverseImage P.ι) W :=
    { functor := P.ι
      map := fun _ _ _ h ↦ h }
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions (ρ := B) Λ.resolutionNatTrans
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ DerivedCategory.Q

set_option linter.unusedSectionVars false in
private theorem baseGrothendieck :
    IsGrothendieckAbelian.{max c v u} (Modules.{c, v, u} J R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J R).1

attribute [local instance 1000] baseGrothendieck

private theorem resolutionKInjective (M : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    ((coefficientHomResolution.{u, c, v} J R).obj M).IsKInjective :=
  CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M

attribute [local instance 1000] resolutionKInjective

private noncomputable def augmentationIso
    (M : CochainComplex (Modules.{c, v, u} J R) ℤ) :
    DerivedCategory.Q.{w}.obj M ≅
      DerivedCategory.Q.obj ((coefficientHomResolution.{u, c, v} J R).obj M) :=
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{max c v u}
      (Modules.{c, v, u} J R)).app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2
  asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{max c v u}
    (Modules.{c, v, u} J R)).app M))

attribute [local instance 3000] monoidal

attribute [local irreducible] monoidal

private noncomputable def representativeEquiv
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L) :
    (DerivedCategory.Q.{w}.obj P ⊗ DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M) ≃
      (DerivedCategory.Q.obj P ⟶ (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)) := by
  let I := (coefficientHomResolution.{u, c, v} J R).obj M
  letI : I.IsKInjective := resolutionKInjective.{c, v, u} J R M
  have : (homComplex (R := R) L I).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, c, v} (J := J) (R := R) L I hL
  exact (tensorIso.{c, v, u, w} J R P L (Or.inr hL)).symm.homFromEquiv.trans
    ((augmentationIso.{c, v, u, w} J R M).homToEquiv.trans
      ((qHomEquiv.{c, v, u, w} J R ((coefficientTotalTensor.{u, c, v} J R).obj (P, L)) I).symm.trans
        ((homotopyEquiv.{c, v, u} J R P L I).trans
          ((qHomEquiv.{c, v, u, w} J R P (homComplex (R := R) L I)).trans
            (coefficientHomResolutionIso.{u, c, v, w} J R L M).symm.homToEquiv))))

private theorem representativeEquiv_uncurry
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (φ : P ⟶ homComplex (R := R) L ((coefficientHomResolution.{u, c, v} J R).obj M)) :
    (tensorIso.{c, v, u, w} J R P L (Or.inr hL)).hom ≫
      (representativeEquiv.{c, v, u, w} J R P L M hL).symm
        (DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{u, c, v, w} J R L M).inv) =
      DerivedCategory.Q.map ((chainEquiv.{c, v, u} J R P L
        ((coefficientHomResolution.{u, c, v} J R).obj M)).symm φ) ≫
          coefficientHomResolutionInverse.{u, c, v, w} J R M := by
  have : (homComplex (R := R) L
      ((coefficientHomResolution.{u, c, v} J R).obj M)).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, c, v} (J := J) (R := R) L _ hL
  unfold representativeEquiv
  simp only [Equiv.symm_trans, Equiv.trans_apply, Equiv.symm_symm,
    Iso.homToEquiv_symm_apply, Iso.symm_inv, Iso.homFromEquiv_symm_apply,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← qHomEquiv_map.{c, v, u, w} J R P _ φ, Equiv.symm_apply_apply, homotopyEquiv_symm_map]
  erw [qHomEquiv_map]
  simp only [Iso.hom_inv_id_assoc]
  rfl

attribute [local irreducible] representativeEquiv

private noncomputable def homRepresentativeIso :
    (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, u, w} J R ≅
      ((𝟭 _).prod (coefficientHomResolution.{u, c, v} J R)) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q :=
  letI : IsGrothendieckAbelian.{max c v u} (Modules.{c, v, u} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  Localization.fac
    (((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max c v u} _)) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{c, v, u, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)

attribute [local irreducible] derivedInternalHomOfUniverses

private theorem homRepresentativeIso_inv_naturality
    (L L' M M' : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (g : L' ⟶ L) (h : M ⟶ M') :
    (coefficientHomResolutionIso.{u, c, v, w} J R L M).inv ≫
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
        ((DerivedCategory.Q.map g).op, DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).map g.op).app
          ((coefficientHomResolution.{u, c, v} J R).obj M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map
              ((coefficientHomResolution.{u, c, v} J R).map h)) ≫
        (coefficientHomResolutionIso.{u, c, v, w} J R L' M').inv := by
  exact ((homRepresentativeIso.{c, v, u, w} J R).inv.naturality
    (X := (op L, M)) (Y := (op L', M')) (g.op, h)).symm

private theorem augmentation_inv_naturality
    (M M' : CochainComplex (Modules.{c, v, u} J R) ℤ) (h : M ⟶ M') :
    DerivedCategory.Q.{w}.map ((coefficientHomResolution.{u, c, v} J R).map h) ≫
        coefficientHomResolutionInverse.{u, c, v, w} J R M' =
      coefficientHomResolutionInverse.{u, c, v, w} J R M ≫ DerivedCategory.Q.map h := by
  have hn := (Functor.whiskerRight
    (CochainComplex.toKInjectiveResolution.{max c v u} (Modules.{c, v, u} J R))
      DerivedCategory.Q.{w}).naturality h
  change DerivedCategory.Q.map h ≫ (augmentationIso.{c, v, u, w} J R M').hom =
    (augmentationIso.{c, v, u, w} J R M).hom ≫
      DerivedCategory.Q.map ((coefficientHomResolution.{u, c, v} J R).map h) at hn
  change _ ≫ (augmentationIso.{c, v, u, w} J R M').inv =
    (augmentationIso.{c, v, u, w} J R M).inv ≫ _
  apply (cancel_epi (augmentationIso.{c, v, u, w} J R M).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← hn, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem representativeHom_surjective
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (ξ : DerivedCategory.Q.{w}.obj P ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)) :
    ∃ φ : P ⟶ homComplex (R := R) L
        ((coefficientHomResolution.{u, c, v} J R).obj M),
      DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{u, c, v, w} J R L M).inv = ξ := by
  have : (homComplex (R := R) L
      ((coefficientHomResolution.{u, c, v} J R).obj M)).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, c, v}
      (J := J) (R := R) L _ hL
  obtain ⟨f, hf⟩ := (qHomEquiv.{c, v, u, w} J R P _).surjective
    (ξ ≫ (coefficientHomResolutionIso.{u, c, v, w} J R L M).hom)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient (Modules.{c, v, u} J R) (.up ℤ)).map_surjective f
  rw [qHomEquiv_map] at hf
  refine ⟨φ, ?_⟩
  rw [hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem nativeTensorIso_naturality
    (P P' L L' : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (hL' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L')
    (f : P' ⟶ P) (g : L' ⟶ L) :
    (tensorIso.{c, v, u, w} J R P' L' (Or.inr hL')).hom ≫
        (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) =
      DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map
        (X := (P', L')) (Y := (P, L)) (f, g)) ≫
        (tensorIso.{c, v, u, w} J R P L (Or.inr hL)).hom := by
  exact (tensorIso_naturality.{c, v, u, w} J R P' L' P L
    (Or.inr hL') (Or.inr hL) f g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem representativeEquiv_symm_naturality
    (P P' L L' M M' : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L)
    (hL' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) L')
    (f : P' ⟶ P) (g : L' ⟶ L) (h : M ⟶ M')
    (ξ : DerivedCategory.Q.{w}.obj P ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M)) :
    (representativeEquiv.{c, v, u, w} J R P' L' M' hL').symm
        (DerivedCategory.Q.map f ≫ ξ ≫
          (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
            ((DerivedCategory.Q.map g).op, DerivedCategory.Q.map h)) =
      (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
        (representativeEquiv.{c, v, u, w} J R P L M hL).symm ξ ≫
          DerivedCategory.Q.map h := by
  obtain ⟨φ, rfl⟩ := representativeHom_surjective.{c, v, u, w} J R P L M hL ξ
  generalize hχ :
    (f ≫ φ ≫ ((homComplexFunctor (R := R)).map g.op).app
        ((coefficientHomResolution.{u, c, v} J R).obj M) ≫
      ((homComplexFunctor (R := R)).obj (op L')).map
        ((coefficientHomResolution.{u, c, v} J R).map h) :
      P' ⟶ homComplex (R := R) L'
        ((coefficientHomResolution.{u, c, v} J R).obj M')) = χ
  have hx : DerivedCategory.Q.map f ≫
      (DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{u, c, v, w} J R L M).inv) ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          ((DerivedCategory.Q.map g).op, DerivedCategory.Q.map h) =
      DerivedCategory.Q.map χ ≫ (coefficientHomResolutionIso.{u, c, v, w} J R L' M').inv := by
    simp only [Category.assoc]
    erw [homRepresentativeIso_inv_naturality]
    rw [← hχ]
    simp only [Functor.map_comp, Category.assoc]
  rw [hx]
  refine GenericNaturality.uncurry_naturality_of_comparison
    (D := DerivedCategory.{w} (Modules.{c, v, u} J R))
    (tensorIso.{c, v, u, w} J R P L (Or.inr hL))
    (tensorIso.{c, v, u, w} J R P' L' (Or.inr hL'))
    (DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map
      (X := (P', L')) (Y := (P, L)) (f, g)))
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g)
    (DerivedCategory.Q.map ((chainEquiv.{c, v, u} J R P L
      ((coefficientHomResolution.{u, c, v} J R).obj M)).symm φ))
    (DerivedCategory.Q.map ((chainEquiv.{c, v, u} J R P' L'
      ((coefficientHomResolution.{u, c, v} J R).obj M')).symm χ))
    (coefficientHomResolutionInverse.{u, c, v, w} J R M)
    (coefficientHomResolutionInverse.{u, c, v, w} J R M')
    (DerivedCategory.Q.map ((coefficientHomResolution.{u, c, v} J R).map h))
    (DerivedCategory.Q.map h) _ _ ?_ ?_ ?_ ?_ ?_
  · exact nativeTensorIso_naturality.{c, v, u, w} J R P P' L L' hL hL' f g
  · have hc := chainEquiv_symm_naturality.{c, v, u} J R P P' L L'
      ((coefficientHomResolution.{u, c, v} J R).obj M)
      ((coefficientHomResolution.{u, c, v} J R).obj M') f g
      ((coefficientHomResolution.{u, c, v} J R).map h) φ
    rw [hχ] at hc
    simpa only [Functor.map_comp] using congrArg (fun t ↦ DerivedCategory.Q.map t) hc
  · exact augmentation_inv_naturality.{c, v, u, w} J R M M' h
  · exact representativeEquiv_uncurry.{c, v, u, w} J R P L M hL φ
  · exact representativeEquiv_uncurry.{c, v, u, w} J R P' L' M' hL' χ

private noncomputable def representativeFunctor :=
  (coefficientKFlatInclusion.{u, c, v} J R ⋙ DerivedCategory.Q.{w}).op.prod
    ((coefficientKFlatInclusion.{u, c, v} J R ⋙ DerivedCategory.Q.{w}).op.prod
      (DerivedCategory.Q.{w} (C := Modules.{c, v, u} J R)))

private noncomputable def representativeHomIso :
    representativeFunctor.{c, v, u, w} J R ⋙
      GenericClosed.homHoms (derivedInternalHomOfUniverses.{c, v, u, w} J R) ≅
      representativeFunctor.{c, v, u, w} J R ⋙
      GenericClosed.tensorHoms (D := DerivedCategory.{w} (Modules.{c, v, u} J R)) :=
  NatIso.ofComponents
    (fun X ↦ (representativeEquiv.{c, v, u, w} J R X.1.unop.obj X.2.1.unop.obj
      X.2.2 X.2.1.unop.property).symm.toIso)
    (fun {X Y} f ↦ by
      ext ξ
      exact representativeEquiv_symm_naturality.{c, v, u, w} J R
        X.1.unop.obj Y.1.unop.obj X.2.1.unop.obj Y.2.1.unop.obj X.2.2 Y.2.2
        X.2.1.unop.property Y.2.1.unop.property f.1.unop.hom f.2.1.unop.hom f.2.2 ξ)

private noncomputable def representativeW :=
  let W := (HomologicalComplex.quasiIso (Modules.{c, v, u} J R) (.up ℤ)).inverseImage
    (coefficientKFlatInclusion.{u, c, v} J R)
  W.op.prod (W.op.prod (HomologicalComplex.quasiIso (Modules.{c, v, u} J R) (.up ℤ)))

private theorem representativeLocalization :
    (representativeFunctor.{c, v, u, w} J R).IsLocalization (representativeW.{c, v, u} J R) := by
  let := kFlatLocalization.{c, v, u, w} J R
  dsimp only [representativeFunctor, representativeW]
  infer_instance

attribute [local instance 1000] representativeLocalization

private noncomputable def closedStructure :
    CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R) :=
  GenericClosed.localizedClosed (D := DerivedCategory.{w} (Modules.{c, v, u} J R))
    (derivedInternalHomOfUniverses.{c, v, u, w} J R)
    (representativeFunctor.{c, v, u, w} J R) (representativeW.{c, v, u} J R)
    (representativeHomIso.{c, v, u, w} J R)

private theorem closedStructure_representatives
    (P L : ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) :
        ObjectProperty (CochainComplex (Modules.{c, v, u} J R) ℤ)))
    (M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (ξ : DerivedCategory.Q.{w}.obj P.obj ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj L.obj), DerivedCategory.Q.obj M)) :
    ((closedStructure.{c, v, u, w} J R).transpose
      (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj L.obj)
      (DerivedCategory.Q.obj M)).symm ξ =
      (representativeEquiv.{c, v, u, w} J R P.obj L.obj M L.property).symm ξ := by
  exact GenericClosed.localizedClosed_transpose_symm
    (D := DerivedCategory.{w} (Modules.{c, v, u} J R))
    (derivedInternalHomOfUniverses.{c, v, u, w} J R)
    (representativeFunctor.{c, v, u, w} J R) (representativeW.{c, v, u} J R)
    (representativeHomIso.{c, v, u, w} J R) (op P, (op L, M)) ξ

set_option linter.unusedSectionVars false in
private theorem chainEquiv_symm_pure
    (P L M : CochainComplex (Modules.{c, v, u} J R) ℤ)
    (φ : P ⟶ homComplex (R := R) L M)
    (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (L.X q).val.obj U) :
    (((chainEquiv.{c, v, u} J R P L M).symm φ).f k).val.app U
        (coefficientTensorGenerator.{u, c, v} J R P L p q k h U x y) =
      (((φ.f p ≫ homComplexπ L M p q k h').val.app U x).app
        (op (Over.mk (𝟙 U.unop))) y) := by
  have he := chainEquiv_symm_f.{c, v, u} J R P L M φ p q k h
  have he' := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.CochainScalarConstruction.pure R (P.X p) (L.X q) U x y)) he
  change ((HomologicalComplex.ιTensorObj P L p q k h ≫
    ((chainEquiv.{c, v, u} J R P L M).symm φ).f k).val.app U)
      (SheafOfModules.CochainScalarConstruction.pure R (P.X p) (L.X q) U x y) = _
  refine he'.trans ?_
  change ((tensorHomEquiv.{u, c, v} R (L.X q) (P.X p) (M.X k)).symm
    (φ.f p ≫ homComplexπ L M p q k h')).val.app U
      ((β_ (P.X p) (L.X q)).hom.val.app U
        (SheafOfModules.CochainScalarConstruction.pure R (P.X p) (L.X q) U x y)) = _
  erw [pure_braiding.{c, v, u} J R, uncurry_pure.{c, v, u} J R]

private theorem closedStructure_uncurry :
    CoefficientTensorUncurryModel.{u, c, v, w} J R (closedStructure.{c, v, u, w} J R)
      (comparison.{c, v, u, w} J R) := by
  intro P L M φ
  refine ⟨(chainEquiv.{c, v, u} J R P.obj L.obj
    ((coefficientHomResolution.{u, c, v} J R).obj M)).symm φ, ?_, ?_⟩
  · intro p q k h h' U x y
    exact chainEquiv_symm_pure.{c, v, u} J R P.obj L.obj
      ((coefficientHomResolution.{u, c, v} J R).obj M) φ p q k h h' U x y
  · rw [closedStructure_representatives.{c, v, u, w} J R]
    exact representativeEquiv_uncurry.{c, v, u, w} J R P.obj L.obj M L.property φ

/-- The native derived tensor is left adjoint to the recorded derived internal Hom,
with the evaluation normalization on the fixed simultaneous K-flat comparison.
The equality fixes only the existing monoidal structure; this theorem constructs
its adjunctions and checks evaluation, and asserts no symmetry or constraint formulas.

Source: Stacks Project, Tag 08J9, proved using 0A90 and 0A8Z
(auxiliary; not a blueprint node).

Proof: choose K-flat representatives P,L and a K-injective replacement I(M).
The sheaf Hom complex Hom(L,I(M)) is K-injective because L is K-flat.
The Hom-total-tensor isomorphism of 0A90, ordinary global sections and zeroth
cohomology identify maps from P into this Hom complex with maps from Tot(P tensor L)
into I(M), modulo homotopy (0A8Z). K-injectivity identifies these classes with
morphisms in the derived category. The inverse of the native lax comparison
identifies the other side with morphisms out of the derived tensor. Both
localizations extend this equivalence uniquely to all derived objects and maps.
Currying on homogeneous sections sends x tensor y to phi(x)(y), without an
extra sign: the Hom differential is exactly the total-tensor chain-map equation.
This also takes homotopies to homotopies. Naturality under precomposition in P,L
and postcomposition in I(M) holds componentwise and descends through localization,
including inverse denominators. Package the resulting natural Hom equivalences
as adjunctions. Naturality in L is the evaluation_naturality field. The componentwise
formula applied before localization is precisely CoefficientTensorUncurryModel;
the inverse localized replacement augmentation gives its stated target comparison.
The monoidal structure and its fixed tensor comparison are those already constructed
by native K-flat localization, so their equalities are identities. -/
theorem closedAdjunction :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R),
      S.monoidal = monoidal.{c, v, u, w} J R ∧
        ∃ T : CoefficientTensorModels.{u, c, v, w} J R S,
          HEq T.comparison (comparison.{c, v, u, w} J R) := by
  refine ⟨closedStructure.{c, v, u, w} J R, rfl, ?_⟩
  exact ⟨⟨comparison.{c, v, u, w} J R, closedStructure_uncurry.{c, v, u, w} J R⟩, HEq.rfl⟩

end CategoryTheory.RingedDerivedNative
