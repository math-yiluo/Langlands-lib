/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorAugmentationComponent
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.preservesZeroMorphisms_of_additive
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

lemma coneComparison_fst
    {B : Type*} [Category B] [Abelian B]
    {D : Type*} [Category D] [Abelian D]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (E : B ⥤ D) [E.Additive] (r : ℤ) :
    ((CochainComplex.mappingCone.mapHomologicalComplexIso f E).hom.f r) ≫
      (CochainComplex.mappingCone.fst ((E.mapHomologicalComplex (.up ℤ)).map f)).1.v
        r (r + 1) rfl = E.map ((CochainComplex.mappingCone.fst f).1.v r (r + 1) rfl) := by
  change (CochainComplex.mappingCone.mapHomologicalComplexXIso' f E r
    (r + 1) rfl).hom ≫ _ = _
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_fst_v,
    CochainComplex.mappingCone.inr_f_fst_v, comp_zero, add_zero]
  exact Category.comp_id _

lemma coneComparison_snd
    {B : Type*} [Category B] [Abelian B]
    {D : Type*} [Category D] [Abelian D]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (E : B ⥤ D) [E.Additive] (r : ℤ) :
    ((CochainComplex.mappingCone.mapHomologicalComplexIso f E).hom.f r) ≫
      (CochainComplex.mappingCone.snd ((E.mapHomologicalComplex (.up ℤ)).map f)).v
        r r (add_zero r) = E.map ((CochainComplex.mappingCone.snd f).v r r (add_zero r)) := by
  change (CochainComplex.mappingCone.mapHomologicalComplexXIso' f E r
    (r + 1) rfl).hom ≫ _ = _
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_snd_v,
    CochainComplex.mappingCone.inr_f_snd_v, comp_zero, zero_add]
  exact Category.comp_id _

def levelConeTower
    {B : Type*} [Category B] [Abelian B]
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    ℕᵒᵖ ⥤ CochainComplex B ℤ where
  obj n := CochainComplex.mappingCone (f.app n)
  map {m n} t := CochainComplex.mappingCone.map (f.app m) (f.app n)
    (X.map t) (Y.map t) (f.naturality t).symm
  map_id n := by
    calc
      _ = CochainComplex.mappingCone.map (f.app n) (f.app n) (𝟙 _) (𝟙 _)
          (by simp) := by congr 1 <;> simp
      _ = _ := CochainComplex.mappingCone.map_id (f.app n)
  map_comp {m n k} t s := by
    simpa only [Functor.map_comp] using CochainComplex.mappingCone.map_comp
      (f.app m) (f.app n) (f.app k) (X.map t) (Y.map t)
      (f.naturality t).symm (X.map s) (Y.map s) (f.naturality s).symm

def levelConeTowerIso
    {B : Type*} [Category B] [Abelian B]
    {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    (CochainComplex.mappingCone
      ((HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse.map f)).asFunctor ≅
      levelConeTower f :=
  NatIso.ofComponents (fun n ↦ CochainComplex.mappingCone.mapHomologicalComplexIso
    ((HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse.map f)
    ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)) (by
      intro m n t
      ext r
      apply CochainComplex.mappingCone.ext_to _ r (r + 1) rfl
      · simp only [HomologicalComplex.comp_f, Category.assoc]
        dsimp only [levelConeTower]
        simp only [CochainComplex.mappingCone.map,
          CochainComplex.mappingCone.desc_f,
          CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
          Preadditive.add_comp, Category.assoc,
          CochainComplex.mappingCone.inl_v_fst_v,
          CochainComplex.mappingCone.inr_f_fst_v, comp_zero, add_zero, Category.comp_id]
        erw [coneComparison_fst]
        rw [← Category.assoc]
        erw [coneComparison_fst]
        exact ((CochainComplex.mappingCone.fst
          ((HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse.map f)).1.v
            r (r + 1) rfl).naturality t
      · simp only [HomologicalComplex.comp_f, Category.assoc]
        dsimp only [levelConeTower]
        simp only [CochainComplex.mappingCone.map,
          CochainComplex.mappingCone.desc_f,
          CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
          Preadditive.add_comp, Category.assoc,
          CochainComplex.mappingCone.inl_v_snd_v,
          CochainComplex.mappingCone.inr_f_snd_v, comp_zero, zero_add, Category.comp_id]
        erw [coneComparison_snd]
        rw [← Category.assoc]
        erw [coneComparison_snd]
        exact ((CochainComplex.mappingCone.snd
          ((HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse.map f)).v
            r r (add_zero r)).naturality t)

def levelConeTower_mapBifunctorIso
    {B : Type*} [Category B] [Abelian B]
    {D : Type*} [Category D] [Abelian D]
    (F : B ⥤ B ⥤ D) [F.Additive] [∀ M : B, (F.obj M).Additive]
    [∀ K L : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
    (P : CochainComplex B ℤ) {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) :
    levelConeTower f ⋙ (Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P ≅
      levelConeTower (Functor.whiskerRight f
        ((Functor.map₂HomologicalComplex F (.up ℤ) (.up ℤ) (.up ℤ)).obj P)) :=
  NatIso.ofComponents (fun n ↦ CochainComplex.mapBifunctorMappingCone₂Iso P (f.app n) F)
    (by
      intro m n t
      exact CochainComplex.mapBifunctorMappingCone₂Iso_hom_naturality
        F (𝟙 P) (f.app m) (f.app n) (X.map t) (Y.map t) (f.naturality t).symm)

def coneTowerMap
    {B : Type*} [Category B] [Abelian B]
    {X Y X' Y' : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    levelConeTower f ⟶ levelConeTower g where
  app n := CochainComplex.mappingCone.map (f.app n) (g.app n)
    (a.app n) (b.app n) (congr_app h n)
  naturality m n t := by
    dsimp only [levelConeTower]
    rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
    congr 1
    · exact a.naturality t
    · exact b.naturality t

def coneTowerIso
    {B : Type*} [Category B] [Abelian B]
    {X Y X' Y' : ℕᵒᵖ ⥤ CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') (h : f ≫ b.hom = a.hom ≫ g) :
    levelConeTower f ≅ levelConeTower g where
  hom := coneTowerMap f g a.hom b.hom h
  inv := coneTowerMap g f a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    dsimp only [coneTowerMap, NatTrans.comp_app, NatTrans.id_app]
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.hom_inv_id_app, CochainComplex.mappingCone.map_id]
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    dsimp only [coneTowerMap, NatTrans.comp_app, NatTrans.id_app]
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.inv_hom_id_app, CochainComplex.mappingCone.map_id]
    rfl

attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local instance] augmentationComponentPreadditive
attribute [local irreducible] completedAdicRing

def towerIsoOfSuccessors
    {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C}
    (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op) : F ≅ G := by
  let f := NatTrans.ofOpSequence (fun n ↦ (e n).hom) h
  have : ∀ n, IsIso (f.app n) := fun n ↦ inferInstanceAs (IsIso (e n.unop).hom)
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact asIso f

@[irreducible] def koszulTensorUnitor
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K P : CochainComplex (CompletedAdicModules T d) ℤ) :
    P ⊗ ((𝟙_ _) ⊗ K) ≅ P ⊗ K :=
  (tensorLeft P).mapIso (λ_ K)

def koszulTensorTowerUnitor
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K : ℕ → CochainComplex (CompletedAdicModules T d) ℤ)
    (step : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    Functor.ofOpSequence (X := fun n ↦ (𝟙_ _) ⊗ K n)
      (fun n ↦ (tensorLeft (𝟙_ _)).map (step n)) ⋙ tensorLeft P ≅
      Functor.ofOpSequence (X := fun n ↦ P ⊗ K n)
      (fun n ↦ (tensorLeft P).map (step n)) := by
  exact towerIsoOfSuccessors (fun n ↦ koszulTensorUnitor T d (K n) P) (by
      intro n
      unfold koszulTensorUnitor
      dsimp only [Functor.mapIso_hom]
      change (tensorLeft P).map
          ((Functor.ofOpSequence (X := fun n ↦ (𝟙_ _) ⊗ K n)
            (fun n ↦ (tensorLeft (𝟙_ _)).map (step n))).map
            (homOfLE (Nat.le_succ n)).op) ≫ _ = _ ≫
          (Functor.ofOpSequence (X := fun n ↦ P ⊗ K n)
            (fun n ↦ (tensorLeft P).map (step n))).map
            (homOfLE (Nat.le_succ n)).op
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (tensorLeft P).map ((tensorLeft (𝟙_ _)).map (step n)) ≫
          (tensorLeft P).map (λ_ (K n)).hom =
        (tensorLeft P).map (λ_ (K (n + 1))).hom ≫ (tensorLeft P).map (step n)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((tensorLeft P).map) (leftUnitor_naturality (step n)))

theorem single_naturality
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P Q : CochainComplex (CompletedAdicModules T d) ℤ) (f : P ⟶ Q)
    {N N' : CompletedAdicModules T d} (g : N ⟶ N') :
    ((((curriedTensor (CompletedAdicModules T d)).map₂CochainComplex).map f).app _ ≫
        (((curriedTensor (CompletedAdicModules T d)).map₂CochainComplex).obj Q).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map g)) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N' Q).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N P).hom ≫
        ((((curriedTensor _).flip.obj N).mapHomologicalComplex (.up ℤ)).map f ≫
          (NatTrans.mapHomologicalComplex
            ((curriedTensor (CompletedAdicModules T d)).flip.map g) (.up ℤ)).app Q) := by
  apply (cancel_epi
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (CompletedAdicModules T d)) N P).inv).1
  apply (cancel_mono
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (CompletedAdicModules T d)) N' Q).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    CochainComplex.mapBifunctorSingle₁XIso, ComplexShape.π_def, Functor.flip_obj_obj,
    curriedTensor_obj_obj, Functor.flip_map_app, curriedTensor_obj_map, Functor.flip_obj_map,
    curriedTensor_map_app, eqToHom_whiskerRight, Iso.symm_mk, Iso.trans_inv, Iso.symm_inv,
    Category.comp_id, Category.assoc, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom_assoc,
    ComplexShape.σ_def, mul_zero, Int.negOnePow_zero, one_smul, NatTrans.naturality_assoc,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  change _ ≫ _ ≫
    (HomologicalComplex.mapBifunctorMap f (𝟙 _) (curriedTensor _) (.up ℤ)).f n ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 Q)
      ((HomologicalComplex.single _ (.up ℤ) 0).map g) (curriedTensor _) (.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp [HomologicalComplex.single_map_f_self, ← tensorHom_id, ← id_tensorHom]

@[irreducible] def quotientUnitIso
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : CompletedAdicModules T d) :
    ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ _) ≅
      (HomologicalComplex.single _ (.up ℤ) 0).obj Q :=
  (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).symm ≪≫
    λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)

@[irreducible] def quotientTensorIso
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : CompletedAdicModules T d) (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    P ⊗ ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ _) ≅
      ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj P :=
  (tensorLeft P).mapIso (quotientUnitIso T d Q) ≪≫
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P

lemma singleTensor_naturality
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    {Q Q' : CompletedAdicModules T d} (f : Q ⟶ Q') :
    P ◁ (HomologicalComplex.single _ (.up ℤ) 0).map f ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q' P).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P).hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) (.up ℤ)).app P := by
  have h := single_naturality T d P P (𝟙 P) f
  erw [((curriedTensor (CompletedAdicModules T d)).map₂CochainComplex).map_id,
    NatTrans.id_app, Category.id_comp,
    (((curriedTensor _).flip.obj Q).mapHomologicalComplex (.up ℤ)).map_id,
    Category.id_comp] at h
  exact h

lemma quotientUnitIso_naturality
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    {Q Q' : CompletedAdicModules T d} (f : Q ⟶ Q') :
    (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) (.up ℤ)).app (𝟙_ _) ≫
        (quotientUnitIso T d Q').hom =
      (quotientUnitIso T d Q).hom ≫ (HomologicalComplex.single _ (.up ℤ) 0).map f := by
  apply (cancel_epi
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).hom).1
  unfold quotientUnitIso
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  erw [← Category.assoc, ← singleTensor_naturality T d, Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact leftUnitor_naturality _

lemma quotientTensorIso_naturality
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    {Q Q' : CompletedAdicModules T d} (f : Q ⟶ Q') :
    P ◁ (NatTrans.mapHomologicalComplex
        ((curriedTensor _).flip.map f) (.up ℤ)).app (𝟙_ _) ≫
          (quotientTensorIso T d Q' P).hom =
      (quotientTensorIso T d Q P).hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) (.up ℤ)).app P := by
  unfold quotientTensorIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  have hq := congrArg ((tensorLeft P).map) (quotientUnitIso_naturality T d f)
  simp only [Functor.map_comp] at hq
  calc
    _ = ((tensorLeft P).map
          ((NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f)
            (.up ℤ)).app (𝟙_ _)) ≫
          (tensorLeft P).map (quotientUnitIso T d Q').hom) ≫ _ :=
      (Category.assoc _ _ _).symm
    _ = ((tensorLeft P).map (quotientUnitIso T d Q).hom ≫
          (tensorLeft P).map ((HomologicalComplex.single _ (.up ℤ) 0).map f)) ≫ _ :=
      congrArg (fun z ↦ z ≫ _) hq
    _ = _ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun z ↦ (tensorLeft P).map (quotientUnitIso T d Q).hom ≫ z)
        (singleTensor_naturality T d P f)

def ordinaryTensorSequence
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : ℕ → CompletedAdicModules T d) (step : ∀ n, Q (n + 1) ⟶ Q n) :
    CompletedAdicModules T d ⥤ ℕᵒᵖ ⥤ CompletedAdicModules T d :=
  (Functor.ofOpSequence
    (X := fun n ↦ (curriedTensor (CompletedAdicModules T d)).flip.obj (Q n))
    (fun n ↦ (curriedTensor _).flip.map (step n))).flip

instance ordinaryTensorSequence_additive
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : ℕ → CompletedAdicModules T d) (step : ∀ n, Q (n + 1) ⟶ Q n) :
    (ordinaryTensorSequence T d Q step).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  exact (tensorRight (Q n.unop)).map_add

lemma ordinaryTensorSequence_succ
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : ℕ → CompletedAdicModules T d) (step : ∀ n, Q (n + 1) ⟶ Q n)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) :
    letI := ordinaryTensorSequence_additive T d Q step
    (((ordinaryTensorSequence T d Q step).mapHomologicalComplex (.up ℤ)).obj P).asFunctor.map
        (homOfLE (Nat.le_succ n)).op =
      (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map (step n)) (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro k
  change ((Functor.ofOpSequence
    (X := fun n ↦ (curriedTensor (CompletedAdicModules T d)).flip.obj (Q n))
    (fun n ↦ (curriedTensor _).flip.map (step n))).map
      (homOfLE (Nat.le_succ n)).op).app (P.X k) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

def quotientTensorTowerIso
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : ℕ → CompletedAdicModules T d) (step : ∀ n, Q (n + 1) ⟶ Q n)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    letI := ordinaryTensorSequence_additive T d Q step
    (((ordinaryTensorSequence T d Q step).mapHomologicalComplex (.up ℤ)).obj
        (𝟙_ _)).asFunctor ⋙ tensorLeft P ≅
      (((ordinaryTensorSequence T d Q step).mapHomologicalComplex (.up ℤ)).obj P).asFunctor := by
  exact towerIsoOfSuccessors (fun n ↦ quotientTensorIso T d (Q n) P) (by
        intro n
        calc
          _ = P ◁ (NatTrans.mapHomologicalComplex
                ((curriedTensor _).flip.map (step n)) (.up ℤ)).app (𝟙_ _) ≫
              (quotientTensorIso T d (Q n) P).hom :=
            congrArg (fun z ↦ (tensorLeft P).map z ≫ (quotientTensorIso T d (Q n) P).hom)
              (ordinaryTensorSequence_succ T d Q step (𝟙_ _) n)
          _ = (quotientTensorIso T d (Q (n + 1)) P).hom ≫
              (NatTrans.mapHomologicalComplex
                ((curriedTensor _).flip.map (step n)) (.up ℤ)).app P :=
            quotientTensorIso_naturality T d P (step n)
          _ = _ := congrArg (fun z ↦ (quotientTensorIso T d (Q (n + 1)) P).hom ≫ z)
            (ordinaryTensorSequence_succ T d Q step P n).symm)

end AlgebraicGeometry.Scheme
