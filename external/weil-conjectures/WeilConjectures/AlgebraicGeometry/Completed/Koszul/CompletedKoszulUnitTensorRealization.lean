/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulRegularUnitNormalization

/-! # Unit tensor realization of the completed exterior Koszul tower

Source: Stacks Project, Tags 099M, 0921 and 093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
attribute [local instance] koszulConstantFunctor_preservesZero
local instance unitTensorCochainMonoidal
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategory (CochainComplex (CompletedAdicModules T d) ℤ) :=
  CategoryTheory.flatConstantCochainMonoidal
    (J := ProEt.topology T) (O := completedAdicCommRing T d)
local instance unitTensorCochainMonoidalStruct
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategoryStruct (CochainComplex (CompletedAdicModules T d) ℤ) :=
  (unitTensorCochainMonoidal T d).toMonoidalCategoryStruct

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
attribute [local irreducible] completedAdicRing completedAdicChangeData

private theorem generator_single (r : ℕ) (a : Fin r → A)
    (j : Fin r) (c : ULift.{t + 1} A) :
    koszulPowerGenerator A r a (Finsupp.single j c) =
      Finsupp.single j (c * ULift.up (a j)) := by
  simp [koszulPowerGenerator, Finsupp.linearCombination_single]

private theorem generator_pow_single (r : ℕ) (a : Fin r → A)
    (k : ℕ) (j : Fin r) (c : ULift.{t + 1} A) :
    (koszulPowerGenerator A r a ^ k) (Finsupp.single j c) =
      Finsupp.single j (c * ULift.up (a j ^ k)) := by
  induction k generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    congr 1
    apply ULift.ext
    simp
  | succ k ih =>
    rw [pow_succ]
    change (koszulPowerGenerator A r a ^ k)
      (koszulPowerGenerator A r a (Finsupp.single j c)) = _
    rw [generator_single, ih]
    congr 1
    apply ULift.ext
    simp [pow_succ, mul_assoc, mul_comm]

private theorem generator_pow (r : ℕ) (a : Fin r → A) (k : ℕ) :
    koszulPowerGenerator A r a ^ k =
      Finsupp.linearCombination (ULift.{t + 1} A)
        (fun j ↦ Finsupp.single j ((ULift.up (a j) : ULift.{t + 1} A) ^ k)) := by
  apply Finsupp.lhom_ext
  intro j c
  rw [generator_pow_single]
  simp only [Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]
  rfl

private theorem coefficient_jump (r : ℕ) (a : Fin r → A) (n k q : ℕ) :
    let K := fun m ↦ ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
      (fun j ↦ ULift.up (a j ^ (m + 1)))
    let e : ∀ m, ((K m).extend ComplexShape.embeddingDownNat).X
        (ComplexShape.embeddingDownNat.f q) ≅
      ModuleCat.of (ULift.{t + 1} A) (⋀[ULift.{t + 1} A]^q (Fin r →₀ ULift.{t + 1} A)) :=
    fun m ↦ (K m).extendXIso ComplexShape.embeddingDownNat (i := q) rfl
    let S := Functor.ofOpSequence (koszulPowerTransition A r a)
    (S.map (homOfLE (Nat.le_add_right n k)).op).f
      (ComplexShape.embeddingDownNat.f q) =
      (e (n + k)).hom ≫ ModuleCat.ofHom
        (exteriorPower.map q (koszulPowerGenerator A r a ^ k)) ≫ (e n).inv := by
  dsimp only
  let K := fun m ↦ ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
    (fun j ↦ ULift.up (a j ^ (m + 1)))
  let e : ∀ m, ((K m).extend ComplexShape.embeddingDownNat).X
        (ComplexShape.embeddingDownNat.f q) ≅
      ModuleCat.of (ULift.{t + 1} A) (⋀[ULift.{t + 1} A]^q (Fin r →₀ ULift.{t + 1} A)) :=
    fun m ↦ (K m).extendXIso ComplexShape.embeddingDownNat (i := q) rfl
  let S := Functor.ofOpSequence (koszulPowerTransition A r a)
  change (S.map _).f _ = (e (n + k)).hom ≫ _ ≫ (e n).inv
  have hstep (m : ℕ) : (koszulPowerTransition A r a m).f
      (ComplexShape.embeddingDownNat.f q) =
      (e (m + 1)).hom ≫ ModuleCat.ofHom
        (exteriorPower.map q (koszulPowerGenerator A r a)) ≫ (e m).inv := by
    dsimp only [koszulPowerTransition]
    exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat rfl
  induction k with
  | zero =>
    have hm : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    erw [hm, S.map_id, HomologicalComplex.id_f, pow_zero]
    change 𝟙 _ = (e n).hom ≫ ModuleCat.ofHom (exteriorPower.map q LinearMap.id) ≫ (e n).inv
    erw [exteriorPower.map_id]
    change 𝟙 _ = (e n).hom ≫ 𝟙 _ ≫ (e n).inv
    erw [Category.id_comp, Iso.hom_inv_id]
  | succ k ih =>
    have hm : (homOfLE (Nat.le_add_right n (k + 1))).op =
        (homOfLE (Nat.le_succ (n + k))).op ≫
          (homOfLE (Nat.le_add_right n k)).op := Subsingleton.elim _ _
    erw [hm, S.map_comp, HomologicalComplex.comp_f, ih]
    dsimp only [S]
    erw [Functor.ofOpSequence_map_homOfLE_succ]
    erw [hstep]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [pow_succ]
    change _ = _ ≫ ModuleCat.ofHom
      (exteriorPower.map q ((koszulPowerGenerator A r a ^ k).comp
        (koszulPowerGenerator A r a))) ≫ _
    have hc : ModuleCat.ofHom (exteriorPower.map q
        ((koszulPowerGenerator A r a ^ k).comp (koszulPowerGenerator A r a))) =
        ModuleCat.ofHom (exteriorPower.map q (koszulPowerGenerator A r a)) ≫
          ModuleCat.ofHom (exteriorPower.map q (koszulPowerGenerator A r a ^ k)) := by
      rw [exteriorPower.map_comp, ModuleCat.ofHom_comp]
    erw [hc]
    simp only [Category.assoc]
    rfl

private theorem unit_twist {C : Type*} [Category* C] [MonoidalCategory C]
    (b : 𝟙_ C ≅ 𝟙_ C) {X : C} (z : 𝟙_ C ⟶ X) :
    (b.hom ≫ z) ≫ (λ_ X).inv ≫ (b.inv ▷ X) =
      (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ z) := by
  calc
    _ = b.hom ≫ (λ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ z) ≫ (b.inv ▷ X) := by
      rw [Category.assoc, leftUnitor_inv_naturality_assoc]
    _ = b.hom ≫ (ρ_ (𝟙_ C)).inv ≫ (b.inv ▷ 𝟙_ C) ≫ (𝟙_ C ◁ z) := by
      rw [whisker_exchange, unitors_inv_equal]
    _ = (b.hom ≫ b.inv) ≫ (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ z) := by
      simp only [Category.assoc, rightUnitor_inv_naturality_assoc, comp_whiskerRight]
    _ = _ := by simp only [Iso.hom_inv_id, Category.id_comp]

private theorem unit_twist_comp {C : Type*} [Category* C] [MonoidalCategory C]
    (b : 𝟙_ C ≅ 𝟙_ C) {X Y : C} (z : 𝟙_ C ⟶ X) (f : 𝟙_ C ⊗ X ⟶ Y) :
    b.hom ≫ z ≫ (λ_ X).inv ≫ (b.inv ▷ X) ≫ f =
      (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C ◁ z) ≫ f := by
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ f) (unit_twist b z)

private theorem unit_tensor_normalization
    (K : CochainComplex (CompletedAdicModules T d) ℤ)
    (b : SheafOfModules.unit (completedAdicRing T d) ≅
      SheafOfModules.unit (completedAdicRing T d))
    (z : SheafOfModules.unit (completedAdicRing T d) ⟶ K.X 0) :
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedAdicCommRing T d)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedAdicCommRing T d)
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let α : U ≅ U :=
    (HomologicalComplex.single (CompletedAdicModules T d) (.up ℤ) 0).mapIso b.symm
  (b.hom ≫ z) ≫ ((λ_ K).inv ≫ (α.hom ▷ K)).f 0 =
    (ρ_ (U.X 0)).inv ≫ (U.X 0 ◁ z) ≫
      HomologicalComplex.ιMapBifunctor U K (curriedTensor _) (.up ℤ) 0 0 0 rfl := by
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedAdicCommRing T d)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedAdicCommRing T d)
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let α : U ≅ U :=
    (HomologicalComplex.single (CompletedAdicModules T d) (.up ℤ) 0).mapIso b.symm
  dsimp only
  change (b.hom ≫ z) ≫ ((λ_ K).inv ≫ (α.hom ▷ K)).f 0 = _
  rw [HomologicalComplex.comp_f]
  have hα : α.hom.f 0 = b.inv := by
    dsimp only [α, Functor.mapIso_hom, Iso.symm_hom]
    rw [HomologicalComplex.single_map_f_self]
    change (𝟙 _) ≫ b.inv ≫ 𝟙 _ = b.inv
    simp only [Category.id_comp, Category.comp_id]
  have hl : (λ_ K).inv.f 0 =
      (λ_ (K.X 0)).inv ≫
        HomologicalComplex.ιMapBifunctor U K (curriedTensor _) (.up ℤ) 0 0 0 rfl := by
    change (HomologicalComplex.leftUnitor' K).inv 0 = _
    rw [HomologicalComplex.leftUnitor'_inv]
    change (λ_ (K.X 0)).inv ≫ (𝟙 _ ▷ K.X 0) ≫ _ = _
    simp only [id_whiskerRight, Category.id_comp]
    rfl
  rw [hl]
  change (b.hom ≫ z) ≫
    ((λ_ (K.X 0)).inv ≫
      HomologicalComplex.ιMapBifunctor U K (curriedTensor _) (.up ℤ) 0 0 0 rfl) ≫
    (HomologicalComplex.mapBifunctorMap α.hom (𝟙 K)
      (curriedTensor _) (.up ℤ)).f 0 = _
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    hα, whiskerLeft_id]
  change b.hom ≫ z ≫
    (λ_ (K.X 0)).inv ≫ (b.inv ▷ K.X 0) ≫ _ =
      (ρ_ (U.X 0)).inv ≫ (U.X 0 ◁ z) ≫ _
  erw [Category.id_comp]
  erw [unit_twist_comp b z]
  rfl

private theorem coefficient_transition
    (r : ℕ) (a : Fin r → A)
    (sA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))))
    (hsA : ∀ n m h k, (sA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k (Finsupp.linearCombination (ULift.{t + 1} A)
        (fun i ↦ Finsupp.single i ((ULift.up (a i) : ULift.{t + 1} A) ^ (m - n))))))
    (n m : ℕ) (h : n ≤ m) :
    HomologicalComplex.extendMap (sA n m h) ComplexShape.embeddingDownNat =
      (Functor.ofOpSequence (koszulPowerTransition A r a)).map (homOfLE h).op := by
  let S := Functor.ofOpSequence (koszulPowerTransition A r a)
  change _ = S.map (homOfLE h).op
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  apply HomologicalComplex.hom_ext
  intro p
  by_cases hp : ∃ q, ComplexShape.embeddingDownNat.f q = p
  · obtain ⟨q, rfl⟩ := hp
    rw [HomologicalComplex.extendMap_f _ _ rfl, hsA,
      coefficient_jump, generator_pow]
    simp only [Nat.add_sub_cancel_left]
    rfl
  · exact (HomologicalComplex.isZero_extend_X
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + k + 1)))
      ComplexShape.embeddingDownNat p (fun q hq ↦ hp ⟨q, hq⟩)).eq_of_src _ _

/-- The concrete scalar realization of the exterior complexes is the actual
Koszul tower tensored with the cochain unit. Any regular-module identification
can be used, with the same scalar twist in every exterior degree.

Source: Stacks Project, more-algebra.tex, lemma-sequence-Koszul-complexes (0921),
and proetale.tex, proof of lemma-naive-completion (099M).
(blueprint: lem-weil-pbc-completed-koszul-unit-tensor-realization).

Proof: termwise application of the composite functor is termwise constant
sheafification followed by completed scalar extension, hence is the construction
of completedAdicKoszul. The inverse left unitor identifies it with unit tensor
completedAdicKoszul. The specified regular-module isomorphism differs from the
canonical one by an automorphism of the completed rank-one module. Such an
automorphism is multiplication by a unit section. Multiply every exterior term
by the inverse unit section to adjust the comparison to c; linearity makes this
commute with the differential and every diagonal transition. In exterior degree
zero, exteriorPower.zeroEquiv identifies the regular module with the Koszul
term, and the normalized unit is exactly this map followed by the tensor
unitor. This proves the last identity. The component formula hsA identifies
sA with the product of the recorded successors: the diagonal exponent is m-n,
and exponents add under composition. Complex extension and scalar realization
preserve the equality. Naturality of the left unitor and of multiplication then
gives the transition identity for every n<=m, including equality. For r=0 the
same degree-zero calculation is the entire comparison. -/
theorem completedKoszulUnitTensorRealization
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (sA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))))
    (hsA : ∀ n m h k, (sA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k (Finsupp.linearCombination (ULift.{t + 1} A)
        (fun i ↦ Finsupp.single i ((ULift.up (a i) : ULift.{t + 1} A) ^ (m - n)))))) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
    ∀ c : U.X 0 ≅ E.obj (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)),
    ∃ eK : ∀ n : ℕ, (E.mapHomologicalComplex (.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))).extend
            ComplexShape.embeddingDownNat) ≅
        ((completedKoszulTensorTower T d r a).obj U).asFunctor.obj (op n),
      (∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap (sA n m h) ComplexShape.embeddingDownNat) ≫
          (eK n).hom = (eK m).hom ≫
            ((completedKoszulTensorTower T d r a).obj U).asFunctor.map (homOfLE h).op) ∧
      ∀ n : ℕ, c.hom ≫ E.map
        (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
          (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
          ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
            (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A) ^ (n + 1))).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv) ≫
        (eK n).hom.f 0 = (completedAdicKoszulTensorUnit T d r a U n).f 0 := by
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  let : MonoidalPreadditive (CompletedAdicModules T d) :=
    SheafOfModules.cochainModulesPreadditive (completedAdicCommRing T d)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedAdicCommRing T d)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedAdicCommRing T d)
  let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let K := completedAdicKoszul T d r a
  let S := Functor.ofOpSequence (koszulPowerTransition A r a)
  let F := ((completedKoszulTensorTower T d r a).obj U).asFunctor
  dsimp only
  intro c
  obtain ⟨c₀, hc₀⟩ := completedKoszulRegularUnitNormalization T d r a
  let b : SheafOfModules.unit (completedAdicRing T d) ≅
      SheafOfModules.unit (completedAdicRing T d) := c ≪≫ c₀.symm
  let α : U ≅ U :=
    (HomologicalComplex.single (CompletedAdicModules T d) (.up ℤ) 0).mapIso b.symm
  let eK : ∀ n : ℕ, K n ≅ F.obj (op n) :=
    fun n ↦ (λ_ (K n)).symm ≪≫ whiskerRightIso α (K n)
  have hη (n : ℕ) :
      (S ⋙ E.mapHomologicalComplex (.up ℤ)).map
          (homOfLE (Nat.le_succ n)).op ≫ (eK n).hom =
        (eK (n + 1)).hom ≫ F.map (homOfLE (Nat.le_succ n)).op := by
    dsimp only [Functor.comp_map, S]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change completedAdicKoszulStep T d r a n ≫
        ((λ_ (K n)).inv ≫ (α.hom ▷ K n)) =
      ((λ_ (K (n + 1))).inv ≫ (α.hom ▷ K (n + 1))) ≫
        (Functor.ofOpSequence (completedAdicKoszulTensorStep T d r a U)).map
          (homOfLE (Nat.le_succ n)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change _ = _ ≫ (U ◁ completedAdicKoszulStep T d r a n)
    rw [leftUnitor_inv_naturality_assoc]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ (λ_ (K (n + 1))).inv ≫ f)
      (whisker_exchange α.hom (completedAdicKoszulStep T d r a n))
  let η : S ⋙ E.mapHomologicalComplex (.up ℤ) ⟶ F :=
    NatTrans.ofOpSequence (fun n ↦ (eK n).hom) hη
  refine ⟨eK, ?_, ?_⟩
  · intro n m h
    rw [coefficient_transition r a sA hsA n m h]
    exact η.naturality (homOfLE h).op
  · intro n
    let z := ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
      (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
        ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
          (fun i ↦ ULift.up (a i ^ (n + 1)))).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv
    have hn : completedAdicKoszulUnitZero T d r a n = c₀.hom ≫ E.map z :=
      hc₀ n
    have hv : c.hom ≫ E.map z = b.hom ≫ completedAdicKoszulUnitZero T d r a n := by
      rw [hn]
      simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_assoc]
    change c.hom ≫ E.map z ≫ ((λ_ (K n)).inv ≫ (α.hom ▷ K n)).f 0 = _
    rw [← Category.assoc, hv]
    change (b.hom ≫ completedAdicKoszulUnitZero T d r a n) ≫
        ((λ_ (K n)).inv ≫ (α.hom ▷ K n)).f 0 =
      (ρ_ (U.X 0)).inv ≫ (U.X 0 ◁ completedAdicKoszulUnitZero T d r a n) ≫
        HomologicalComplex.ιMapBifunctor U (K n) (curriedTensor _) (.up ℤ) 0 0 0 rfl
    exact unit_tensor_normalization T d (K n) b (completedAdicKoszulUnitZero T d r a n)

end AlgebraicGeometry.Scheme
