/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.SignedKoszulSummandTermTransport

/-!
# The differential on a negative Koszul pure tensor

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free tensor calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

section TensorPoint

open MonoidalCategory

variable {E : Type*} [Category* E] [Preadditive E] [HasCountableCoproducts E]
  [MonoidalCategory E] [MonoidalPreadditive E]

@[irreducible] private noncomputable def tensorPoint
    (P Q : CochainComplex E ℤ) (p t n : ℤ) (h : p + t = n)
    (f : 𝟙_ E ⟶ P.X p) (g : 𝟙_ E ⟶ Q.X t) :
    𝟙_ E ⟶ (HomologicalComplex.mapBifunctor P Q (curriedTensor E) (.up ℤ)).X n :=
  (λ_ (𝟙_ E)).inv ≫ (f ⊗ₘ g) ≫
    CochainComplex.ιMapBifunctor P Q (curriedTensor E) p t n h

variable (P Q : CochainComplex E ℤ) (p t n : ℤ) (h : p + t = n)
  (f : 𝟙_ E ⟶ P.X p) (g : 𝟙_ E ⟶ Q.X t)

private theorem tensorPoint_precomp_left (s : End (𝟙_ E)) :
    tensorPoint P Q p t n h (s.asHom ≫ f) g =
      s.asHom ≫ tensorPoint P Q p t n h f g := by
  unfold tensorPoint
  rw [unitors_inv_equal, rightUnitor_inv_comp_tensorHom_assoc]
  simp only [Category.assoc, rightUnitor_inv_naturality_assoc,
    tensorHom_def, comp_whiskerRight]

private theorem tensorPoint_precomp_right (s : End (𝟙_ E)) :
    tensorPoint P Q p t n h f (s.asHom ≫ g) =
      s.asHom ≫ tensorPoint P Q p t n h f g := by
  unfold tensorPoint
  simp only [leftUnitor_inv_comp_tensorHom_assoc, Category.assoc]

private theorem tensorPoint_sum_right {ι : Type*} (S : Finset ι)
    (g : ι → (𝟙_ E ⟶ Q.X t)) :
    tensorPoint P Q p t n h f (∑ i ∈ S, g i) =
      ∑ i ∈ S, tensorPoint P Q p t n h f (g i) := by
  simp only [tensorPoint, tensor_sum, Preadditive.sum_comp, Preadditive.comp_sum]

private theorem tensorPoint_zero_left : tensorPoint P Q p t n h 0 g = 0 := by
  simp only [tensorPoint, MonoidalPreadditive.zero_tensor, zero_comp, comp_zero]

private theorem tensorPoint_index (t' : ℤ) (h' : p + t' = n)
    (β : ∀ k, 𝟙_ E ⟶ Q.X k) (ht : t = t') :
    tensorPoint P Q p t n h f (β t) = tensorPoint P Q p t' n h' f (β t') := by
  subst t'
  rfl

private theorem tensorPoint_d :
    tensorPoint P Q p t n h f g ≫
        (HomologicalComplex.mapBifunctor P Q (curriedTensor E) (.up ℤ)).d n (n + 1) =
      tensorPoint P Q (p + 1) t (n + 1) (by omega) (f ≫ P.d p (p + 1)) g +
        (-1 : ℤˣ) ^ p •
          tensorPoint P Q p (t + 1) (n + 1) (by omega) f (g ≫ Q.d t (t + 1)) := by
  unfold tensorPoint
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Category.assoc]
  rw [HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ rfl _ _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ rfl _ (by dsimp; omega)]
  change _ ≫ _ ≫ ((1 : ℤˣ) • (_ ≫ _)) +
    _ ≫ _ ≫ (((-1 : ℤˣ) ^ p) • (_ ≫ _)) = _
  simp only [one_smul, Linear.comp_units_smul, curriedTensor_map_app,
    curriedTensor_obj_map, tensorHom_comp_whiskerRight_assoc,
    tensorHom_comp_whiskerLeft_assoc]

omit [HasCountableCoproducts E] [MonoidalCategory E] [MonoidalPreadditive E] in
private theorem negative_units_comp {X Y Z : E} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (-1 : ℤˣ) ^ (-1 : ℤ) • (f ≫ g) = (-f) ≫ g := by
  change (-1 : ℤ) • (f ≫ g) = (-f) ≫ g
  simp only [neg_one_smul, Preadditive.neg_comp]

end TensorPoint

private theorem negativeFactorBasis_d_neg
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedNegativeKoszulFactorBasis O b m (-1) ≫
        (ringedNegativeKoszulFactor O b m).d (-1) 0 =
      ((ringedKoszulScalar O b) ^ (m + 1)).asHom ≫
        ringedNegativeKoszulFactorBasis O b m 0 := by
  simp [ringedNegativeKoszulFactorBasis, ringedNegativeKoszulFactor,
    HomologicalComplex.double_d]

private theorem negativeFactorBasis_d_zero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedNegativeKoszulFactorBasis O b m 0 ≫
        (ringedNegativeKoszulFactor O b m).d 0 1 = 0 := by
  rw [show (ringedNegativeKoszulFactor O b m).d 0 1 = 0 from
    HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide), comp_zero]

private theorem map_preimage_succ {r : ℕ} (I : Finset (Fin (r + 1))) :
    (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective r h)).map (Fin.succEmb r) =
      I.erase 0 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

private theorem negativeBasis_transport
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (I : Finset (Fin r)) (n n' : ℤ) (h : n = n') :
    ringedNegativeKoszulBasis O r b m I n ≫
        eqToHom (congrArg (ringedNegativeKoszul O r b m).X h) =
      ringedNegativeKoszulBasis O r b m I n' := by
  subst n'
  simp

private theorem earlier_map_succ {r : ℕ} (S : Finset (Fin r)) (i : Fin r) :
    ((S.map (Fin.succEmb r)).filter (fun j ↦ j < i.succ)).card =
      (S.filter (fun j ↦ j < i)).card := by
  simp [Finset.filter_map]

private theorem earlier_insert_zero {r : ℕ} (S : Finset (Fin r)) (i : Fin r) :
    ((insert 0 (S.map (Fin.succEmb r))).filter (fun j ↦ j < i.succ)).card =
      (S.filter (fun j ↦ j < i)).card + 1 := by
  simp [Finset.filter_insert, earlier_map_succ]

noncomputable section Basis

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})

local instance instIsGrothendieckAbelianSignedKoszulSummandDifferential :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  SheafOfModules.isGrothendieckAbelian _

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

local instance instMonoidalPreadditiveSignedKoszulSummandDifferential :
    MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).1

local instance instMonoidalClosedSignedKoszulSummandDifferential :
    MonoidalClosed (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  Classical.choice (SheafOfModules.tensorClosed O).2.1

private theorem negativeBasis_map_succ (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (S : Finset (Fin r)) (n : ℤ) :
    ringedNegativeKoszulBasis O (r + 1) b m (S.map (Fin.succEmb r)) n =
      tensorPoint (ringedNegativeKoszulFactor O (b 0) m)
        (ringedNegativeKoszul O r (fun i ↦ b i.succ) m) 0 n n (by omega)
        (ringedNegativeKoszulFactorBasis O (b 0) m 0)
        (ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m S n) := by
  have h0 : (0 : Fin (r + 1)) ∉ S.map (Fin.succEmb r) := by simp
  have hp : (S.map (Fin.succEmb r)).preimage Fin.succ
      (fun _ _ _ _ h ↦ Fin.succ_injective r h) = S := by ext i; simp
  let B (k : ℤ) := tensorPoint (ringedNegativeKoszulFactor O (b 0) m)
    (ringedNegativeKoszul O r (fun i ↦ b i.succ) m) k (n - k) n (by omega)
    (ringedNegativeKoszulFactorBasis O (b 0) m k)
    (ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m S (n - k))
  have he : (if (0 : Fin (r + 1)) ∈ S.map (Fin.succEmb r) then (-1 : ℤ) else 0) = 0 :=
    ite_eq_right h0
  have hrec : ringedNegativeKoszulBasis O (r + 1) b m (S.map (Fin.succEmb r)) n =
      B (if (0 : Fin (r + 1)) ∈ S.map (Fin.succEmb r) then -1 else 0) := by
    simp only [ringedNegativeKoszulBasis, B, tensorPoint, hp]
    rfl
  rw [hrec, he]
  exact tensorPoint_index _ _ _ _ _ _ _ _ _
    (fun k ↦ ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m S k) (sub_zero n)

private theorem negativeBasis_insert_zero (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (S : Finset (Fin r)) (n : ℤ) :
    ringedNegativeKoszulBasis O (r + 1) b m (insert 0 (S.map (Fin.succEmb r))) n =
      tensorPoint (ringedNegativeKoszulFactor O (b 0) m)
        (ringedNegativeKoszul O r (fun i ↦ b i.succ) m) (-1) (n + 1) n (by omega)
        (ringedNegativeKoszulFactorBasis O (b 0) m (-1))
        (ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m S (n + 1)) := by
  have h0 : (0 : Fin (r + 1)) ∈ insert 0 (S.map (Fin.succEmb r)) :=
    Finset.mem_insert_self _ _
  have hp : (insert 0 (S.map (Fin.succEmb r))).preimage Fin.succ
      (fun _ _ _ _ h ↦ Fin.succ_injective r h) = S := by ext i; simp
  let B (k : ℤ) := tensorPoint (ringedNegativeKoszulFactor O (b 0) m)
    (ringedNegativeKoszul O r (fun i ↦ b i.succ) m) k (n - k) n (by omega)
    (ringedNegativeKoszulFactorBasis O (b 0) m k)
    (ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m S (n - k))
  have he : (if (0 : Fin (r + 1)) ∈ insert 0 (S.map (Fin.succEmb r))
      then (-1 : ℤ) else 0) = -1 := ite_eq_left h0
  have hrec : ringedNegativeKoszulBasis O (r + 1) b m
      (insert 0 (S.map (Fin.succEmb r))) n =
      B (if (0 : Fin (r + 1)) ∈ insert 0 (S.map (Fin.succEmb r)) then -1 else 0) := by
    simp only [ringedNegativeKoszulBasis, B, tensorPoint, hp]
    rfl
  rw [hrec, he]
  exact tensorPoint_index _ _ _ _ _ _ _ _ _
    (fun k ↦ ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m S k)
    (sub_neg_eq_add n 1)

attribute [local irreducible] ringedNegativeKoszulBasis ringedNegativeKoszulFactorBasis
  ringedKoszulScalar

private theorem negativeBasis_d_insert_term (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (S : Finset (Fin r)) (n : ℤ) (i : Fin r) :
    (-1 : ℤˣ) ^ (-1 : ℤ) •
        tensorPoint (ringedNegativeKoszulFactor O (b 0) m)
          (ringedNegativeKoszul O r (fun j ↦ b j.succ) m)
          (-1) (n + 1 + 1) (n + 1) (by omega)
          (ringedNegativeKoszulFactorBasis O (b 0) m (-1))
          ((((-1 : ℤ) ^ (S.filter (fun j ↦ j < i)).card) •
            ((ringedKoszulScalar O (b i.succ)) ^ (m + 1))).asHom ≫
            ringedNegativeKoszulBasis O r (fun j ↦ b j.succ) m (S.erase i) (n + 1 + 1)) =
      (((-1 : ℤ) ^
        ((insert 0 (S.map (Fin.succEmb r))).filter (fun j ↦ j < i.succ)).card) •
        ((ringedKoszulScalar O (b i.succ)) ^ (m + 1))).asHom ≫
        ringedNegativeKoszulBasis O (r + 1) b m
          ((insert 0 (S.map (Fin.succEmb r))).erase i.succ) (n + 1) := by
  erw [tensorPoint_precomp_right, earlier_insert_zero,
    Finset.erase_insert_of_ne (Fin.succ_ne_zero i).symm, ← Finset.map_erase,
    negativeBasis_insert_zero, negative_units_comp]
  erw [pow_succ (-1 : ℤ), mul_neg_one, neg_smul]
  simp only [End.neg_asHom]

private theorem negativeBasis_d_insert (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (S : Finset (Fin r)) (n : ℤ)
    (hd : ∀ (T : Finset (Fin r)) (k : ℤ),
    ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m T k ≫
        (ringedNegativeKoszul O r (fun i ↦ b i.succ) m).d k (k + 1) =
      ∑ i ∈ T, (((-1 : ℤ) ^ (T.filter (fun j ↦ j < i)).card) •
        ((ringedKoszulScalar O (b i.succ)) ^ (m + 1))).asHom ≫
        ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m (T.erase i) (k + 1)) :
    ringedNegativeKoszulBasis O (r + 1) b m (insert 0 (S.map (Fin.succEmb r))) n ≫
        (ringedNegativeKoszul O (r + 1) b m).d n (n + 1) =
      ∑ i ∈ (insert 0 (S.map (Fin.succEmb r))), (((-1 : ℤ) ^
        ((insert 0 (S.map (Fin.succEmb r))).filter (fun j ↦ j < i)).card) •
        ((ringedKoszulScalar O (b i)) ^ (m + 1))).asHom ≫
        ringedNegativeKoszulBasis O (r + 1) b m
          ((insert 0 (S.map (Fin.succEmb r))).erase i) (n + 1) := by
  classical
  have hn : (0 : Fin (r + 1)) ∉ S.map (Fin.succEmb r) := by simp
  rw [negativeBasis_insert_zero]
  erw [tensorPoint_d, negativeFactorBasis_d_neg, hd]
  erw [tensorPoint_precomp_left, tensorPoint_sum_right, Finset.smul_sum,
    Finset.sum_insert hn, Finset.sum_map S (Fin.succEmb r)]
  apply congrArg₂ (· + ·)
  · have hc : ((insert 0 (S.map (Fin.succEmb r))).filter (fun j ↦ j < 0)).card = 0 :=
      by simp
    erw [hc, pow_zero, one_smul, Finset.erase_insert hn, negativeBasis_map_succ]
    rfl
  · apply Finset.sum_congr rfl
    intro i hi
    exact negativeBasis_d_insert_term O r b m S n i

private theorem negativeBasis_d_map (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (S : Finset (Fin r)) (n : ℤ)
    (hd : ∀ (T : Finset (Fin r)) (k : ℤ),
    ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m T k ≫
        (ringedNegativeKoszul O r (fun i ↦ b i.succ) m).d k (k + 1) =
      ∑ i ∈ T, (((-1 : ℤ) ^ (T.filter (fun j ↦ j < i)).card) •
        ((ringedKoszulScalar O (b i.succ)) ^ (m + 1))).asHom ≫
        ringedNegativeKoszulBasis O r (fun i ↦ b i.succ) m (T.erase i) (k + 1)) :
    ringedNegativeKoszulBasis O (r + 1) b m (S.map (Fin.succEmb r)) n ≫
        (ringedNegativeKoszul O (r + 1) b m).d n (n + 1) =
      ∑ i ∈ (S.map (Fin.succEmb r)), (((-1 : ℤ) ^
        ((S.map (Fin.succEmb r)).filter (fun j ↦ j < i)).card) •
        ((ringedKoszulScalar O (b i)) ^ (m + 1))).asHom ≫
        ringedNegativeKoszulBasis O (r + 1) b m
          ((S.map (Fin.succEmb r)).erase i) (n + 1) := by
  classical
  rw [negativeBasis_map_succ]
  erw [tensorPoint_d, negativeFactorBasis_d_zero, tensorPoint_zero_left,
    zero_add, zpow_zero, one_smul, hd, tensorPoint_sum_right,
    Finset.sum_map S (Fin.succEmb r)]
  apply Finset.sum_congr rfl
  intro i hi
  erw [tensorPoint_precomp_right, earlier_map_succ, ← Finset.map_erase,
    negativeBasis_map_succ]
  rfl

private theorem negativeBasis_d (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (I : Finset (Fin r)) (n : ℤ) :
    ringedNegativeKoszulBasis O r b m I n ≫ (ringedNegativeKoszul O r b m).d n (n + 1) =
      ∑ i ∈ I, (((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card) •
        ((ringedKoszulScalar O (b i)) ^ (m + 1))).asHom ≫
        ringedNegativeKoszulBasis O r b m (I.erase i) (n + 1) := by
  classical
  induction r generalizing n with
  | zero =>
    have hI : I = ∅ := Subsingleton.elim _ _
    subst I
    simp [ringedNegativeKoszul, ringedSiteRingComplex]
  | succ r ih =>
    let S := I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective r h)
    have hS : S.map (Fin.succEmb r) = I.erase 0 := map_preimage_succ I
    by_cases h0 : (0 : Fin (r + 1)) ∈ I
    · have hI : I = insert 0 (S.map (Fin.succEmb r)) := by
        rw [hS, Finset.insert_erase h0]
      rw [hI]
      exact negativeBasis_d_insert O r b m S n (ih (fun i ↦ b i.succ))
    · have hI : I = S.map (Fin.succEmb r) := by
        rw [hS, Finset.erase_eq_of_notMem h0]
      rw [hI]
      exact negativeBasis_d_map O r b m S n (ih (fun i ↦ b i.succ))

end Basis

/-- The ordered negative Koszul basis differential, before tensoring with coefficients.
The erased-index coefficient includes the preceding-index sign and the scalar power m+1.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul; the finite ordered-tensor calculation.
(auxiliary; not a blueprint node).

Proof in words: induct on the number of factors.  The empty tensor has zero
differential.  In the successor step use the differential of the two-term head
factor and the induction hypothesis for the tail.  A head in degree zero has no
outgoing differential; a head in degree -1 contributes its scalar power.  The
tensor differential contributes one minus sign for every selected preceding
factor.  Reindexing the tail subsets by `Fin.succ` gives the displayed erased-
index sum and its degree transports.
-/
theorem ringedNegativeKoszulBasis_d_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (I : Finset (Fin (r + 1))) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ringedNegativeKoszulBasis O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ)) ≫
      (ringedNegativeKoszul O (r + 1)
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m).d
        (-(I.card : ℤ)) (-(I.card : ℤ) + 1) =
      ∑ i ∈ I, if h : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ) then
        ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
            (ringedKoszulScalar O ⟨(ρ (a i)).val, (ρ (a i)).property⟩) ^ (m + 1)).asHom ≫
          ringedNegativeKoszulBasis O (r + 1)
            (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m
            (I.erase i) (-((I.erase i).card : ℤ)) ≫
          eqToHom (congrArg
            (ringedNegativeKoszul O (r + 1)
              (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m).X h.symm)
      else 0 := by
  classical
  rw [negativeBasis_d]
  apply Finset.sum_congr rfl
  intro i hi
  have hcard : (I.erase i).card + 1 = I.card := by
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hsrc : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ) := by omega
  rw [dite_eq_left hsrc]
  symm
  exact congrArg (fun f ↦
    ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card •
      ((ringedKoszulScalar O ⟨(ρ (a i)).val, (ρ (a i)).property⟩) ^ (m + 1))).asHom ≫ f)
    (negativeBasis_transport O (r + 1)
      (fun j ↦ ⟨(ρ (a j)).val, (ρ (a j)).property⟩) m (I.erase i)
      _ _ hsrc.symm)

/-- The Koszul-direction part of the differential on a specified pure tensor.
The ordered tensor has positive length. This contains neither the coefficient-complex
differential nor a coordinate isomorphism.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul; the second step of
lem-cbc-signed-koszul-tensor-coordinates.
(auxiliary; not a blueprint node).

Proof in words: use HomologicalComplex.mapBifunctor.ι_D₂ to evaluate the
second total differential on the inclusion in ringedNegativeKoszulSummand.
Induct on the number of ordered Koszul factors. The empty tensor is O[0],
whose differential is zero, giving the induction base. In the successor step
apply the two total-differential formulas to the recursive basis map. The head
factor contributes only when zero belongs to I. Its preceding-index count is
zero. For each successor index the tail induction gives its coefficient;
the additional head sign is minus one exactly when zero belongs to I.
Thus the earlier-index count is the tail count plus that indicator.
This expands the differential of the ordered Koszul basis vector.
A factor in degree zero contributes zero. A factor i in degree
-1 contributes multiplication by a_i^(m+1) and changes its degree to zero,
leaving the basis vector for I.erase i. The total-tensor sign is minus one for
each earlier factor in degree -1, hence (-1) to the cardinality of the filter
of elements of I smaller than i. Tensoring with K adds the sign (-1)^(q+|I|),
written by parity in A. Multiplication on the rank-one factor acts on a tensor
through the same global-section scalar action ringedKoszulCoefficientSMul.
For i in I, card (I.erase i)=card I-1, so the displayed equality of coefficient
degrees holds. Insert its equality transport to give exactly the corresponding
summand below. Additivity of tensor and composition gives the finite sum.
For the empty subset the sum is empty. For r=1 its only erased coefficient is
(-1)^(q+1) a_0^(m+1). The proof involves neither scalar inversion nor boundedness
of K and is valid for zero rings, zero sections, and the empty site. -/
theorem ringedNegativeKoszulSummand_D₂_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
    (I : Finset (Fin (r + 1))) :
    letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
      SheafOfModules.isGrothendieckAbelian _
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ringedNegativeKoszulSummand O ρ a m K q I ≫
      HomologicalComplex.mapBifunctor.D₂ K
        (ringedNegativeKoszul O (r + 1) (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m)
        (MonoidalCategory.curriedTensor _) (.up ℤ) q (q + 1) =
      ∑ i ∈ I, if h : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ) then
        ringedKoszulCoefficientSMul O ρ
          ((if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1))
          (K.XIsoOfEq h).hom ≫
            ringedNegativeKoszulSummand O ρ a m K (q + 1) (I.erase i)
      else 0 := by
  let E := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let Q := ringedNegativeKoszul O (r + 1)
    (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m
  change ringedNegativeKoszulSummand O ρ a m K q I ≫
    HomologicalComplex.mapBifunctor.D₂ K Q (MonoidalCategory.curriedTensor E)
      (.up ℤ) q (q + 1) = _
  change ((MonoidalCategory.rightUnitor (K.X (q + I.card))).inv ≫
    MonoidalCategory.tensorHom (𝟙 _) (ringedNegativeKoszulBasis O (r + 1)
      (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ))) ≫
    CochainComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E)
      (q + I.card) (-(I.card : ℤ)) q (by omega)) ≫
      HomologicalComplex.mapBifunctor.D₂ K Q (MonoidalCategory.curriedTensor E)
        (.up ℤ) q (q + 1) = _
  simp only [Category.assoc]
  rw [HomologicalComplex.mapBifunctor.ι_D₂]
  have hrel : (ComplexShape.up ℤ).Rel (-(I.card : ℤ))
      (-(I.card : ℤ) + 1) := by
    change -(I.card : ℤ) + 1 = -(I.card : ℤ) + 1
    rfl
  have hpi : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (.up ℤ)
      (q + I.card, -(I.card : ℤ) + 1) = q + 1 := by
    change q + (I.card : ℤ) + (-(I.card : ℤ) + 1) = q + 1
    omega
  have hd := HomologicalComplex.mapBifunctor.d₂_eq K Q
    (MonoidalCategory.curriedTensor E) (.up ℤ) (q + I.card)
    (i₂ := -(I.card : ℤ)) (i₂' := -(I.card : ℤ) + 1) hrel (q + 1) hpi
  rw [hd]
  have he₂ : (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (q + I.card, -(I.card : ℤ)) = (-1 : ℤˣ) ^ (q + I.card) := by
    rfl
  rw [he₂]
  dsimp only [MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app]
  simp only [MonoidalCategory.id_tensorHom]
  rw [Linear.comp_units_smul]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [ringedNegativeKoszulBasis_d_succ O ρ r a m I]
  rw [Linear.comp_units_smul]
  change _ • (_ ≫ (MonoidalCategory.tensorLeft (K.X (q + I.card))).map _ ≫ _) = _
  rw [Functor.map_sum]
  rw [Preadditive.sum_comp, Preadditive.comp_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hdeg : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ)
  · have hcard : (I.erase i).card + 1 = I.card := by
      rw [Finset.card_erase_of_mem hi]
      omega
    have hsrc : -(I.card : ℤ) + 1 = -((I.erase i).card : ℤ) := by omega
    simp only [dite_eq_left hsrc, dite_eq_left hdeg]
    rw [ringedNegativeKoszulSummand]
    exact ringedNegativeKoszulSummand_D₂_term O ρ r a m K q I i hi hdeg hsrc
  · have hsrc : -(I.card : ℤ) + 1 ≠ -((I.erase i).card : ℤ) := by
      intro hs
      apply hdeg
      omega
    simp only [dite_eq_right hsrc, dite_eq_right hdeg, Functor.map_zero,
      comp_zero, zero_comp, smul_zero]
end CategoryTheory
