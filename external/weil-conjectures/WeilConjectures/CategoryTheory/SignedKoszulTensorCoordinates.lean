/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.SignedKoszulSummandDifferential
import WeilConjectures.CategoryTheory.SignedKoszulTensorCoproduct

/-!
# The normalized finite tensor calculation

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

private theorem pureTensor_firstDifferential
    {E : Type*} [Category* E] [Preadditive E] [HasCountableCoproducts E]
    [MonoidalCategory E] [MonoidalPreadditive E]
    (K Q : CochainComplex E ℤ) (p p' n q q' : ℤ)
    (hp : p + 1 = p') (h : p + n = q) (h' : p' + n = q')
    (β : MonoidalCategory.tensorUnit E ⟶ Q.X n) :
    (MonoidalCategory.rightUnitor (K.X p)).inv ≫ MonoidalCategory.tensorHom (𝟙 _) β ≫
      HomologicalComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) (.up ℤ)
        p n q h ≫
      HomologicalComplex.mapBifunctor.D₁ K Q (MonoidalCategory.curriedTensor E)
        (.up ℤ) q q' =
    K.d p p' ≫ (MonoidalCategory.rightUnitor (K.X p')).inv ≫
      MonoidalCategory.tensorHom (𝟙 _) β ≫
      HomologicalComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) (.up ℤ)
        p' n q' h' := by
  rw [HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hp _ _ h']
  rw [show ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, n) = 1 from rfl]
  simp only [one_smul, MonoidalCategory.curriedTensor_map_app]
  rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]
  simp only [MonoidalCategory.tensorHom_comp_whiskerRight_assoc,
    MonoidalCategory.whiskerRight_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

private theorem negativeKoszulSummand_d
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
    (I : Finset (Fin r)) :
    ringedNegativeKoszulSummand O ρ a m K q I ≫
        ((ringedNegativeKoszulTensor O ρ a m).obj K).d q (q + 1) =
      K.d (q + I.card) ((q + 1) + I.card) ≫
        ringedNegativeKoszulSummand O ρ a m K (q + 1) I +
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
  let Q := ringedNegativeKoszul O r (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m
  change ringedNegativeKoszulSummand O ρ a m K q I ≫
    (HomologicalComplex.mapBifunctor K Q (MonoidalCategory.curriedTensor E) (.up ℤ)).d
      q (q + 1) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  apply congrArg₂ (· + ·)
  · exact pureTensor_firstDifferential K Q (q + I.card) ((q + 1) + I.card)
      (-(I.card : ℤ)) q (q + 1) (by omega) (by omega) (by omega)
      (ringedNegativeKoszulBasis O r
        (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩) m I (-(I.card : ℤ)))
  · cases r with
    | zero =>
      have hI : I = ∅ := Subsingleton.elim _ _
      subst I
      have hd : HomologicalComplex.mapBifunctor.D₂ K
          (HomologicalComplex.tensorUnit E (.up ℤ)) (MonoidalCategory.curriedTensor E)
          (.up ℤ) q (q + 1) = 0 := by
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p n h
        rw [HomologicalComplex.mapBifunctor.ι_D₂, comp_zero]
        exact HomologicalComplex.tensor_unit_d₂ K p n (q + 1)
      change _ ≫ HomologicalComplex.mapBifunctor.D₂ K
        (HomologicalComplex.tensorUnit E (.up ℤ)) (MonoidalCategory.curriedTensor E)
        (.up ℤ) q (q + 1) = _
      rw [hd, comp_zero]
      simp only [Finset.sum_empty]
    | succ r => exact ringedNegativeKoszulSummand_D₂_succ O ρ r a m K q I

private theorem zeroKoszulSummands_isColimit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (a : Fin 0 → A) (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
    Nonempty (IsColimit (Cofan.mk
      (((ringedNegativeKoszulTensor O ρ a m).obj K).X q)
      (ringedNegativeKoszulSummand O ρ a m K q))) := by
  classical
  let E := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let e : ((ringedNegativeKoszulTensor O ρ a m).obj K).X q ≅ K.X q :=
    (HomologicalComplex.eval E (.up ℤ) q).mapIso (ringedKoszulRightUnitIso O K)
  let e' : ((ringedNegativeKoszulTensor O ρ a m).obj K).X q ≅
      K.X (q + ((∅ : Finset (Fin 0)).card : ℤ)) :=
    e ≪≫ K.XIsoOfEq (by simp)
  have he : e.inv = (HomologicalComplex.rightUnitor' K).inv q := rfl
  have hs : ringedNegativeKoszulSummand O ρ a m K q ∅ = e'.inv := by
    dsimp only [e', Iso.trans_inv]
    rw [he, HomologicalComplex.rightUnitor'_inv]
    simp [ringedNegativeKoszulSummand, ringedNegativeKoszulBasis,
      MonoidalCategory.id_tensorHom, HomologicalComplex.XIsoOfEq]
    cases q <;> rfl
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦ e'.hom ≫ s.inj ∅) ?_ ?_⟩
  · intro s I
    have hI : I = ∅ := Subsingleton.elim _ _
    subst I
    change ringedNegativeKoszulSummand O ρ a m K q ∅ ≫ (e'.hom ≫ s.inj ∅) = _
    rw [hs, Iso.inv_hom_id_assoc]
  · intro s f hf
    apply (cancel_epi e'.inv).1
    rw [Iso.inv_hom_id_assoc, ← hs]
    exact hf ∅

/-- The finite subset decomposition of the ordered negative tensor, with the signed
matrix for its differential and the canonical pure-tensor normalization.
This does not construct transitions or assert quasi-isomorphism invariance.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the finite free negative Koszul calculation;
step 1 of lem-cbc-signed-koszul-finite-coordinates.
(auxiliary; not a blueprint node).

Proof in words: induct on the number of ordered factors. For zero factors, identify
K tensor O[0] with K by its right unitor and identify the sole subset with the empty
set. For the successor, split subsets according to membership of the first index.
The negative double complex is O in degrees -1 and 0 and zero otherwise. Distributing
the tensor over these two terms and over the finite subset decomposition of the tail
therefore gives the indicated biproduct. Define its inverse by the specified pure
tensors, using the inverse unitors and total-tensor inclusions. The projections are
multiplication by the rank-one coordinates, so their composites with the inclusions
are the Kronecker identities and their sum is the identity. Thus these maps are inverse.
In the total differential the K part has sign one. The ith factor part has sign (-1)^(q+|I|)
from K and one extra minus sign for every preceding negative factor. Its coefficient
is a_i^(m+1) and it erases i. Sum over i, inserting the equality transports between
the indicated degrees, to obtain the stated matrix. This also proves normalization.
At r=0 only the K differential survives; at r=1 the off-diagonal coefficient is
(-1)^(q+1) a_0^(m+1). Nothing divides by a scalar, so zero rings and zero sections
are allowed. The calculation is degreewise finite and places no bound on K. -/
theorem exists_ringedSignedKoszulTensorCoordinates
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin r → A) :
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  ∃ (coordinates : ∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ),
    ((ringedNegativeKoszulTensor O ρ a m).obj K).X q ≅
      ⨁ fun I : Finset (Fin r) ↦ K.X (q + I.card)),
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
      (I L : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates m K q).inv ≫
        (((ringedNegativeKoszulTensor O ρ a) m).obj K).d q (q + 1) ≫ (coordinates m K (q + 1)).hom ≫
          biproduct.π _ L =
      (if I = L then K.d (q + I.card) ((q + 1) + L.card) else 0) +
      (if h : q + (I.card : ℤ) = (q + 1) + (L.card : ℤ) then
        ringedKoszulCoefficientSMul O ρ (∑ i ∈ I, if I.erase i = L then
          (if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
            (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1) else 0)
              (K.XIsoOfEq h).hom else 0)) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)),
      biproduct.ι _ I ≫ (coordinates m K q).inv =
        ringedNegativeKoszulSummand O ρ a m K q I) := by
  classical
  let := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let : Linear (RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.homLinear O.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property
  have hc (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
      Nonempty (IsColimit (Cofan.mk
        (((ringedNegativeKoszulTensor O ρ a m).obj K).X q)
        (ringedNegativeKoszulSummand O ρ a m K q))) := by
    cases r with
    | zero => exact zeroKoszulSummands_isColimit O ρ a m K q
    | succ r => exact isColimit_ringedNegativeKoszulSummands_succ O ρ r a m K q
  let c (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
      ((ringedNegativeKoszulTensor O ρ a m).obj K).X q ≅
        ⨁ fun I : Finset (Fin r) ↦ K.X (q + I.card) :=
    (Classical.choice (hc m K q))
      |>.coconePointUniqueUpToIso (biproduct.isColimit _)
  have hn (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)) :
      biproduct.ι _ I ≫ (c m K q).inv =
        ringedNegativeKoszulSummand O ρ a m K q I := by
    exact IsColimit.comp_coconePointUniqueUpToIso_inv
      (Classical.choice (hc m K q))
      (biproduct.isColimit _) (Discrete.mk I)
  have hp (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I L : Finset (Fin r)) :
      ringedNegativeKoszulSummand O ρ a m K q I ≫
          (c m K q).hom ≫ biproduct.π _ L =
        if h : I = L then
          (K.XIsoOfEq (congrArg (fun P : Finset (Fin r) ↦ q + (P.card : ℤ)) h)).hom
        else 0 := by
    rw [← hn]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π]
    by_cases h : I = L
    · subst L
      simp
    · simp [h]
  refine ⟨c, ?_, hn⟩
  intro m K q I L
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hn]
  rw [negativeKoszulSummand_d]
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc]
  apply congrArg₂ (· + ·)
  · rw [hp]
    by_cases h : I = L
    · subst L
      simp
    · simp [h]
  · by_cases h : q + (I.card : ℤ) = (q + 1) + (L.card : ℤ)
    · rw [dite_eq_left h]
      simp only [ringedKoszulCoefficientSMul, map_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases he : I.erase i = L
      · subst L
        simp [h, Category.assoc, hp]
      · by_cases heq : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ)
        · simp only [dite_eq_left heq, Category.assoc,
            Linear.smul_comp, hp, dite_eq_right he, ite_eq_right he, map_zero, comp_zero,
            zero_smul, smul_zero]
        · simp only [dite_eq_right heq, zero_comp, ite_eq_right he, map_zero, zero_smul]
    · rw [dite_eq_right h]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases heq : q + (I.card : ℤ) = (q + 1) + ((I.erase i).card : ℤ)
      · have he : I.erase i ≠ L := by
          intro he
          exact h (he ▸ heq)
        simp only [dite_eq_left heq, Category.assoc, ringedKoszulCoefficientSMul,
          Linear.smul_comp, hp, dite_eq_right he, comp_zero, smul_zero]
      · simp only [dite_eq_right heq, zero_comp]

end CategoryTheory
