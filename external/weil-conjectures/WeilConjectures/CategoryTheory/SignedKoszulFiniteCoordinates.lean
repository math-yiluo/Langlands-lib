/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.SignedKoszulTensorCoordinates
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# Finite coordinates of the normalized negative Koszul tensors

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

private theorem coefficient_smul_comp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {M N P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)}
    (b : A) (f : M ⟶ N) (g : N ⟶ P) :
    ringedKoszulCoefficientSMul O ρ b f ≫ g =
      ringedKoszulCoefficientSMul O ρ b (f ≫ g) := by
  let : Linear (RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.homLinear O.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property
  exact Linear.smul_comp M N P (ρ b) f g

private theorem coefficient_comp_smul
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {M N P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)}
    (b : A) (f : M ⟶ N) (g : N ⟶ P) :
    f ≫ ringedKoszulCoefficientSMul O ρ b g =
      ringedKoszulCoefficientSMul O ρ b (f ≫ g) := by
  let : Linear (RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.homLinear O.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property
  exact Linear.comp_smul M N P f (ρ b) g

private theorem coefficient_one
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {M N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)}
    (f : M ⟶ N) : ringedKoszulCoefficientSMul O ρ 1 f = f := by
  let := SheafOfModules.homModule O.obj
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property M N
  change (ρ 1) • f = f
  rw [map_one, one_smul]

private theorem koszul_product_coefficient {A : Type z} [CommRing A]
    {r : ℕ} (a : Fin r → A) (m : ℕ) (q : ℤ) (I L : Finset (Fin r)) :
    (∏ i ∈ I, a i) * (∑ i ∈ I, if I.erase i = L then
      (if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
        (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1) else 0) =
    (∑ i ∈ I, if I.erase i = L then
      (if Even (q + (I.card : ℤ)) then (1 : A) else -1) *
        (-1 : A) ^ (I.filter (fun j ↦ j < i)).card * a i ^ (m + 1 + 1) else 0) *
      ∏ i ∈ L, a i := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : I.erase i = L
  · simp only [ite_eq_left h]
    rw [← h, ← Finset.prod_erase_mul _ _ hi, pow_succ]
    ring
  · simp only [ite_eq_right h, mul_zero, zero_mul]

private theorem pureTensor_naturality
    {E : Type*} [Category* E] [Preadditive E] [HasCountableCoproducts E]
    [MonoidalCategory E] [MonoidalPreadditive E]
    (Q : CochainComplex E ℤ) {K L : CochainComplex E ℤ} (f : K ⟶ L)
    (p n q : ℤ) (h : p + n = q) (β : MonoidalCategory.tensorUnit E ⟶ Q.X n) :
    (MonoidalCategory.rightUnitor (K.X p)).inv ≫ MonoidalCategory.tensorHom (𝟙 _) β ≫
      HomologicalComplex.ιMapBifunctor K Q (MonoidalCategory.curriedTensor E) (.up ℤ)
        p n q h ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 Q)
        (MonoidalCategory.curriedTensor E) (.up ℤ)).f q =
    f.f p ≫ (MonoidalCategory.rightUnitor (L.X p)).inv ≫
      MonoidalCategory.tensorHom (𝟙 _) β ≫
      HomologicalComplex.ιMapBifunctor L Q (MonoidalCategory.curriedTensor E) (.up ℤ)
        p n q h := by
  simp only [HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, MonoidalCategory.curriedTensor_obj_map,
    MonoidalCategory.curriedTensor_map_app, MonoidalCategory.whiskerLeft_id]
  rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]
  simp only [MonoidalCategory.tensorHom_comp_whiskerRight_assoc,
    MonoidalCategory.whiskerRight_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  exact congrArg (fun g ↦ (MonoidalCategory.rightUnitor (K.X p)).inv ≫
    MonoidalCategory.tensorHom (f.f p) β ≫ g)
    (Category.id_comp (HomologicalComplex.ιMapBifunctor L Q
      (MonoidalCategory.curriedTensor E) (.up ℤ) p n q h))

private theorem negativeKoszulSummand_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    {r : ℕ} (a : Fin r → A) (m : ℕ)
    {K L : ringedSiteComplex O} (f : K ⟶ L) (q : ℤ) (I : Finset (Fin r)) :
    ringedNegativeKoszulSummand O ρ a m K q I ≫
        ((ringedNegativeKoszulTensor O ρ a m).map f).f q =
      f.f (q + I.card) ≫ ringedNegativeKoszulSummand O ρ a m L q I := by
  let E := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let b : Fin r → (O.obj ⋙ forget CommRingCat).sections :=
    fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩
  let Q := ringedNegativeKoszul O r b m
  let β := ringedNegativeKoszulBasis O r b m I (-(I.card : ℤ))
  exact pureTensor_naturality Q f (q + I.card) (-(I.card : ℤ)) q (by omega) β

private theorem negativeKoszul_preserves_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin r → A) (m : ℕ)
    {K L : ringedSiteComplex O} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso ((ringedNegativeKoszulTensor O ρ a m).map f) := by
  let E := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} E := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let W := HomologicalComplex.quasiIso E (.up ℤ)
  have hfactor (b : (O.obj ⋙ forget CommRingCat).sections) :
      W.kFlat (ringedNegativeKoszulFactor O b m) := by
    let F := ringedNegativeKoszulFactor O b m
    have hzero (n : ℤ) (hn : n ≠ -1) (hn' : n ≠ 0) : IsZero (F.X n) :=
      HomologicalComplex.isZero_double_X _ _ n hn hn'
    have : F.IsStrictlyGE (-1) := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact hzero n (by omega) (by omega)
    have : F.IsStrictlyLE 0 := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro n hn
      exact hzero n (by omega) (by omega)
    apply CochainComplex.kFlat_of_bounded_of_flat F (-1) 0
    intro n
    by_cases hn : n = -1
    · subst n
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.doubleXIso₀ _ _).symm (ObjectProperty.prop_unit _)
    by_cases hn' : n = 0
    · subst n
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.doubleXIso₁ _ _ (by decide)).symm (ObjectProperty.prop_unit _)
    exact ObjectProperty.flat_of_isZero (hzero n hn hn')
  have hnegative (s : ℕ) (b : Fin s → (O.obj ⋙ forget CommRingCat).sections) :
      W.kFlat (ringedNegativeKoszul O s b m) := by
    induction s with
    | zero => exact ObjectProperty.prop_unit _
    | succ s ih =>
      exact ObjectProperty.prop_tensor (hfactor (b 0)) (ih (fun i ↦ b i.succ))
  exact (hnegative r (fun i ↦ ⟨(ρ (a i)).val, (ρ (a i)).property⟩)).whiskerRight hf

/-- The ordered negative Koszul tensors have normalized finite subset coordinates,
scalar-diagonal transitions, compatible empty-coordinate inclusions, and preserve
quasi-isomorphisms. No countable product, fibre, localization, or coefficient functor
comparison occurs in this finite statement.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, bounded finite free Koszul calculation;
steps 1--3 and 7 of lem-cbc-exact-linear-koszul-fiber.
(auxiliary; not a blueprint node).

Proof in words: induct on the number of ordered factors. The empty tensor is O[0]
and its tensor with K is K by the right unitor. Split a subset into whether it contains
the first index and the subset of successor indices. The two supported degrees of the
first factor and distribution of tensor over finite direct sums identify the next
ordered tensor with the direct sum indexed by those subsets. The inclusion into a
subset coordinate is the inverse unitor, tensor of the specified basis maps, and the
total tensor inclusion; these are exactly ringedNegativeKoszulSummand. Multiplication
in the rank-one factors supplies inverse coordinates. Naturality of the unitors and
total tensor inclusions makes coefficient maps diagonal in these coordinates.
The first total differential is d_K. The differential of the ith negative factor
has coefficient a_i^(m+1), preceded by one sign for each earlier negative factor and
by (-1)^(q+|I|) for the coefficient degree. This is exactly the displayed erased-index
matrix, including all equality transports. Conjugate the diagonal scalar product over
I by these coordinates to construct the transition. Its chain equation reduces to
(product over I of a_j) a_i^(m+1) = a_i^(m+2) (product over I.erase i of a_j).
The empty-coordinate inclusions are chain maps and commute with transitions because
the empty product is one. Filter the tensor by subset cardinality at most k.
The kth quotient is the finite direct sum of reindexed copies of K with |I|=k,
whose differential is d_K; a degreewise sign twist identifies them with the usual
shifts. This filtration is finite and degreewise split. A quasi-isomorphism of K
induces quasi-isomorphisms on the quotients; the long exact homology sequences and
induction give a quasi-isomorphism on each tensor. This works for unbounded K.
For r=0 only the empty coordinate occurs. For r=1 the negative summand has
coefficient (-1)^(q+1) a_0^(m+1) and transition a_0. No inverse scalar is used, so
zero and unit scalars, zero rings, and empty sites are all allowed. -/
theorem exists_ringedSignedKoszulFiniteCoordinates
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) {A : Type z} [CommRing A]
    (ρ : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (a : Fin r → A) :
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  ∃ (coordinates : ∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ),
    ((ringedNegativeKoszulTensor O ρ a m).obj K).X q ≅
      ⨁ fun I : Finset (Fin r) ↦ K.X (q + I.card))
    (step : ∀ m : ℕ, ringedNegativeKoszulTensor O ρ a (m + 1) ⟶
      ringedNegativeKoszulTensor O ρ a m)
    (inclusion : ∀ m : ℕ, 𝟭 (ringedSiteComplex O) ⟶ (ringedNegativeKoszulTensor O ρ a) m),
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
    (∀ (m : ℕ) {K L : ringedSiteComplex O} (f : K ⟶ L)
      (q : ℤ) (I P : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates m K q).inv ≫ (((ringedNegativeKoszulTensor O ρ a) m).map f).f q ≫
        (coordinates m L q).hom ≫ biproduct.π _ P =
      if h : I = P then f.f (q + I.card) ≫
        (L.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
      (I L : Finset (Fin r)),
    biproduct.ι _ I ≫ (coordinates (m + 1) K q).inv ≫ ((step m).app K).f q ≫
        (coordinates m K q).hom ≫ biproduct.π _ L =
      if h : I = L then ringedKoszulCoefficientSMul O ρ (∏ i ∈ I, a i)
        (K.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ)
      (I : Finset (Fin r)),
    ((inclusion m).app K).f q ≫ (coordinates m K q).hom ≫ biproduct.π _ I =
      if h : q = q + (I.card : ℤ) then (K.XIsoOfEq h).hom else 0) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)),
      biproduct.ι _ I ≫ (coordinates m K q).inv =
        ringedNegativeKoszulSummand O ρ a m K q I) ∧
    (∀ (m : ℕ) (K : ringedSiteComplex O),
      (inclusion (m + 1)).app K ≫ (step m).app K = (inclusion m).app K) ∧
    (∀ (m : ℕ) {K L : ringedSiteComplex O} (f : K ⟶ L),
      QuasiIso f → QuasiIso ((ringedNegativeKoszulTensor O ρ a m).map f)) := by
  classical
  let := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let : Linear (RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.homLinear O.obj
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).property
  obtain ⟨c, hd, hn⟩ := exists_ringedSignedKoszulTensorCoordinates O ρ r a
  have hm : ∀ (m : ℕ) {K L : ringedSiteComplex O} (f : K ⟶ L)
      (q : ℤ) (I P : Finset (Fin r)),
    biproduct.ι _ I ≫ (c m K q).inv ≫ (((ringedNegativeKoszulTensor O ρ a) m).map f).f q ≫
        (c m L q).hom ≫ biproduct.π _ P =
      if h : I = P then f.f (q + I.card) ≫
        (L.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
      else 0 := by
    intro m K L f q I P
    simp only [← Category.assoc, hn, negativeKoszulSummand_naturality]
    rw [← hn m L q I]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π]
    by_cases h : I = P
    · subst P
      simp
    · simp [h]
  let T := ringedNegativeKoszulTensor O ρ a
  let p (I : Finset (Fin r)) : A := ∏ i ∈ I, a i
  let t (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
      ((T (m + 1)).obj K).X q ⟶ ((T m).obj K).X q :=
    (c (m + 1) K q).hom ≫
      biproduct.map (fun I ↦ ringedKoszulCoefficientSMul O ρ (p I) (𝟙 (K.X (q + I.card)))) ≫
        (c m K q).inv
  have htrow (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)) :
      (biproduct.ι _ I ≫ (c (m + 1) K q).inv) ≫ t m K q =
        ringedKoszulCoefficientSMul O ρ (p I) (biproduct.ι _ I ≫ (c m K q).inv) := by
    simp only [t, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_map_assoc]
    rw [coefficient_smul_comp, Category.id_comp]
  have htcol (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)) :
      t m K q ≫ (c m K q).hom ≫ biproduct.π _ I =
        ringedKoszulCoefficientSMul O ρ (p I)
          ((c (m + 1) K q).hom ≫ biproduct.π _ I) := by
    simp only [t, Category.assoc, Iso.inv_hom_id_assoc, biproduct.map_π]
    rw [coefficient_comp_smul, coefficient_comp_smul, Category.comp_id]
  have hscale (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I L : Finset (Fin r)) :
      ringedKoszulCoefficientSMul O ρ (p I)
        (biproduct.ι _ I ≫ (c m K q).inv ≫ ((T m).obj K).d q (q + 1) ≫
          (c m K (q + 1)).hom ≫ biproduct.π _ L) =
      ringedKoszulCoefficientSMul O ρ (p L)
        (biproduct.ι _ I ≫ (c (m + 1) K q).inv ≫ ((T (m + 1)).obj K).d q (q + 1) ≫
          (c (m + 1) K (q + 1)).hom ≫ biproduct.π _ L) := by
    simp only [T, hd, ringedKoszulCoefficientSMul, smul_add]
    apply congrArg₂ (· + ·)
    · by_cases h : I = L
      · subst L
        rfl
      · simp only [ite_eq_right h, smul_zero]
    · by_cases h : q + (I.card : ℤ) = (q + 1) + (L.card : ℤ)
      · simp only [dite_eq_left h, smul_smul, ← map_mul]
        apply congrArg (fun b : A ↦ ringedKoszulCoefficientSMul O ρ b (K.XIsoOfEq h).hom)
        exact (koszul_product_coefficient a m q I L).trans (mul_comm _ _)
      · simp only [dite_eq_right h, smul_zero]
  have htcomm (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
      t m K q ≫ ((T m).obj K).d q (q + 1) =
        ((T (m + 1)).obj K).d q (q + 1) ≫ t m K (q + 1) := by
    apply (cancel_epi (c (m + 1) K q).inv).1
    apply (cancel_mono (c m K (q + 1)).hom).1
    apply biproduct.hom_ext'
    intro I
    apply biproduct.hom_ext
    intro L
    simp only [← Category.assoc, htrow, ringedKoszulCoefficientSMul, Linear.smul_comp]
    simp only [Category.assoc, htcol, ringedKoszulCoefficientSMul, Linear.comp_smul]
    exact hscale m K q I L
  let step (m : ℕ) : T (m + 1) ⟶ T m :=
    { app K :=
        { f := t m K
          comm' := by
            intro q q' h
            have hq : q' = q + 1 := h.symm
            subst q'
            exact htcomm m K q }
      naturality := by
        intro K L f
        apply HomologicalComplex.hom_ext
        intro q
        change ((T (m + 1)).map f).f q ≫ t m L q =
          t m K q ≫ ((T m).map f).f q
        apply (cancel_epi (c (m + 1) K q).inv).1
        apply (cancel_mono (c m L q).hom).1
        apply biproduct.hom_ext'
        intro I
        apply biproduct.hom_ext
        intro P
        simp only [← Category.assoc, htrow, ringedKoszulCoefficientSMul, Linear.smul_comp]
        simp only [Category.assoc, htcol, ringedKoszulCoefficientSMul, Linear.comp_smul]
        simp only [T, hm]
        by_cases h : I = P
        · subst P
          rfl
        · simp only [dite_eq_right h, smul_zero] }
  have hstep (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I L : Finset (Fin r)) :
      biproduct.ι _ I ≫ (c (m + 1) K q).inv ≫ ((step m).app K).f q ≫
          (c m K q).hom ≫ biproduct.π _ L =
        if h : I = L then ringedKoszulCoefficientSMul O ρ (p I)
          (K.XIsoOfEq (congrArg (fun V : Finset (Fin r) ↦ q + (V.card : ℤ)) h)).hom
        else 0 := by
    change biproduct.ι _ I ≫ (c (m + 1) K q).inv ≫ t m K q ≫
      (c m K q).hom ≫ biproduct.π _ L = _
    simp only [← Category.assoc, htrow, ringedKoszulCoefficientSMul, Linear.smul_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π]
    by_cases h : I = L
    · subst L
      simp
    · simp [h]
  let e (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) : K.X q ⟶ ((T m).obj K).X q :=
    (K.XIsoOfEq (by simp : q = q + ((∅ : Finset (Fin r)).card : ℤ))).hom ≫
      biproduct.ι (fun I : Finset (Fin r) ↦ K.X (q + I.card)) ∅ ≫ (c m K q).inv
  have hecomm (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) :
      e m K q ≫ ((T m).obj K).d q (q + 1) = K.d q (q + 1) ≫ e m K (q + 1) := by
    apply (cancel_mono (c m K (q + 1)).hom).1
    apply biproduct.hom_ext
    intro I
    have hdeg : q ≠ q + 1 + (I.card : ℤ) := by omega
    by_cases hI : I = ∅
    · subst I
      simpa [e, Category.assoc, ringedKoszulCoefficientSMul, map_zero, zero_smul] using
        congrArg (fun g ↦
          (K.XIsoOfEq (by simp : q = q + ((∅ : Finset (Fin r)).card : ℤ))).hom ≫ g)
          (hd m K q ∅ ∅)
    · simpa [e, Category.assoc, hI, Ne.symm hI, hdeg] using
        congrArg (fun g ↦
          (K.XIsoOfEq (by simp : q = q + ((∅ : Finset (Fin r)).card : ℤ))).hom ≫ g)
          (hd m K q ∅ I)
  let inclusion (m : ℕ) : 𝟭 (ringedSiteComplex O) ⟶ T m :=
    { app K :=
        { f := e m K
          comm' := by
            intro q q' h
            have hq : q' = q + 1 := h.symm
            subst q'
            exact hecomm m K q }
      naturality := by
        intro K L f
        apply HomologicalComplex.hom_ext
        intro q
        change f.f q ≫ e m L q = e m K q ≫ ((T m).map f).f q
        apply (cancel_mono (c m L q).hom).1
        apply biproduct.hom_ext
        intro I
        by_cases hI : I = ∅
        · subst I
          simpa [e, Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality_assoc] using
            (congrArg (fun g ↦
              (K.XIsoOfEq (by simp : q = q + ((∅ : Finset (Fin r)).card : ℤ))).hom ≫ g)
              (hm m f q ∅ ∅)).symm
        · simpa [e, Category.assoc, hI, Ne.symm hI] using
            (congrArg (fun g ↦
              (K.XIsoOfEq (by simp : q = q + ((∅ : Finset (Fin r)).card : ℤ))).hom ≫ g)
              (hm m f q ∅ I)).symm }
  have hecol (m : ℕ) (K : ringedSiteComplex O) (q : ℤ) (I : Finset (Fin r)) :
      ((inclusion m).app K).f q ≫ (c m K q).hom ≫ biproduct.π _ I =
        if h : q = q + (I.card : ℤ) then (K.XIsoOfEq h).hom else 0 := by
    change e m K q ≫ (c m K q).hom ≫ biproduct.π _ I = _
    by_cases hI : I = ∅
    · subst I
      simp [e, Category.assoc]
    · have hcard : I.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
      have hdeg : q ≠ q + (I.card : ℤ) := by omega
      simp [e, Category.assoc, Ne.symm hI, hdeg]
  refine ⟨c, step, inclusion, hd, hm, hstep, hecol, hn, ?_, ?_⟩
  · intro m K
    apply HomologicalComplex.hom_ext
    intro q
    change e (m + 1) K q ≫ t m K q = e m K q
    have htr := htrow m K q ∅
    simp only [p, Finset.prod_empty, coefficient_one] at htr
    simpa only [e, Category.assoc] using
      congrArg (fun g ↦
        (K.XIsoOfEq (by simp : q = q + ((∅ : Finset (Fin r)).card : ℤ))).hom ≫ g)
        htr
  · intro m K L f hf
    exact negativeKoszul_preserves_quasiIso O ρ r a m f hf

end CategoryTheory
