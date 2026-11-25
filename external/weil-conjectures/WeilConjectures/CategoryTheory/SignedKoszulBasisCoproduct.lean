/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel

/-!
# Degreewise basis coproduct for the negative Koszul tensor

This isolates the finite graded basis calculation from the coefficient-complex tensor.
Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

open MonoidalCategory

private theorem basis_one_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (b : Fin 1 → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    (I : Finset (Fin 1)) (n : ℤ) (hn : n = -(I.card : ℤ)) :
    IsIso (ringedNegativeKoszulBasis O 1 b m I n) := by
  classical
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let F := ringedNegativeKoszulFactor O (b 0) m
  let e := HomologicalComplex.rightUnitor F
  have hI : I = ∅ ∨ I = {0} := Finset.subset_singleton_iff.mp (by
    intro i hi
    simp [Subsingleton.elim i (0 : Fin 1)])
  rcases hI with rfl | rfl
  · simp only [Finset.card_empty, Int.natCast_zero, neg_zero] at hn
    subst n
    have he : e.inv.f 0 = (ρ_ (F.X 0)).inv ≫
        (F.X 0) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ _)).inv ≫
          CochainComplex.ιMapBifunctor F (ringedSiteRingComplex O)
            (curriedTensor _) 0 0 0 (by omega) :=
      HomologicalComplex.rightUnitor'_inv F 0
    have hb : ringedNegativeKoszulBasis O 1 b m ∅ 0 =
        ringedNegativeKoszulFactorBasis O (b 0) m 0 ≫ e.inv.f 0 := by
      rw [he]
      change (λ_ _).inv ≫
        (ringedNegativeKoszulFactorBasis O (b 0) m 0 ⊗ₘ
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ _)).inv) ≫
            CochainComplex.ιMapBifunctor F (ringedSiteRingComplex O)
              (curriedTensor _) 0 0 0 (by omega) = _
      rw [rightUnitor_inv_naturality_assoc, unitors_inv_equal]
      simp only [tensorHom_def, Category.assoc]
      rfl
    rw [hb]
    have : IsIso (ringedNegativeKoszulFactorBasis O (b 0) m 0) := by
      simp only [ringedNegativeKoszulFactorBasis, show (0 : ℤ) ≠ -1 by omega,
        ↓reduceDIte, eqToHom_refl, Category.comp_id]
      infer_instance
    infer_instance
  · simp only [Finset.card_singleton, Int.natCast_one] at hn
    subst n
    have he : e.inv.f (-1) = (ρ_ (F.X (-1))).inv ≫
        (F.X (-1)) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ _)).inv ≫
          CochainComplex.ιMapBifunctor F (ringedSiteRingComplex O)
            (curriedTensor _) (-1) 0 (-1) (by omega) :=
      HomologicalComplex.rightUnitor'_inv F (-1)
    have hb : ringedNegativeKoszulBasis O 1 b m {0} (-1) =
        ringedNegativeKoszulFactorBasis O (b 0) m (-1) ≫ e.inv.f (-1) := by
      rw [he]
      change (λ_ _).inv ≫
        (ringedNegativeKoszulFactorBasis O (b 0) m (-1) ⊗ₘ
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ _)).inv) ≫
            CochainComplex.ιMapBifunctor F (ringedSiteRingComplex O)
              (curriedTensor _) (-1) 0 (-1) (by omega) = _
      rw [rightUnitor_inv_naturality_assoc, unitors_inv_equal]
      simp only [tensorHom_def, Category.assoc]
      rfl
    rw [hb]
    have : IsIso (ringedNegativeKoszulFactorBasis O (b 0) m (-1)) := by
      simp only [ringedNegativeKoszulFactorBasis, ↓reduceDIte, eqToHom_refl,
        Category.comp_id]
      infer_instance
    infer_instance

/-- The one-factor negative Koszul basis has the degreewise coproduct property.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
one two-term factor.  Proof: split on the integer degree.  In degrees `-1` and `0`
the corresponding factor basis map is an isomorphism from the tensor unit, and in every
other degree the factor is zero and the indexing subtype is empty.  The coproduct
universal property is therefore the isomorphism case or the zero-object case.
(auxiliary; not a blueprint node).
-/
theorem isColimit_ringedNegativeKoszulBasis_base
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (b : Fin 1 → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n : ℤ) :
    Nonempty (IsColimit (Cofan.mk
      ((ringedNegativeKoszul O 1 b m).X n)
      (fun I : {I : Finset (Fin 1) // n = -(I.card : ℤ)} ↦
        ringedNegativeKoszulBasis O 1 b m I.1 n))) := by
  classical
  let S := {I : Finset (Fin 1) // n = -(I.card : ℤ)}
  have sets (I : Finset (Fin 1)) : I = ∅ ∨ I = {0} :=
    Finset.subset_singleton_iff.mp (by
      intro i hi
      simp [Subsingleton.elim i (0 : Fin 1)])
  have : Subsingleton S := ⟨by
    intro I K
    apply Subtype.ext
    have hi := I.property
    have hk := K.property
    rcases sets I.val with hi' | hi' <;>
      rcases sets K.val with hk' | hk' <;> simp_all⟩
  by_cases hs : Nonempty S
  · let i : S := Classical.choice hs
    have : IsIso (ringedNegativeKoszulBasis O 1 b m i.val n) :=
      basis_one_iso O b m i.val n i.property
    refine ⟨Cofan.IsColimit.mk _
      (fun s ↦ inv (ringedNegativeKoszulBasis O 1 b m i.val n) ≫ s.inj i)
      (fun s j ↦ ?_) (fun s f hf ↦ ?_)⟩
    · obtain rfl := Subsingleton.elim j i
      simp
    · simpa [← cancel_epi (ringedNegativeKoszulBasis O 1 b m i.val n)] using hf i
  · have hn0 : n ≠ 0 := fun hn ↦ hs ⟨⟨∅, by simpa using hn⟩⟩
    have hn1 : n ≠ -1 := fun hn ↦ hs ⟨⟨{0}, by simpa using hn⟩⟩
    let := SheafOfModules.isGrothendieckAbelian
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := Classical.choice (SheafOfModules.tensorClosed O).2.1
    let F := ringedNegativeKoszulFactor O (b 0) m
    let e := (HomologicalComplex.eval _ (.up ℤ) n).mapIso
      (HomologicalComplex.rightUnitor F)
    have hzF : IsZero (F.X n) :=
      HomologicalComplex.isZero_double_X _ _ n hn1 hn0
    have hz : IsZero ((ringedNegativeKoszul O 1 b m).X n) := hzF.of_iso e
    refine ⟨Cofan.IsColimit.mk _ (fun _ ↦ 0) (fun _ j ↦ ?_)
      (fun _ _ _ ↦ hz.eq_of_src _ _)⟩
    exact (hs ⟨j⟩).elim

private def extendSubset (k : ℕ) (t : Bool) (I : Finset (Fin k)) :
    Finset (Fin (k + 1)) :=
  if t then insert 0 (I.map (Fin.succEmb k)) else I.map (Fin.succEmb k)

private theorem extendSubset_zero (k : ℕ) (t : Bool) (I : Finset (Fin k)) :
    (0 : Fin (k + 1)) ∈ extendSubset k t I ↔ t = true := by
  classical
  cases t <;> simp [extendSubset, Finset.mem_map, Fin.succEmb]

private theorem extendSubset_tail (k : ℕ) (t : Bool) (I : Finset (Fin k)) :
    (extendSubset k t I).preimage Fin.succ
      (fun _ _ _ _ h ↦ Fin.succ_injective k h) = I := by
  classical
  ext i
  cases t <;> simp [extendSubset, Fin.succEmb]

private theorem extendSubset_card (k : ℕ) (t : Bool) (I : Finset (Fin k)) :
    (extendSubset k t I).card = I.card + if t then 1 else 0 := by
  classical
  have h : (0 : Fin (k + 1)) ∉ I.map (Fin.succEmb k) := by
    simp [Finset.mem_map, Fin.succEmb]
  cases t <;> simp [extendSubset, h]

private theorem extendSubset_recover (k : ℕ) (I : Finset (Fin (k + 1))) :
    extendSubset k (decide ((0 : Fin (k + 1)) ∈ I))
      (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective k h)) = I := by
  classical
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [extendSubset_zero]
  · by_cases h : (0 : Fin (k + 1)) ∈ I <;>
      simp [extendSubset, h, Fin.succEmb]

/-- The successor step for the recursive negative Koszul basis coproduct.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul,
finite free tensor calculation.  Proof: tensor the tail coproducts supplied by `h`
with the two degree-supported basis maps of the head factor.  The finite coproduct
preservation of tensor identifies the resulting legs with the recursive maps
`ringedNegativeKoszulBasis`; reindexing by adjoining zero or applying `Fin.succ`
identifies the resulting pair of indices with subsets of `Fin (r+2)` having the
specified cardinality.  The corresponding coproduct transport is the displayed
cofan.
(auxiliary; not a blueprint node).
-/
theorem isColimit_ringedNegativeKoszulBasis_step
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin (r + 2) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n : ℤ)
    (h : ∀ n : ℤ, Nonempty (IsColimit (Cofan.mk
      ((ringedNegativeKoszul O (r + 1) (fun i ↦ b i.succ) m).X n)
      (fun I : {I : Finset (Fin (r + 1)) // n = -(I.card : ℤ)} ↦
        ringedNegativeKoszulBasis O (r + 1) (fun i ↦ b i.succ) m I.1 n)))) :
    Nonempty (IsColimit (Cofan.mk
      ((ringedNegativeKoszul O (r + 2) b m).X n)
      (fun I : {I : Finset (Fin (r + 2)) // n = -(I.card : ℤ)} ↦
        ringedNegativeKoszulBasis O (r + 2) b m I.1 n))) := by
  classical
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let M := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let F := ringedNegativeKoszulFactor O (b 0) m
  let Q := ringedNegativeKoszul O (r + 1) (fun i ↦ b i.succ) m
  let B (q : ℤ) (I : {I : Finset (Fin (r + 1)) // q = -(I.card : ℤ)}) :=
    ringedNegativeKoszulBasis O (r + 1) (fun i ↦ b i.succ) m I.1 q
  let hc (p q : ℤ) :=
    Cofan.isColimitMapCoconeEquiv (tensorLeft (F.X p)) _
      (Cofan.mk (Q.X q) (B q))
      (isColimitOfPreserves (tensorLeft (F.X p)) (h q).some)
  have hfi (p : ℤ) (hp : p = -1 ∨ p = 0) :
      IsIso (ringedNegativeKoszulFactorBasis O (b 0) m p) := by
    rcases hp with rfl | rfl
    · simp only [ringedNegativeKoszulFactorBasis, ↓reduceDIte, eqToHom_refl,
        Category.comp_id]
      infer_instance
    · simp only [ringedNegativeKoszulFactorBasis, show (0 : ℤ) ≠ -1 by omega,
        ↓reduceDIte, eqToHom_refl, Category.comp_id]
      infer_instance
  let δ (p : ℤ) (hp : p = -1 ∨ p = 0) : M ≅ F.X p ⊗ M := by
    let := hfi p hp
    exact (λ_ M).symm ≪≫ (asIso (ringedNegativeKoszulFactorBasis O (b 0) m p) ⊗ᵢ
      Iso.refl M)
  have hδ (p : ℤ) (hp : p = -1 ∨ p = 0) :
      (δ p hp).hom = (λ_ M).inv ≫
        (ringedNegativeKoszulFactorBasis O (b 0) m p ⊗ₘ 𝟙 M) := rfl
  let idx (p q : ℤ) (hp : p = -1 ∨ p = 0) (hpq : p + q = n)
      (I : {I : Finset (Fin (r + 1)) // q = -(I.card : ℤ)}) :
      {I : Finset (Fin (r + 2)) // n = -(I.card : ℤ)} :=
    ⟨extendSubset (r + 1) (decide (p = -1)) I.val, by
      have hi := I.property
      have ht := extendSubset_card (r + 1) (decide (p = -1)) I.val
      rcases hp with rfl | rfl <;> dsimp at ht <;> omega⟩
  have hb (I : Finset (Fin (r + 2))) (p : ℤ) (hp : p = -1 ∨ p = 0)
      (hh : (if (0 : Fin (r + 2)) ∈ I then (-1 : ℤ) else 0) = p) :
      ringedNegativeKoszulBasis O (r + 2) b m I n =
        (δ p hp).hom ≫ (tensorLeft (F.X p)).map
          (ringedNegativeKoszulBasis O (r + 1) (fun i ↦ b i.succ) m
            (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective (r + 1) h))
            (n - p)) ≫
          CochainComplex.ιMapBifunctor F Q (curriedTensor _) p (n - p) n (by omega) := by
    subst p
    rw [hδ _ hp]
    change (λ_ M).inv ≫
      (ringedNegativeKoszulFactorBasis O (b 0) m
          (if (0 : Fin (r + 2)) ∈ I then -1 else 0) ⊗ₘ
        ringedNegativeKoszulBasis O (r + 1) (fun i ↦ b i.succ) m
          (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective (r + 1) h))
          (n - if (0 : Fin (r + 2)) ∈ I then -1 else 0)) ≫
        CochainComplex.ιMapBifunctor F Q (curriedTensor _)
          (if (0 : Fin (r + 2)) ∈ I then -1 else 0)
          (n - if (0 : Fin (r + 2)) ∈ I then -1 else 0) n (by omega) = _
    simp only [tensorLeft, curriedTensor_obj_map, tensorHom_def, whiskerLeft_id,
      Category.comp_id, Category.assoc]
    rfl
  let d (s : Cofan (fun _ : {I : Finset (Fin (r + 2)) // n = -(I.card : ℤ)} ↦ M))
      (p q : ℤ) (hpq : p + q = n) : F.X p ⊗ Q.X q ⟶ s.pt :=
    if hp : p = -1 ∨ p = 0 then
      (hc p q).desc (Cofan.mk s.pt (fun I ↦ (δ p hp).inv ≫ s.inj (idx p q hp hpq I)))
    else 0
  refine ⟨Cofan.IsColimit.mk _ (fun s ↦
    HomologicalComplex.mapBifunctorDesc (K₁ := F) (K₂ := Q)
      (F := curriedTensor _) (c := ComplexShape.up ℤ)
      (fun p q hpq ↦ d s p q hpq)) ?_ ?_⟩
  · intro s I
    let p : ℤ := if (0 : Fin (r + 2)) ∈ I.val then -1 else 0
    let T := I.val.preimage Fin.succ
      (fun _ _ _ _ h ↦ Fin.succ_injective (r + 1) h)
    have hp : p = -1 ∨ p = 0 := by dsimp [p]; split_ifs <;> simp
    have hcard : I.val.card = T.card + if (0 : Fin (r + 2)) ∈ I.val then 1 else 0 := by
      have ht := congrArg Finset.card (extendSubset_recover (r + 1) I.val)
      rw [extendSubset_card] at ht
      simpa [T] using ht.symm
    have ht : n - p = -(T.card : ℤ) := by
      have hi := I.property
      dsimp [p]
      split_ifs at * <;> omega
    have hidx : idx p (n - p) hp (by omega) ⟨T, ht⟩ = I := by
      apply Subtype.ext
      change extendSubset (r + 1) (decide (p = -1)) T = I.val
      have hh : decide (p = -1) = decide ((0 : Fin (r + 2)) ∈ I.val) := by
        dsimp [p]
        split_ifs <;> simp_all
      rw [hh]
      exact extendSubset_recover (r + 1) I.val
    change ringedNegativeKoszulBasis O (r + 2) b m I.val n ≫ _ = _
    rw [hb I.val p hp rfl, Category.assoc, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    have hfac := (hc p (n - p)).fac
      (Cofan.mk s.pt (fun L ↦ (δ p hp).inv ≫
        s.inj (idx p (n - p) hp (by omega) L))) ⟨⟨T, ht⟩⟩
    simpa only [d, dite_eq_left hp, tensorLeft, Category.assoc, Cofan.mk_ι_app,
      cofan_mk_inj, Discrete.functor_obj, Iso.hom_inv_id_assoc, hidx] using
      congrArg ((δ p hp).hom ≫ ·) hfac
  · intro s f hf
    apply HomologicalComplex.mapBifunctor.hom_ext (K₁ := F) (K₂ := Q)
      (F := curriedTensor _) (c := ComplexShape.up ℤ)
    intro p q hpq
    change p + q = n at hpq
    have hq : q = n - p := by omega
    subst q
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    by_cases hp : p = -1 ∨ p = 0
    · apply (hc p (n - p)).hom_ext
      rintro ⟨L, hL⟩
      apply (cancel_epi (δ p hp).hom).1
      let I := idx p (n - p) hp hpq ⟨L, hL⟩
      have hh : (if (0 : Fin (r + 2)) ∈ I.val then (-1 : ℤ) else 0) = p := by
        change (if (0 : Fin (r + 2)) ∈
          extendSubset (r + 1) (decide (p = -1)) L then (-1 : ℤ) else 0) = p
        rcases hp with rfl | rfl <;> simp [extendSubset_zero]
      have ht : I.val.preimage Fin.succ
          (fun _ _ _ _ h ↦ Fin.succ_injective (r + 1) h) = L :=
        extendSubset_tail (r + 1) (decide (p = -1)) L
      have hi := hf I
      change ringedNegativeKoszulBasis O (r + 2) b m I.val n ≫ f = s.inj I at hi
      rw [hb I.val p hp hh] at hi
      simp only [ht, Category.assoc] at hi
      have hfac := (hc p (n - p)).fac
        (Cofan.mk s.pt (fun T ↦ (δ p hp).inv ≫ s.inj (idx p (n - p) hp hpq T))) ⟨⟨L, hL⟩⟩
      change (δ p hp).hom ≫ (tensorLeft (F.X p)).map (B (n - p) ⟨L, hL⟩) ≫
          CochainComplex.ιMapBifunctor F Q (curriedTensor _) p (n - p) n hpq ≫ f =
        (δ p hp).hom ≫ (tensorLeft (F.X p)).map (B (n - p) ⟨L, hL⟩) ≫ d s p (n - p) hpq
      exact hi.trans (by
        simpa only [d, dite_eq_left hp, tensorLeft, Category.assoc, Cofan.mk_ι_app,
          cofan_mk_inj, Discrete.functor_obj, Iso.hom_inv_id_assoc] using
          (congrArg ((δ p hp).hom ≫ ·) hfac).symm)
    · have hzF : IsZero (F.X p) :=
        HomologicalComplex.isZero_double_X _ _ p (fun h ↦ hp (Or.inl h))
          (fun h ↦ hp (Or.inr h))
      have hz : IsZero (F.X p ⊗ Q.X (n - p)) :=
        ((curriedTensor _).flip.obj (Q.X (n - p))).map_isZero hzF
      exact hz.eq_of_src _ _

/-- The recursive negative Koszul basis is a degreewise coproduct.  The source of a
subset is the tensor unit in its supported degree and the zero object otherwise.

Source: Stacks Project, algebraization.tex, Tag 0A0E, the finite free negative Koszul
calculation.  Proof: induction on the ordered tensor length, using the one-factor base
case and the successor tensor step above.  This proves the universal property degree by
degree, including length one, zero rings, and empty sites.
(auxiliary; not a blueprint node).
-/
theorem isColimit_ringedNegativeKoszulBasis_succ
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n : ℤ) :
    Nonempty (IsColimit (Cofan.mk
      ((ringedNegativeKoszul O (r + 1) b m).X n)
      (fun I : {I : Finset (Fin (r + 1)) // n = -(I.card : ℤ)} ↦
        ringedNegativeKoszulBasis O (r + 1) b m I.1 n))) := by
  induction r generalizing m n with
  | zero =>
      exact isColimit_ringedNegativeKoszulBasis_base O b m n
  | succ r ih =>
      apply isColimit_ringedNegativeKoszulBasis_step O r b m n
      intro q
      exact ih (fun i ↦ b i.succ) m q

end CategoryTheory
