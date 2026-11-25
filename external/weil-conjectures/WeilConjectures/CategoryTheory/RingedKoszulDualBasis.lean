/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ExteriorKoszulBasisDifferential
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedNegativeKoszulExteriorDifferential
import WeilConjectures.CategoryTheory.SignedKoszulBasisCoproduct

/-! # Finite subset coordinates for the actual dual Koszul tower

Source: Stacks Project, More on Algebra, Tag 0664; Algebraization, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem negative_basis_isColimit
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) (q : ℤ) :
    Nonempty (IsColimit (Cofan.mk ((ringedNegativeKoszul O r s n).X q)
      (fun I : exteriorKoszulIndex r q ↦ ringedNegativeKoszulBasis O r s n I.1 q))) := by
  classical
  cases r with
  | succ r => exact isColimit_ringedNegativeKoszulBasis_succ O r s n q
  | zero =>
    by_cases hq : q = 0
    · subst q
      let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O))
      have hb (I : exteriorKoszulIndex 0 0) :
          ringedNegativeKoszulBasis O 0 s n I.1 0 = e.inv := by
        simp [ringedNegativeKoszulBasis, e]
      refine ⟨Cofan.IsColimit.mk _ (fun c ↦ e.hom ≫ c.inj ⟨∅, rfl⟩) ?_ ?_⟩
      · intro c I
        change ringedNegativeKoszulBasis O 0 s n I.1 0 ≫ _ = _
        rw [hb, e.inv_hom_id_assoc]
        congr 1
        exact Subtype.ext (Subsingleton.elim _ _)
      · intro c f hf
        have h := hf ⟨∅, rfl⟩
        change ringedNegativeKoszulBasis O 0 s n ∅ 0 ≫ f = _ at h
        rw [hb ⟨∅, rfl⟩] at h
        simpa only [← Category.assoc, e.hom_inv_id, Category.id_comp] using
          congrArg (e.hom ≫ ·) h
    · have hz : IsZero ((ringedNegativeKoszul O 0 s n).X q) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq
      refine ⟨Cofan.IsColimit.mk _ (fun _ ↦ 0) ?_ ?_⟩
      · intro c I
        have hi := I.2
        have he : I.1 = ∅ := Subsingleton.elim _ _
        simp only [he, Finset.card_empty, Int.natCast_zero, neg_zero] at hi
        exact (hq hi).elim
      · intro c f hf
        exact hz.eq_of_src _ _

private theorem unit_tensor_scalars
    {E : Type*} [Category E] [MonoidalCategory E]
    (f g : End (MonoidalCategory.tensorUnit E)) :
    (MonoidalCategory.leftUnitor (MonoidalCategory.tensorUnit E)).inv ≫
      MonoidalCategory.tensorHom f.asHom g.asHom =
    (f * g).asHom ≫ (MonoidalCategory.leftUnitor (MonoidalCategory.tensorUnit E)).inv := by
  rw [MonoidalCategory.leftUnitor_inv_comp_tensorHom,
    MonoidalCategory.unitors_inv_equal, ← MonoidalCategory.rightUnitor_inv_naturality]
  simp only [End.mul_asHom, Category.assoc]

private theorem subset_prod_succ {A : Type w} [CommRing A] (r : ℕ)
    (a : Fin (r + 1) → A) (I : Finset (Fin (r + 1))) :
    (∏ i ∈ I, a i) = (if (0 : Fin (r + 1)) ∈ I then a 0 else 1) *
      ∏ i ∈ I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective r h), a i.succ := by
  classical
  have h (k : ℕ) (J : Finset (Fin k)) (f : Fin k → A) :
      (∏ i ∈ J, f i) = ∏ i : Fin k, if i ∈ J then f i else 1 := by simp
  rw [h, Fin.prod_univ_succ]
  congr 1
  rw [h r (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective r h))
    (fun i ↦ a i.succ)]
  simp only [Finset.mem_preimage]

private theorem negative_factor_basis_step
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w})
    (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) (q : ℤ) :
    ringedNegativeKoszulFactorBasis O s (n + 1) q ≫
        (ringedNegativeKoszulFactorTransition O s n).f q =
      (if q = -1 then (ringedKoszulScalar O s).asHom else 𝟙 _) ≫
        ringedNegativeKoszulFactorBasis O s n q := by
  by_cases hq : q = -1
  · subst q
    simp [ringedNegativeKoszulFactorTransition, ringedNegativeKoszulFactorTransitionF,
      ringedNegativeKoszulFactorBasis]
  · by_cases hq' : q = 0
    · subst q
      simp [ringedNegativeKoszulFactorTransition, ringedNegativeKoszulFactorTransitionF,
        ringedNegativeKoszulFactorBasis]
    · simp [ringedNegativeKoszulFactorTransition, ringedNegativeKoszulFactorTransitionF,
        ringedNegativeKoszulFactorBasis, hq, hq']

private theorem ringed_inclusion_natural
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w})
    (K L K' L' : ringedSiteComplex O) (f : K ⟶ K') (g : L ⟶ L')
    (p t q : ℤ) (h : p + t = q) :
    letI := SheafOfModules.isGrothendieckAbelian
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    CochainComplex.ιMapBifunctor K L (MonoidalCategory.curriedTensor _) p t q h ≫
        (((ringedKoszulTensor O).map f).app L).f q ≫
          (((ringedKoszulTensor O).obj K').map g).f q =
      MonoidalCategory.tensorHom (f.f p) (g.f t) ≫
        CochainComplex.ιMapBifunctor K' L' (MonoidalCategory.curriedTensor _) p t q h := by
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  change HomologicalComplex.ιMapBifunctor K L (MonoidalCategory.curriedTensor _)
      (.up ℤ) p t q h ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 L)
        (MonoidalCategory.curriedTensor _) (.up ℤ)).f q ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K') g
        (MonoidalCategory.curriedTensor _) (.up ℤ)).f q = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.id_whiskerRight, MonoidalCategory.tensorHom_def_assoc]
  erw [Category.id_comp, Category.id_comp]

private theorem negative_basis_succ
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) (r : ℕ)
    (s : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections)
    (n : ℕ) (I : Finset (Fin (r + 1))) (q : ℤ) :
    letI := SheafOfModules.isGrothendieckAbelian
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    ringedNegativeKoszulBasis O (r + 1) s n I q =
      (MonoidalCategory.leftUnitor
        (SheafOfModules.unit ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O))).inv ≫
      MonoidalCategory.tensorHom
        (ringedNegativeKoszulFactorBasis O (s 0) n (if 0 ∈ I then -1 else 0))
        (ringedNegativeKoszulBasis O r (fun i ↦ s i.succ) n
          (I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective r h))
          (q - if 0 ∈ I then -1 else 0)) ≫
      CochainComplex.ιMapBifunctor (ringedNegativeKoszulFactor O (s 0) n)
        (ringedNegativeKoszul O r (fun i ↦ s i.succ) n)
        (MonoidalCategory.curriedTensor _) (if 0 ∈ I then -1 else 0)
        (q - if 0 ∈ I then -1 else 0) q (by omega) := rfl

private theorem negative_transition_succ
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) (r : ℕ)
    (s : Fin (r + 1) → (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    ringedNegativeKoszulTransition O (r + 1) s n =
      ((ringedKoszulTensor O).map (ringedNegativeKoszulFactorTransition O (s 0) n)).app
        (ringedNegativeKoszul O r (fun i ↦ s i.succ) (n + 1)) ≫
      ((ringedKoszulTensor O).obj (ringedNegativeKoszulFactor O (s 0) n)).map
        (ringedNegativeKoszulTransition O r (fun i ↦ s i.succ) n) := rfl

attribute [local irreducible] homComplexFunctor ringedKoszulFactor
  ringedNegativeKoszulFactor ringedKoszulScalar

private theorem negative_basis_step
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    (r : ℕ) (a : Fin r → A)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hρ : ∀ i, ρ (a i) = ringedKoszulScalar O (s i))
    (n : ℕ) (q : ℤ) (I : Finset (Fin r)) :
    ringedNegativeKoszulBasis O r s (n + 1) I q ≫
        (ringedNegativeKoszulTransition O r s n).f q =
      (ρ (∏ i ∈ I, a i)).asHom ≫ ringedNegativeKoszulBasis O r s n I q := by
  classical
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  induction r generalizing q with
  | zero =>
    have hI : I = ∅ := Subsingleton.elim _ _
    subst I
    simp [ringedNegativeKoszulTransition, ringedNegativeKoszulBasis]
  | succ r ih =>
    let J := I.preimage Fin.succ (fun _ _ _ _ h ↦ Fin.succ_injective r h)
    let p : ℤ := if (0 : Fin (r + 1)) ∈ I then -1 else 0
    have ht := ih (fun i ↦ a i.succ) (fun i ↦ s i.succ) (fun i ↦ hρ i.succ)
      (q - p) J
    have hf := negative_factor_basis_step O (s 0) n p
    have hp : (if p = -1 then (ringedKoszulScalar O (s 0)).asHom else 𝟙 _) =
        (ρ (if (0 : Fin (r + 1)) ∈ I then a 0 else 1)).asHom := by
      by_cases h : (0 : Fin (r + 1)) ∈ I
      · simp [p, h, hρ]
      · simp [p, h]
    rw [hp] at hf
    rw [negative_basis_succ, negative_transition_succ,
      HomologicalComplex.comp_f, negative_basis_succ]
    simp only [Category.assoc]
    rw [ringed_inclusion_natural]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, hf, ht,
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    erw [reassoc_of% (unit_tensor_scalars
      (ρ (if (0 : Fin (r + 1)) ∈ I then a 0 else 1))
      (ρ (∏ i ∈ J, a i.succ)))]
    rw [subset_prod_succ, map_mul]
    rfl

/-- The dual tensor has a finite ordered-subset basis with its actual matrices.
This statement concerns only the ringed-site complexes: it has no additive
realization functor or exterior algebra comparison.

Source: Stacks Project, More on Algebra, Tag 0664; Algebraization, Tag 0A0E,
lemma-derived-completion-koszul, finite free duality and its transition maps.
(auxiliary; not a blueprint node).

Proof: use the supported-subset coproduct of the canonical negative tensor
basis for positive length. For the empty tensor, its sole basis in degree zero
is the inverse single-complex identification; in other degrees its term is zero
and the index type is empty. The canonical negative basis has the actual exterior
boundary coefficients by ringedNegativeKoszulBasis_exterior_d.

Compute the actual one-factor transition on its two basis maps. It acts by its
section in degree minus one and by identity in degree zero. Naturality of the
ordered tensor inclusions combines these calculations inductively: the inverse
unit unitor converts the tensor of scalar endomorphisms into their product.
Splitting the subset product into its first-index contribution and its successor
indices gives the one-step diagonal formula.

Compose the canonical negative basis with the proved negative-to-dual tensor
isomorphisms, including their separate empty-list case. Transport the coproduct
universal property and the differential equation along these isomorphisms.
Their naturality gives the actual one-step dual-tower transition, and induction
on n <= m, using functoriality and the product-of-powers identity, gives the full
transition formula. Their normalized empty-basis equation is exactly the stated
dual unit. No scalar is inverted, so empty lists, zero rings, zero or unit
sections, and empty sites are included. -/
theorem exists_ringedKoszulDualBasis
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    (r : ℕ) (a : Fin r → A)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hρ : ∀ i, ρ (a i) = ringedKoszulScalar O (s i)) :
    let D := ringedKoszulDualTower O r s
    ∃ b : ∀ (n : ℕ) (q : ℤ), exteriorKoszulIndex r q →
        (SheafOfModules.unit ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O) ⟶
          (D.obj (op n)).X q),
      (∀ n q, Nonempty (IsColimit (Cofan.mk ((D.obj (op n)).X q) (b n q)))) ∧
      (∀ n q I, b n q I ≫ (D.obj (op n)).d q (q + 1) =
        ∑ L : exteriorKoszulIndex r (q + 1),
          (ρ (exteriorKoszulCoefficient r (fun i ↦ a i ^ (n + 1)) q I L)).asHom ≫
            b n (q + 1) L) ∧
      (∀ n m (h : n ≤ m) q I, b m q I ≫ (D.map (homOfLE h).op).f q =
        (ρ (∏ i ∈ I.1, a i ^ (m - n))).asHom ≫ b n q I) ∧
      ∀ n, b n 0 ⟨∅, rfl⟩ =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r s n).f 0 := by
  classical
  dsimp only
  obtain ⟨e, he, hu⟩ :
      ∃ e : ∀ n : ℕ, ringedNegativeKoszul O r s n ≅
          (ringedKoszulDualTower O r s).obj (op n),
        (∀ n, ringedNegativeKoszulTransition O r s n ≫ (e n).hom =
          (e (n + 1)).hom ≫ (ringedKoszulDualTower O r s).map
            (homOfLE (Nat.le_succ n)).op) ∧
        (∀ n, ringedNegativeKoszulBasis O r s n ∅ 0 ≫ (e n).hom.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
            (ringedKoszulDualUnit O r s n).f 0) := by
    cases r with
    | zero => exact ringedNegativeKoszulZeroDuality O s
    | succ r => exact ringedNegativeKoszulSuccDuality O r s
  let D := ringedKoszulDualTower O r s
  let b (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :=
    ringedNegativeKoszulBasis O r s n I.1 q ≫ (e n).hom.f q
  have hstep (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :
      b (n + 1) q I ≫ (D.map (homOfLE (Nat.le_succ n)).op).f q =
        (ρ (∏ i ∈ I.1, a i)).asHom ≫ b n q I := by
    dsimp only [b]
    have ht := congrArg (fun f ↦ f.f q) (he n)
    simp only [HomologicalComplex.comp_f] at ht
    rw [Category.assoc, ← ht, ← Category.assoc,
      negative_basis_step O ρ r a s hρ, Category.assoc]
  refine ⟨b, ?_, ?_, ?_, hu⟩
  · intro n q
    obtain ⟨hc⟩ := negative_basis_isColimit O r s n q
    let z := (HomologicalComplex.eval _ (.up ℤ) q).mapIso (e n)
    refine ⟨Cofan.IsColimit.mk _ (fun c ↦ z.inv ≫ hc.desc c) ?_ ?_⟩
    · intro c I
      change (ringedNegativeKoszulBasis O r s n I.1 q ≫ z.hom) ≫
        z.inv ≫ hc.desc c = _
      rw [Category.assoc, z.hom_inv_id_assoc]
      exact hc.fac c ⟨I⟩
    · intro c f hf
      apply (cancel_epi z.hom).1
      rw [z.hom_inv_id_assoc]
      apply hc.hom_ext
      intro ⟨I⟩
      have h := hf I
      change (ringedNegativeKoszulBasis O r s n I.1 q ≫ z.hom) ≫ f = c.inj I at h
      calc
        _ = c.inj I := by simpa only [Cofan.mk_ι_app, Category.assoc] using h
        _ = _ := (hc.fac c ⟨I⟩).symm
  · intro n q I
    dsimp only [b]
    rw [Category.assoc, (e n).hom.comm,
      ← Category.assoc, ringedNegativeKoszulBasis_exterior_d O ρ r a s hρ,
      Preadditive.sum_comp]
    simp only [Category.assoc]
  · intro n m h q I
    induction m, h using Nat.le_induction with
    | base =>
      change b n q I ≫ (D.map (𝟙 (op n))).f q = _
      simp only [Functor.map_id, HomologicalComplex.id_f, Nat.sub_self, pow_zero,
        Finset.prod_const_one, map_one, End.one_asHom, Category.id_comp]
      exact Category.comp_id _
    | succ m h ih =>
      have hm : D.map (homOfLE (h.trans (Nat.le_succ m))).op =
          D.map (homOfLE (Nat.le_succ m)).op ≫ D.map (homOfLE h).op := by
        rw [← Functor.map_comp]
        congr 1
      rw [hm, HomologicalComplex.comp_f, ← Category.assoc, hstep, Category.assoc, ih,
        ← Category.assoc, ← End.mul_asHom, ← map_mul]
      congr 2
      have hsub : m + 1 - n = (m - n) + 1 := by omega
      simp only [hsub, pow_succ, Finset.prod_mul_distrib]

end CategoryTheory
