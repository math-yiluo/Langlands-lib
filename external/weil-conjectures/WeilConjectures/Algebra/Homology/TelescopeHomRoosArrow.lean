/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import WeilConjectures.Algebra.Homology.TelescopeColimit
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import all WeilConjectures.Algebra.Homology.SignedDoubleHomCone
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The telescope Hom arrow and the ordinary-limit Roos arrow

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A; derived.tex, Tag 0949.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local irreducible] homComplexFunctor

namespace TelescopeHomRoosProof

open SignedDoubleHomCone.Calculation
open HomologicalComplex.homotopyCofiber

universe v' u'
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]
  {F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ}

-- The cone calculation is independent of sheaves and of all limit exactness hypotheses.
omit [HasBinaryBiproducts D] in
private theorem dual_additive {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) : (dualF F I).Additive where
  map_add := by
    intro K L f g
    apply HomologicalComplex.hom_ext
    intro n
    apply proj_ext P L.unop I n
    intro p
    change ((dualF F I).map (f + g)).f n ≫ P.π L.unop I n p (p + n) rfl = _
    have hh (h : K ⟶ L) := dual_proj P I h.unop n p (p + n) rfl
    simp only [Quiver.Hom.op_unop] at hh
    rw [hh]
    simp only [unop_add, HomologicalComplex.add_f_apply, H.map_add_left,
      Preadditive.comp_add, Preadditive.add_comp]
    rw [hh, hh]

private theorem dual_telescope_shift
    {A₀ B₀ : Type*} [Category* A₀] [Category* B₀]
    [Preadditive A₀] [Preadditive B₀]
    (E : ℕ ⥤ A₀) (T : A₀ᵒᵖ ⥤ B₀) [T.Additive]
    (K : ℕᵒᵖ ⥤ B₀) [HasProduct (fun n ↦ K.obj (op n))]
    (e : E.op ⋙ T ≅ K) (S : A₀) (ι : ∀ n, E.obj n ⟶ S) (u : S ⟶ S)
    (hι : ∀ n, ι n ≫ u = ι n - E.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1))
    (b : T.obj (op S) ⟶ ∏ᶜ (fun n ↦ K.obj (op n)))
    (hb : ∀ n, b ≫ Pi.π (fun n ↦ K.obj (op n)) n = T.map (ι n).op ≫ e.hom.app (op n)) :
    T.map u.op ≫ b = b ≫
      towerTransitionEndomorphism (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, hb, ← Category.assoc, ← T.map_comp, ← op_comp, hι n,
    op_sub, T.map_sub, Preadditive.sub_comp, op_comp, T.map_comp, Category.assoc]
  simp only [towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
    Category.id_comp, Pi.lift_comp_π]
  rw [ ← Category.assoc b, hb, hb, Category.assoc,
    ← e.hom.naturality (homOfLE (Nat.le_succ n)).op]
  rfl

private theorem pred_rel (n : ℤ) : (ComplexShape.up ℤ).Rel (n - 1) n := by
  change n - 1 + 1 = n
  omega

private lemma coneMap_first {A B A' B' : CochainComplex D ℤ}
    (f : A ⟶ B) (g : A' ⟶ B') (α : Arrow.mk f ⟶ Arrow.mk g) (n : ℤ) :
    (mapArrowHom f g (fun j : ℤ ↦ ⟨j - 1, pred_rel j⟩) α).f (n - 1) ≫
        fstX g (n - 1) n (pred_rel n) =
      fstX f (n - 1) n (pred_rel n) ≫ α.left.f n := by
  apply ext_from_X f n (n - 1) (pred_rel n)
  · simp only [← Category.assoc, mapArrowHom, inlX_desc_f]
    simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero]
    rw [inrCompHomotopy_hom _ _ n (n - 1) (pred_rel n)]
    simp only [Category.assoc, inlX_fstX, Category.comp_id, Category.id_comp]
  · dsimp only [mapArrowHom]
    rw [← Category.assoc, inrX_desc_f]
    simp only [HomologicalComplex.comp_f, Category.assoc, inr_f,
      inrX_fstX, comp_zero, inrX_fstX_assoc, zero_comp]

private lemma coneMap_second {A B A' B' : CochainComplex D ℤ}
    (f : A ⟶ B) (g : A' ⟶ B') (α : Arrow.mk f ⟶ Arrow.mk g) (n : ℤ) :
    (mapArrowHom f g (fun j : ℤ ↦ ⟨j - 1, pred_rel j⟩) α).f n ≫ sndX g n =
      sndX f n ≫ α.right.f n := by
  apply ext_from_X f (n + 1) n rfl
  · simp only [← Category.assoc, mapArrowHom, inlX_desc_f]
    simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero]
    rw [inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [Category.assoc, inlX_sndX, comp_zero, zero_comp]
  · dsimp only [mapArrowHom]
    rw [← Category.assoc, inrX_desc_f]
    simp only [HomologicalComplex.comp_f, Category.assoc, inr_f,
      inrX_sndX, Category.comp_id, inrX_sndX_assoc]

private theorem rel_of_eq (n t : ℤ) (h : t + 1 = n) :
    (ComplexShape.up ℤ).Rel t n := h

private noncomputable def coneDualIso {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) {A B : CochainComplex D ℤ} (f : A ⟶ B) :
    hc F (CochainComplex.mappingCone f) I ≅
      CochainComplex.mappingCocone (-((dualF F I).map f.op)) := by
  let g := -((dualF F I).map f.op)
  let W := CochainComplex.mappingCocone g
  let a (n t : ℤ) (h : t + 1 = n) :
      (hc F (HomologicalComplex.homotopyCofiber f) I).X n ⟶
        HomologicalComplex.homotopyCofiber.X g t :=
    outB P I f n ≫ inlX g n t (rel_of_eq n t h) +
      n.negOnePow • (outA P I f n t h ≫ inrX g t)
  let b (n t : ℤ) (h : t + 1 = n) :
      HomologicalComplex.homotopyCofiber.X g t ⟶
        (hc F (HomologicalComplex.homotopyCofiber f) I).X n :=
    (show HomologicalComplex.homotopyCofiber.X g t ⟶
      (hc F (HomologicalComplex.homotopyCofiber f) I).X n from
      fstX g t n (rel_of_eq n t h) ≫ inB P I f n) +
    (show HomologicalComplex.homotopyCofiber.X g t ⟶
      (hc F (HomologicalComplex.homotopyCofiber f) I).X n from
      n.negOnePow • (sndX g t ≫ inA P I f t ≫
        ((hc F (HomologicalComplex.homotopyCofiber f) I).XIsoOfEq h).hom))
  have hab (n t : ℤ) (h : t + 1 = n) : a n t h ≫ b n t h = 𝟙 _ := by
    subst n
    dsimp only [a, b]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      Linear.comp_units_smul, Linear.units_smul_comp,
      inlX_fstX_assoc, inlX_sndX_assoc, inrX_fstX_assoc, inrX_sndX_assoc,
      comp_zero, zero_comp, smul_zero, add_zero, zero_add,
      smul_smul, Int.units_mul_self, one_smul]
    exact out_in_sum P I f t
  have hba (n t : ℤ) (h : t + 1 = n) : b n t h ≫ a n t h = 𝟙 _ := by
    subst n
    dsimp only [a, b]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
    apply ext_from_X g (t + 1) t (rel_of_eq (t + 1) t rfl)
    · simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        Linear.comp_units_smul, Linear.units_smul_comp,
        inlX_fstX_assoc, inlX_sndX_assoc,
        zero_comp, smul_zero, add_zero]
      erw [← Category.assoc, inB_outB, Category.id_comp]
      erw [← Category.assoc, inB_outA]
      simp
    · simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        Linear.comp_units_smul, Linear.units_smul_comp,
        inrX_fstX_assoc, inrX_sndX_assoc,
        zero_comp, zero_add]
      simp only [← Category.assoc, inA_outB, inA_outA,
        zero_comp, Category.id_comp, smul_zero, zero_add,
        smul_smul, Int.units_mul_self, one_smul, Category.comp_id]
  have comm (n m t s : ℤ) (ht : t + 1 = n) (hs : s + 1 = m) (hnm : n + 1 = m) :
      b n t ht ≫ (hc F (HomologicalComplex.homotopyCofiber f) I).d n m =
        (-HomologicalComplex.homotopyCofiber.d g t s) ≫ b m s hs := by
    subst m
    have hsn : s = n := by omega
    subst s
    subst n
    dsimp only [b]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
    apply ext_from_X g (t + 1) t (rel_of_eq (t + 1) t rfl)
    · simp only [Preadditive.comp_add, Preadditive.add_comp,
        Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
        inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, smul_zero, add_zero,
        Preadditive.comp_neg, Preadditive.neg_comp]
      simp only [inlX_d_assoc g t (t + 1) (t + 1 + 1) rfl rfl]
      simp only [Preadditive.add_comp, Preadditive.neg_comp,
        Category.assoc, inlX_fstX_assoc,
        inlX_sndX_assoc, inrX_fstX_assoc, inrX_sndX_assoc,
        comp_zero, zero_comp, add_zero, zero_add,
        g, HomologicalComplex.neg_f_apply, neg_add_rev, neg_neg]
      simpa only [Preadditive.comp_neg, neg_neg, add_comm] using inB_d P I f (t + 1)
    · simp only [Preadditive.comp_add, Preadditive.add_comp,
        Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
        inrX_fstX_assoc, inrX_sndX_assoc, zero_comp, zero_add,
        Preadditive.comp_neg, Preadditive.neg_comp]
      simp only [inrX_d_assoc]
      simp only [inrX_fstX_assoc, inrX_sndX_assoc,
        Int.negOnePow_succ, Units.neg_smul, neg_neg]
      simpa only [Int.negOnePow_succ, Units.neg_smul, Preadditive.comp_neg,
        Preadditive.neg_comp, smul_neg, comp_zero, zero_comp, neg_zero, zero_add] using
        congrArg (fun z ↦ (t + 1).negOnePow • z) (inA_d P I f t)
  let e (n : ℤ) : W.X n ≅ (hc F (HomologicalComplex.homotopyCofiber f) I).X n :=
    ⟨b n (n - 1) (by omega), a n (n - 1) (by omega),
      hba n (n - 1) (by omega), hab n (n - 1) (by omega)⟩
  refine (HomologicalComplex.Hom.isoOfComponents e ?_).symm
  intro n m hnm
  change b n (n - 1) _ ≫ (hc F (HomologicalComplex.homotopyCofiber f) I).d n m =
    W.d n m ≫ b m (m - 1) _
  change _ = ((-1 : ℤ).negOnePow • HomologicalComplex.homotopyCofiber.d g
    (n - 1) (m - 1)) ≫ _
  simpa only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul] using
    comm n m (n - 1) (m - 1) (by omega) (by omega) hnm

private lemma coneDualIso_first {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) {A B : CochainComplex D ℤ} (f : A ⟶ B) (n : ℤ) :
    (coneDualIso P I f).hom.f n ≫
        fstX (-((dualF F I).map f.op)) (n - 1) n
          (pred_rel n) =
      ((dualF F I).map (CochainComplex.mappingCone.inr f).op).f n := by
  change (outB P I f n ≫
      inlX (-((dualF F I).map f.op)) n (n - 1)
        (pred_rel n) +
    n.negOnePow • (outA P I f n (n - 1) (by omega) ≫
      inrX (-((dualF F I).map f.op)) (n - 1))) ≫ _ = _
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    inlX_fstX, inrX_fstX, Category.comp_id, comp_zero, smul_zero, add_zero]
  rfl

private lemma coneDualIso_second {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) {A B : CochainComplex D ℤ} (f : A ⟶ B) (n : ℤ) :
    (coneDualIso P I f).hom.f n ≫ sndX (-((dualF F I).map f.op)) (n - 1) =
      n.negOnePow • outA P I f n (n - 1) (by omega) := by
  change (outB P I f n ≫
      inlX (-((dualF F I).map f.op)) n (n - 1)
        (pred_rel n) +
    n.negOnePow • (outA P I f n (n - 1) (by omega) ≫
      inrX (-((dualF F I).map f.op)) (n - 1))) ≫ _ = _
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    inlX_sndX, inrX_sndX, Category.comp_id, comp_zero, zero_add]

-- Subsequent proofs use the two coordinate equations, without unfolding the constructed iso.
attribute [local irreducible] coneDualIso

private lemma cone_precomp_outA_zero {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) {A B L : CochainComplex D ℤ} (u : A ⟶ B)
    (f : CochainComplex.mappingCone u ⟶ L)
    (hf : (CochainComplex.mappingCone.inl u).comp
      (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero _) = 0) (n : ℤ) :
    ((dualF F I).map f.op).f n ≫ outA P I u n (n - 1) (by omega) = 0 := by
  apply proj_ext P A I (n - 1)
  intro a
  rw [Category.assoc, outA_proj P I u n (n - 1) (by omega) a (a - 1) _
    (by omega) rfl]
  erw [← Category.assoc, dual_proj P I f, Category.assoc, H.map_comp]
  have ha := congrArg
    (fun z ↦ z.v a (a - 1) (show a + (-1) = a - 1 by omega)) hf
  simp only [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.HomComplex.Cochain.zero_v] at ha
  rw [ha, H.map_zero_left, comp_zero, zero_comp]

private theorem coneDual_square {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) {A B L Q Y Z : CochainComplex D ℤ}
    (u : A ⟶ B) (f : CochainComplex.mappingCone u ⟶ L) (g : Y ⟶ Z)
    (a : hc F L I ≅ Q) (b : hc F B I ⟶ Y) (c : hc F A I ⟶ Z)
    (z : CochainComplex.mappingCocone (-((dualF F I).map u.op)) ≅
      CochainComplex.mappingCocone g)
    (hz₁ : ∀ n : ℤ, z.hom.f n ≫ fstX g (n - 1) n (pred_rel n) =
      fstX (-((dualF F I).map u.op)) (n - 1) n (pred_rel n) ≫ b.f n)
    (hz₂ : ∀ n : ℤ, z.hom.f n ≫ sndX g (n - 1) =
      sndX (-((dualF F I).map u.op)) (n - 1) ≫ c.f (n - 1))
    (r : Q ⟶ CochainComplex.mappingCocone g) (k : Q ⟶ Y)
    (hr₁ : ∀ n : ℤ, r.f n ≫ fstX g (n - 1) n (pred_rel n) = k.f n)
    (hr₂ : ∀ n : ℤ, r.f n ≫ sndX g (n - 1) = 0)
    (h : (dualF F I).map (CochainComplex.mappingCone.inr u ≫ f).op ≫ b = a.hom ≫ k)
    (hf : (CochainComplex.mappingCone.inl u).comp
      (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero _) = 0) :
    a.hom ≫ r = (dualF F I).map f.op ≫ (coneDualIso P I u ≪≫ z).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ext_to_X g (n - 1) n (pred_rel n)
  · simp only [HomologicalComplex.comp_f, Iso.trans_hom, Category.assoc]
    erw [hr₁, hz₁, ← Category.assoc ((coneDualIso P I u).hom.f n), coneDualIso_first]
    have hn := congrArg (fun k ↦ k.f n) h
    simp only [op_comp, Functor.map_comp, NatTrans.comp_app,
      HomologicalComplex.comp_f, Category.assoc] at hn
    exact hn.symm
  · simp only [HomologicalComplex.comp_f, Iso.trans_hom, Category.assoc]
    erw [hr₂, comp_zero, hz₂,
      ← Category.assoc ((coneDualIso P I u).hom.f n), coneDualIso_second,
      Linear.units_smul_comp, Linear.comp_units_smul,
      ← Category.assoc (((dualF F I).map f.op).f n),
      cone_precomp_outA_zero P I u f hf n]
    simp

omit [HasBinaryBiproducts D] in
private noncomputable def dualCoproductFanIsLimit {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ) {ι : Type*} (K : ι → CochainComplex D ℤ)
    (S : CochainComplex D ℤ) (ιS : ∀ k, K k ⟶ S)
    (hS : ∀ n p : ℤ, IsLimit (Fan.mk (H.obj (S.X p) (I.X (p + n)))
      (fun k ↦ H.map ((ιS k).f p) (𝟙 _)))) :
    IsLimit (Fan.mk (hc F S I) (fun k ↦ (dualF F I).map (ιS k).op)) := by
  apply HomologicalComplex.isLimitOfEval
  intro n
  apply IsLimit.ofExistsUnique
  intro s
  let t (p : ℤ) := Fan.mk s.pt
    (fun k ↦ s.π.app ⟨k⟩ ≫ P.π (K k) I n p (p + n) rfl)
  let l := (P.lim S I n).lift
    (Fan.mk s.pt (fun p ↦ (hS n p).lift (t p)))
  have hl (p : ℤ) : l ≫ P.π S I n p (p + n) rfl = (hS n p).lift (t p) :=
    (P.lim S I n).fac _ ⟨p⟩
  refine ⟨l, ?_, ?_⟩
  · rintro ⟨k⟩
    apply proj_ext P (K k) I n
    intro p
    change (l ≫ ((dualF F I).map (ιS k).op).f n) ≫ P.π (K k) I n p (p + n) rfl = _
    rw [Category.assoc, dual_proj, ← Category.assoc, hl]
    exact (hS n p).fac (t p) ⟨k⟩
  · intro g hg
    apply proj_ext P S I n
    intro p
    rw [hl]
    apply (hS n p).uniq (t p)
    rintro ⟨k⟩
    change (g ≫ P.π S I n p (p + n) rfl) ≫ H.map ((ιS k).f p) (𝟙 _) = _
    rw [Category.assoc, ← dual_proj, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ P.π (K k) I n p (p + n) rfl) (hg ⟨k⟩)

end TelescopeHomRoosProof

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

private local instance (O : Sheaf J CommRingCat.{u}) :
    HasColimitsOfShape (Discrete ℕ) (ringedSiteComplex O) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
  have : HasColimitsOfShape (Discrete ℕ) A := inferInstance
  refine ⟨fun F ↦ ?_⟩
  have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval A (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

namespace TelescopeHomRoosProof

open SignedDoubleHomCone.Calculation

attribute [local irreducible] homComplexπ homComplexIsLimit

private noncomputable def sheafHomData (O : Sheaf J CommRingCat.{u}) :
    HomData (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) where
  obj := fun A B ↦ SheafOfModules.homObj.{u, u, u, u} (R := O) A B
  map := fun f g ↦ SheafOfModules.homObjMap.{u, u, u, u} (R := O) f g
  map_id := fun _ _ ↦ SheafOfModules.homObjMap_id (R := O)
  map_comp := fun f f' g g' ↦
    SheafOfModules.homObjMap_comp_homObjMap (R := O) f f' g g'
  map_add_left := by
    intro A A' B B' f g h
    exact SheafOfModules.hom_ext
      (PresheafOfModules.homObjMap_add_left f.val g.val h.val)
  map_zero_left := by
    intro A A' B B' g
    exact SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left g.val)

private noncomputable def sheafHomSpec (O : Sheaf J CommRingCat.{u}) :
    Spec (sheafHomData O) (homComplexFunctor (R := O)) where
  π := fun L M n a b h ↦ homComplexπ.{u, u, u, u} (R := O) L M n a b h
  lim := fun L M n ↦ homComplexIsLimit.{u, u, u, u} (R := O) L M n
  diff := fun L M n m a b b' a' hnm h h' ha' ↦
    homComplex_d_π.{u, u, u, u} (R := O) L M n m a b b' a' hnm h h' ha'
  map := fun _ _ _ _ f g n a b h ↦
    homComplexFunctor_map_f_π.{u, u, u, u} (R := O) f g n a b h

-- Keep the concrete sheaf implementation out of later abstract cone calculations.
attribute [local irreducible] sheafHomSpec

private noncomputable def sheafDualCoproductFanIsLimit
    (O : Sheaf J CommRingCat.{u}) (E : ℕ ⥤ ringedSiteComplex O) (I : ringedSiteComplex O) :
    IsLimit (Fan.mk (((homComplexFunctor (R := O)).obj (op (∐ fun n ↦ E.obj n))).obj I)
      (fun n ↦ ((homComplexFunctor (R := O)).flip.obj I).map
        (Sigma.ι (fun n ↦ E.obj n) n).op)) := by
  apply dualCoproductFanIsLimit (sheafHomSpec O)
  intro n p
  let ev := HomologicalComplex.eval
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) (.up ℤ) p
  exact (SheafOfModules.internalHomCoproductFanIsLimit O
    (fun n ↦ (E.obj n).X p)
    (Cofan.mk _ (fun n ↦ ev.map (Sigma.ι (fun n ↦ E.obj n) n)))
    ((Cofan.isColimitMapCoconeEquiv ev _ _)
      (isColimitOfPreserves ev (coproductIsCoproduct (fun n ↦ E.obj n))))
    (I.X (p + n))).some

private noncomputable abbrev ordinaryCone (O : Sheaf J CommRingCat.{u})
    (X : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ) :
    Cone X.asFunctor where
  pt := ExactProductsRoos.ordinary.obj X
  π :=
    { app := fun m ↦ (NatTrans.mapHomologicalComplex (lim.π m) (.up ℤ)).app X
      naturality := fun {m k} f ↦ by
        apply HomologicalComplex.hom_ext
        intro n
        change 𝟙 _ ≫ limit.π (X.X n) k = limit.π (X.X n) m ≫ (X.X n).map f
        simpa only [Category.id_comp] using (limit.w (X.X n) f).symm }

private noncomputable def ordinaryConeIsLimit (O : Sheaf J CommRingCat.{u})
    (X : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ) :
    IsLimit (ordinaryCone O X) := by
  apply HomologicalComplex.isLimitOfEval
  intro n
  exact limit.isLimit (X.X n)

end TelescopeHomRoosProof

-- The canonical sheaf limit instances require more than the default elaboration budget.
/-- The algebraic telescope-Hom comparison identifies the actual arrow, using both
canonical legs of the map from the telescope to the ordinary colimit. Neither
K-injectivity nor a quasi-isomorphism hypothesis is part of this assertion.

Source: Stacks Project, sites-cohomology.tex, Tag 0A0A,
lemma-colim-and-lim-of-duals; derived.tex, Tag 0949, lemma-colim-hocolim.
(auxiliary; not a blueprint node).

Proof: write S for the direct sum of the sequence E. Internal Hom of the colimit
is the inverse limit of Hom(E_m,I): transpose a local bilinear pairing to use the
colimit universal property in each source degree, then interchange the products
over source degrees and sequence indices. This gives a chain isomorphism to the
ordinary limit of X via the specified tower isomorphism e. The same universal
property identifies Hom(S,I) with the product of X, and precomposition by
1-shift becomes the Roos difference delta. A degree-n map from the telescope
has coordinates (a,b) in Hom(S,I)^n and Hom(S,I)^(n-1), with differential
(d a,d b+(-1)^(n+1)delta(a)). Sending (a,b) to (a,(-1)^n b) identifies this
with mappingCocone(-delta), whose differential is (d a,delta(a)-d b).
Both inverse equations follow from the product and binary biproduct identities.
For precomposition by f, its first coordinate is the ordinary-limit inclusion:
the unshifted restriction of f is the family of colimit legs. Its second
coordinate is zero because the shifted cochain restriction of f is zero.
Therefore these two chain isomorphisms intertwine Hom(f,I) with the specified
zero-second-coordinate comparison. They form the asserted isomorphism of arrows.
This works for constant sequences and zero objects and uses no exactness of
products or injectivity. -/
theorem telescopeHom_roos_arrow_iso
    (O : Sheaf J CommRingCat.{u}) (E : ℕ ⥤ ringedSiteComplex O)
    (I : ringedSiteComplex O)
    (X : CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ)
    (e : E.op ⋙ (homComplexFunctor (R := O)).flip.obj I ≅ X.asFunctor)
    (f : CochainComplex.mappingCone (CochainComplex.telescopeColimitShift O E) ⟶
      colimit E)
    (hf₁ : CochainComplex.mappingCone.inr (CochainComplex.telescopeColimitShift O E) ≫
      f = CochainComplex.telescopeToColimit O E)
    (hf₂ : (CochainComplex.mappingCone.inl (CochainComplex.telescopeColimitShift O E)).comp
      (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero _) = 0) :
    Nonempty (Arrow.mk (((homComplexFunctor (R := O)).map f.op).app I) ≅
      Arrow.mk (ExactProductsRoos.comparison.app X)) := by
  classical
  let T := SignedDoubleHomCone.Calculation.dualF (homComplexFunctor (R := O)) I
  let P := TelescopeHomRoosProof.sheafHomSpec O
  let : T.Additive := TelescopeHomRoosProof.dual_additive P I
  let S := ∐ fun n ↦ E.obj n
  let u := CochainComplex.telescopeColimitShift O E
  let q := CochainComplex.telescopeToColimit O E
  let Y := ExactProductsRoos.product.obj X
  let δ := ExactProductsRoos.difference.app X
  let c := (Cone.postcompose e.hom).obj (ringedHomComplexColimitCone O E I)
  let hc : IsLimit c := (IsLimit.postcomposeHomEquiv e _).symm
    (ringedHomComplexColimitCone_isLimit O E I).some
  let a := hc.conePointUniqueUpToIso (TelescopeHomRoosProof.ordinaryConeIsLimit O X)
  have ha (m : ℕᵒᵖ) :
      a.hom ≫ (TelescopeHomRoosProof.ordinaryCone O X).π.app m =
        T.map (colimit.ι E m.unop).op ≫ e.hom.app m :=
    hc.conePointUniqueUpToIso_hom_comp
      (TelescopeHomRoosProof.ordinaryConeIsLimit O X) m
  let d := Fan.mk (T.obj (op S)) (fun n ↦
    T.map (Sigma.ι (fun n ↦ E.obj n) n).op ≫ e.hom.app (op n))
  let hd : IsLimit d := Fan.IsLimit.ofIsos
    (TelescopeHomRoosProof.sheafDualCoproductFanIsLimit O E I)
    (fun n ↦ (e.app (op n)).symm) (Iso.refl _) (fun n ↦ by
      change T.map (Sigma.ι (fun n ↦ E.obj n) n).op =
        (T.map (Sigma.ι (fun n ↦ E.obj n) n).op ≫ e.hom.app (op n)) ≫
          e.inv.app (op n)
      rw [Category.assoc, e.hom_inv_id_app]
      erw [Category.comp_id])
  let b : T.obj (op S) ≅ Y :=
    hd.conePointUniqueUpToIso (productIsProduct (fun n ↦ X.asFunctor.obj (op n)))
  have hb (n : ℕ) : b.hom ≫ Pi.π (fun n ↦ X.asFunctor.obj (op n)) n =
      T.map (Sigma.ι (fun n ↦ E.obj n) n).op ≫ e.hom.app (op n) :=
    hd.conePointUniqueUpToIso_hom_comp
      (productIsProduct (fun n ↦ X.asFunctor.obj (op n))) ⟨n⟩
  have hu : T.map u.op ≫ b.hom = b.hom ≫ δ :=
    TelescopeHomRoosProof.dual_telescope_shift E T X.asFunctor e S
      (Sigma.ι (fun n ↦ E.obj n)) u (fun n ↦ Sigma.ι_comp_desc _ n) b.hom hb
  have hq : T.map q.op ≫ b.hom = a.hom ≫ ExactProductsRoos.inclusion.app X := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hb, ← Category.assoc, ← T.map_comp, ← op_comp]
    rw [show Sigma.ι (fun n ↦ E.obj n) n ≫ q = colimit.ι E n from Sigma.ι_comp_desc _ n]
    change _ = a.hom ≫ (Pi.lift (fun n : ℕ ↦
      (TelescopeHomRoosProof.ordinaryCone O X).π.app (op n))) ≫ _
    rw [Pi.lift_comp_π]
    exact (ha (op n)).symm
  let v : Arrow.mk (-T.map u.op) ≅ Arrow.mk (-δ) :=
    Arrow.isoMk b b (by
      change b.hom ≫ (-δ) = (-T.map u.op) ≫ b.hom
      simpa only [Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg hu.symm)
  let z := (shiftFunctor _ (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso _ _
      (fun j : ℤ ↦ ⟨j - 1, TelescopeHomRoosProof.pred_rel j⟩) v)
  have hz₁ (n : ℤ) : z.hom.f n ≫
      HomologicalComplex.homotopyCofiber.fstX (-δ) (n - 1) n
        (TelescopeHomRoosProof.pred_rel n) =
      HomologicalComplex.homotopyCofiber.fstX (-T.map u.op) (n - 1) n
        (TelescopeHomRoosProof.pred_rel n) ≫ b.hom.f n := by
    exact TelescopeHomRoosProof.coneMap_first _ _ v.hom n
  have hz₂ (n : ℤ) : z.hom.f n ≫
      HomologicalComplex.homotopyCofiber.sndX (-δ) (n - 1) =
      HomologicalComplex.homotopyCofiber.sndX (-T.map u.op) (n - 1) ≫
        b.hom.f (n - 1) := by
    exact TelescopeHomRoosProof.coneMap_second _ _ v.hom (n - 1)
  let t := TelescopeHomRoosProof.coneDualIso P I u ≪≫ z
  refine ⟨Arrow.isoMk a t ?_⟩
  have hcmp₁ (n : ℤ) : (ExactProductsRoos.comparison.app X).f n ≫
      HomologicalComplex.homotopyCofiber.fstX (-δ) (n - 1) n
        (TelescopeHomRoosProof.pred_rel n) =
      (ExactProductsRoos.inclusion.app X).f n := by
    change (ExactProductsRoos.comparisonApp X).f n ≫ _ = _
    rw [ExactProductsRoos.comparisonApp_f]
    change ((ExactProductsRoos.inclusion.app X).f n ≫
      HomologicalComplex.homotopyCofiber.inlX (-δ) n (n - 1)
        (TelescopeHomRoosProof.pred_rel n)) ≫ _ = _
    rw [Category.assoc, HomologicalComplex.homotopyCofiber.inlX_fstX,
      Category.comp_id]
  have hcmp₂ (n : ℤ) : (ExactProductsRoos.comparison.app X).f n ≫
      HomologicalComplex.homotopyCofiber.sndX (-δ) (n - 1) = 0 := by
    change (ExactProductsRoos.comparisonApp X).f n ≫ _ = _
    rw [ExactProductsRoos.comparisonApp_f]
    change ((ExactProductsRoos.inclusion.app X).f n ≫
      HomologicalComplex.homotopyCofiber.inlX (-δ) n (n - 1)
        (TelescopeHomRoosProof.pred_rel n)) ≫ _ = _
    rw [Category.assoc, HomologicalComplex.homotopyCofiber.inlX_sndX, comp_zero]
  exact TelescopeHomRoosProof.coneDual_square P I u f (-δ) a b.hom b.hom z hz₁ hz₂
    (ExactProductsRoos.comparison.app X) (ExactProductsRoos.inclusion.app X)
    hcmp₁ hcmp₂ (by rw [hf₁]; exact hq) hf₂

end CategoryTheory
