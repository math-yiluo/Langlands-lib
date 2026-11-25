/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import all WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones

/-! # Additive realization of a family of strict augmentation cones

Source: Stacks Project, derived.tex, definition-cone and lemma-functorial-cone.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/- The additive cone calculation below is the finite calculation from
PrincipalConeExactEquivalence. Keeping its proved private helpers here avoids
loading the principal-completion and derived-slice theory for this finite result. -/
namespace ConeNaturality
open HomologicalComplex CochainComplex CochainComplex.HomComplex
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (H : A ⥤ B) [H.Additive]
private theorem mapCone_inl {X Y : CochainComplex A ℤ}
    (f : X ⟶ Y) (p q : ℤ) (hpq : p + -1 = q) :
    H.map ((mappingCone.inl f).v p q hpq) ≫
      (mappingCone.mapHomologicalComplexIso f H).hom.f q =
        (mappingCone.inl ((H.mapHomologicalComplex (.up ℤ)).map f)).v p q hpq := by
  change H.map ((mappingCone.inl f).v p q hpq) ≫
    (mappingCone.mapHomologicalComplexXIso f H q).hom = _
  rw [mappingCone.mapHomologicalComplexXIso_eq f H q p (by omega)]
  simp only [mappingCone.mapHomologicalComplexXIso'_hom, Preadditive.comp_add,
    ← H.map_comp_assoc, mappingCone.inl_v_fst_v, mappingCone.inl_v_snd_v,
    H.map_id, H.map_zero, Category.id_comp, Limits.zero_comp, add_zero]

private theorem mapCone_ext {X Y : CochainComplex A ℤ} (f : X ⟶ Y) (n : ℤ)
    {Z : B} (a b : H.obj ((mappingCone f).X n) ⟶ Z)
    (h₁ : H.map ((mappingCone.inl f).v (n + 1) n (by omega)) ≫ a =
      H.map ((mappingCone.inl f).v (n + 1) n (by omega)) ≫ b)
    (h₂ : H.map ((mappingCone.inr f).f n) ≫ a =
      H.map ((mappingCone.inr f).f n) ≫ b) : a = b := by
  have hid := congrArg H.map (mappingCone.id_X f n (n + 1) rfl)
  simp only [H.map_add, H.map_comp, H.map_id] at hid
  calc
    a = (H.map ((mappingCone.fst f).1.v n (n + 1) rfl) ≫
        H.map ((mappingCone.inl f).v (n + 1) n (by omega)) +
      H.map ((mappingCone.snd f).v n n (add_zero n)) ≫
        H.map ((mappingCone.inr f).f n)) ≫ a := by rw [hid, Category.id_comp]
    _ = _ := by rw [Preadditive.add_comp, Category.assoc, Category.assoc, h₁, h₂]
    _ = b := by rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      hid, Category.id_comp]

private theorem mapCone_natural {X Y X' Y' : CochainComplex A ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    let G := H.mapHomologicalComplex (.up ℤ)
    G.map (mappingCone.map f g a b h) ≫ (mappingCone.mapHomologicalComplexIso g H).hom =
      (mappingCone.mapHomologicalComplexIso f H).hom ≫
        mappingCone.map (G.map f) (G.map g) (G.map a) (G.map b)
          (by rw [← G.map_comp, ← G.map_comp, h]) := by
  dsimp only
  ext n
  apply mapCone_ext H f n
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      ← H.map_comp_assoc]
    simp only [Int.reduceNeg, mappingCone.map, mappingCone.inl_v_desc_f,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Functor.map_comp,
      ← Category.assoc, mapCone_inl,
      Functor.mapHomologicalComplex_map_f]
    rw [Category.assoc, mapCone_inl]
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      ← H.map_comp_assoc]
    have hf := congrArg (fun z ↦ z.f n) (mappingCone.map_inr f H)
    have hg := congrArg (fun z ↦ z.f n) (mappingCone.map_inr g H)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hf hg
    simp only [mappingCone.map, Int.reduceNeg, mappingCone.inr_f_desc_f, comp_f,
      Functor.map_comp, ← Category.assoc, hf,
      Functor.mapHomologicalComplex_map_f]
    rw [Category.assoc, hg]

end ConeNaturality

private theorem cofiberMap_eq_coneMap
    {V : Type*} [Category V] [Abelian V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : a ≫ g = f ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      CochainComplex.mappingCone.map f g a b h.symm := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain, CochainComplex.HomComplex.Cochain.comp_v,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.fst,
    CochainComplex.mappingCone.snd, CochainComplex.mappingCone.inr]

private def coneIso
    {V : Type*} [Category V] [Abelian V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ≅ K') (b : L ≅ L') (h : f ≫ b.hom = a.hom ≫ g) :
    CochainComplex.mappingCone f ≅ CochainComplex.mappingCone g where
  hom := CochainComplex.mappingCone.map f g a.hom b.hom h
  inv := CochainComplex.mappingCone.map g f a.inv b.inv (by
    apply (cancel_epi a.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact CochainComplex.mappingCone.map_id f
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact CochainComplex.mappingCone.map_id g

private theorem coneIso_natural
    {V : Type*} [Category V] [Abelian V]
    {K₁ L₁ K₂ L₂ K₁' L₁' K₂' L₂' : CochainComplex V ℤ}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (g₁ : K₁' ⟶ L₁') (g₂ : K₂' ⟶ L₂')
    (a₁ : K₁ ≅ K₁') (b₁ : L₁ ≅ L₁') (a₂ : K₂ ≅ K₂') (b₂ : L₂ ≅ L₂')
    (h₁ : f₁ ≫ b₁.hom = a₁.hom ≫ g₁) (h₂ : f₂ ≫ b₂.hom = a₂.hom ≫ g₂)
    (t : K₁ ⟶ K₂) (q : L₁ ⟶ L₂) (h : f₁ ≫ q = t ≫ f₂)
    (t' : K₁' ⟶ K₂') (q' : L₁' ⟶ L₂') (h' : g₁ ≫ q' = t' ≫ g₂)
    (ht : t ≫ a₂.hom = a₁.hom ≫ t') (hq : q ≫ b₂.hom = b₁.hom ≫ q') :
    CochainComplex.mappingCone.map f₁ f₂ t q h ≫ (coneIso f₂ g₂ a₂ b₂ h₂).hom =
      (coneIso f₁ g₁ a₁ b₁ h₁).hom ≫ CochainComplex.mappingCone.map g₁ g₂ t' q' h' := by
  dsimp only [coneIso]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  simp only [ht, hq]

/-- Natural comparisons of the sources of epimorphic augmentations force the
quotient comparisons and induce natural comparisons of the strict cone families.

Source: Stacks Project, derived.tex, definition-cone and lemma-functorial-cone.
(auxiliary; not a blueprint node).
Proof: cancel each epimorphic augmentation in its strict transition square to
obtain naturality on targets. Apply the additive cone comparison, the cone map
of the source/target isomorphisms, and evaluation of the tower cone. Cone-map
composition proves naturality. This is a generic finite categorical calculation;
no Koszul or coefficient hypotheses enter. -/
theorem additiveConeFamilyComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    (K L : ℕ → CochainComplex C ℤ) (f : ∀ n, K n ⟶ L n)
    (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (q : ∀ n m : ℕ, n ≤ m → (L m ⟶ L n))
    (hc : ∀ n m h, t n m h ≫ f n = f m ≫ q n m h)
    {T Q : ℕᵒᵖ ⥤ CochainComplex D ℤ} (ε : T ⟶ Q)
    (eK : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.obj (op n))
    (eQ : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (L n) ≅ Q.obj (op n))
    (haug : ∀ n, (E.mapHomologicalComplex (.up ℤ)).map (f n) ≫ (eQ n).hom =
      (eK n).hom ≫ ε.app (op n))
    (ht : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map (t n m h) ≫ (eK n).hom =
      (eK m).hom ≫ T.map (homOfLE h).op)
    (hfepi : ∀ n, Epi ((E.mapHomologicalComplex (.up ℤ)).map (f n))) :
    ∃ e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.homotopyCofiber (f n)) ≅
      (CochainComplex.mappingCone
        ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.obj
          (op n),
      ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom (f m) (f n)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk (t n m h) (q n m h) (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫ (CochainComplex.mappingCone
          ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.map
            (homOfLE h).op := by
  let H := E.mapHomologicalComplex (.up ℤ)
  have (n : ℕ) : Epi (H.map (f n)) := hfepi n
  have hqn (n m : ℕ) (h : n ≤ m) :
      H.map (q n m h) ≫ (eQ n).hom = (eQ m).hom ≫ Q.map (homOfLE h).op := by
    apply (cancel_epi (H.map (f m))).1
    rw [← H.map_comp_assoc, ← hc n m h, H.map_comp, Category.assoc, haug,
      ← Category.assoc, ht n m h, Category.assoc, ε.naturality,
      ← Category.assoc, ← haug, Category.assoc]
  let W := (CochainComplex.mappingCone
    ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor
  let z (n : ℕ) : CochainComplex.mappingCone (ε.app (op n)) ≅ W.obj (op n) :=
    (levelConeTowerIso ε).symm.app (op n)
  have hz (n m : ℕ) (h : n ≤ m) :
      CochainComplex.mappingCone.map (ε.app (op m)) (ε.app (op n))
        (T.map (homOfLE h).op) (Q.map (homOfLE h).op)
        (ε.naturality (homOfLE h).op).symm ≫ (z n).hom =
      (z m).hom ≫ W.map (homOfLE h).op :=
    (levelConeTowerIso ε).inv.naturality (homOfLE h).op
  let e (n : ℕ) := CochainComplex.mappingCone.mapHomologicalComplexIso (f n) E ≪≫
    coneIso (H.map (f n)) (ε.app (op n)) (eK n) (eQ n) (haug n) ≪≫ z n
  refine ⟨e, ?_⟩
  intro n m h
  rw [cofiberMap_eq_coneMap]
  dsimp only [e, Iso.trans_hom, Iso.app_hom]
  change H.map (CochainComplex.mappingCone.map (f m) (f n)
      (t n m h) (q n m h) (hc n m h).symm) ≫ _ = _
  rw [← Category.assoc, ConeNaturality.mapCone_natural]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((z n).hom), coneIso_natural]
  · simp only [Category.assoc]
    rw [hz n m h]
  · exact (ε.naturality (homOfLE h).op).symm
  · exact ht n m h
  · exact hqn n m h

end CategoryTheory
