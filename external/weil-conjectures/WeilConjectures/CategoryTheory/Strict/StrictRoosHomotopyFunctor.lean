/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# The strict Roos functor on compatible homotopies

Source: Stacks Project, derived.tex, Tags 014E (definition-cone),
08TC (definition-derived-limit), 013H (definition-complexes-notation),
and dga.tex, Tag 09MJ (definition-linear-category).
(blueprint: lem-pur-strict-roos-homotopy-functor)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

private noncomputable abbrev pπ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) (n : ℕ) :
    (roosP X).X i ⟶ (X.X i).obj (op n) :=
  (Pi.π (fun m : ℕ ↦ X.asFunctor.obj (op m)) n).f i

private noncomputable def pLimit (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) :=
  isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
    (fun n : ℕ ↦ X.asFunctor.obj (op n))

private theorem p_ext {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {i : ℤ} {B : A}
    {a b : B ⟶ (roosP X).X i} (h : ∀ n : ℕ, a ≫ pπ X i n = b ≫ pπ X i n) :
    a = b := by
  apply (pLimit X i).hom_ext
  rintro ⟨n⟩
  exact h n

private noncomputable def pHom {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {i j : ℤ}
    (a : X.X i ⟶ Y.X j) : (roosP X).X i ⟶ (roosP Y).X j :=
  (pLimit Y j).lift (Fan.mk _ (fun n : ℕ ↦ pπ X i n ≫ a.app (op n)))

private theorem pHom_π {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {i j : ℤ}
    (a : X.X i ⟶ Y.X j) (n : ℕ) :
    pHom a ≫ pπ Y j n = pπ X i n ≫ a.app (op n) :=
  (pLimit Y j).fac _ ⟨n⟩

private theorem pmap_π {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y)
    (i : ℤ) (n : ℕ) :
    (roosPmap f).f i ≫ pπ Y i n = pπ X i n ≫ (f.f i).app (op n) := by
  simpa only [roosPmap, HomologicalComplex.comp_f, pπ,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f] using
    congrArg (fun f ↦ f.f i) (Pi.map_π
      (fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) n)

private theorem pd_π (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i j : ℤ) (n : ℕ) :
    (roosP X).d i j ≫ pπ X j n = pπ X i n ≫ (X.d i j).app (op n) :=
  ((Pi.π (fun m : ℕ ↦ X.asFunctor.obj (op m)) n).comm i j).symm

private theorem pu_π (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) (n : ℕ) :
    (roosU X).f i ≫ pπ X i n = pπ X i n -
      pπ X i (n + 1) ≫ (X.X i).map (homOfLE (Nat.le_succ n)).op := by
  simpa only [roosU, HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
    HomologicalComplex.asFunctor_map_f, pπ] using
    congrArg (fun (f : roosP X ⟶ X.asFunctor.obj (op n)) ↦ f.f i)
    ((towerTransitionEndomorphism_eq_iff
      (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n)

private theorem pHom_u {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {i j : ℤ}
    (a : X.X i ⟶ Y.X j) :
    pHom a ≫ (roosU Y).f j = (roosU X).f i ≫ pHom a := by
  apply p_ext
  intro n
  simp only [Category.assoc, pu_π, Preadditive.comp_sub, pHom_π,
    reassoc_of% pHom_π, reassoc_of% pu_π, Preadditive.sub_comp]
  rw [a.naturality]

private theorem pHom_comm {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {f g : X ⟶ Y}
    (h : Homotopy f g) (p : ℤ) :
    (roosPmap f).f (p + 1) =
      (roosP X).d (p + 1) (p + 1 + 1) ≫ pHom (h.hom (p + 1 + 1) (p + 1)) +
      pHom (h.hom (p + 1) p) ≫ (roosP Y).d p (p + 1) +
      (roosPmap g).f (p + 1) := by
  apply p_ext
  intro n
  simp only [Preadditive.add_comp, Category.assoc, pmap_π, pHom_π,
    reassoc_of% pd_π, reassoc_of% pHom_π, pd_π]
  have hc := h.comm (p + 1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (p + 1) (p + 1 + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)] at hc
  have hn := congrArg (fun a ↦ pπ X (p + 1) n ≫ a.app (op n)) hc
  simpa only [NatTrans.comp_app, NatTrans.app_add, Preadditive.comp_add,
    Category.assoc] using hn

private theorem roos_additive : (roosF (A := A)).Additive where
  map_add {X Y f g} := by
    have hadd (i : ℤ) : (roosPmap (f + g)).f i =
        (roosPmap f).f i + (roosPmap g).f i := by
      apply p_ext
      intro n
      simp [Preadditive.add_comp, pmap_π, Preadditive.comp_add]
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change (roosF.map (f + g)).f (p + 1) =
      (roosF.map f).f (p + 1) + (roosF.map g).f (p + 1)
    apply (cancel_mono (roosχ Y p).hom).1
    simp only [Preadditive.add_comp, roosF_map_χ,
      hadd, ← Preadditive.comp_add]
    congr 1
    apply biprod.hom_ext <;> simp [Preadditive.add_comp, Preadditive.comp_add]

private theorem roos_linear (k : Type w) [CommRing k] [Linear k A] :
    (roosF (A := A)).Linear k where
  map_smul {X Y} f r := by
    have hsmul (i : ℤ) : (roosPmap (r • f)).f i = r • (roosPmap f).f i := by
      apply p_ext
      intro n
      simp [Linear.smul_comp, pmap_π, Linear.comp_smul]
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change (roosF.map (r • f)).f (p + 1) = r • (roosF.map f).f (p + 1)
    apply (cancel_mono (roosχ Y p).hom).1
    simp only [Linear.smul_comp, roosF_map_χ,
      hsmul, ← Linear.comp_smul]
    congr 1
    apply biprod.hom_ext <;> simp [Linear.smul_comp, Linear.comp_smul]

private noncomputable abbrev cχ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) :
    (roosConeFunctor.obj X).X i ≅ (roosP X).X (i + 1) ⊞ (roosP X).X i :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) i (i + 1) rfl

private theorem cone_map_χ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y)
    (i : ℤ) :
    (roosConeFunctor.map f).f i ≫ (cχ Y i).hom =
      (cχ X i).hom ≫ biprod.map ((roosPmap f).f (i + 1)) ((roosPmap f).f i) := by
  apply CochainComplex.mappingCone.ext_from (roosU X) (i + 1) i rfl
  · change (CochainComplex.mappingCone.inl (roosU X)).v (i + 1) i (by omega) ≫
        (CochainComplex.mappingCone.map _ _ (roosPmap f) (roosPmap f)
          (roosU_natural f)).f i ≫ _ = _
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
    simp only [CochainComplex.mappingCone.inl,
      CochainComplex.HomComplex.Cochain.mk_v, Category.assoc, cχ,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    apply biprod.hom_ext <;> simp
  · change (CochainComplex.mappingCone.inr (roosU X)).f i ≫
        (CochainComplex.mappingCone.map _ _ (roosPmap f) (roosPmap f)
          (roosU_natural f)).f i ≫ _ = _
    rw [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc]
    simp only [HomologicalComplex.comp_f, CochainComplex.mappingCone.inr, Category.assoc]
    apply biprod.hom_ext <;> simp [cχ]

private theorem cone_d_χ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) :
    (roosConeFunctor.obj X).d i (i + 1) ≫ (cχ X (i + 1)).hom =
      (cχ X i).hom ≫ biprod.lift
        (-(biprod.fst ≫ (roosP X).d (i + 1) (i + 1 + 1)))
        (biprod.fst ≫ (roosU X).f (i + 1) +
          biprod.snd ≫ (roosP X).d i (i + 1)) := by
  change HomologicalComplex.homotopyCofiber.d (roosU X) i (i + 1) ≫ _ = _
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.lift_fst, Preadditive.comp_neg, cχ,
      HomologicalComplex.homotopyCofiber.fstX] using
        HomologicalComplex.homotopyCofiber.d_fstX (roosU X) i (i + 1) (i + 1 + 1) rfl rfl
  · have hs (r q : ℤ) (hr : (ComplexShape.up ℤ).Rel r q) :
        HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hr).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' hr
      dsimp only [HomologicalComplex.homotopyCofiber.sndX]
      rw [dite_eq_left hr]
    simpa only [Category.assoc, biprod.lift_snd, Preadditive.comp_add, cχ,
      HomologicalComplex.homotopyCofiber.fstX, hs i (i + 1) rfl,
      hs (i + 1) (i + 1 + 1) rfl] using
        HomologicalComplex.homotopyCofiber.d_sndX (roosU X) i (i + 1) rfl

private noncomputable def coneHom {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) (i j : ℤ) :
    (roosConeFunctor.obj X).X i ⟶ (roosConeFunctor.obj Y).X j :=
  (cχ X i).hom ≫ biprod.map (-pHom (h.hom (i + 1) (j + 1))) (pHom (h.hom i j)) ≫
    (cχ Y j).inv

private theorem coneHom_comm {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) (p : ℤ) :
    (roosConeFunctor.map f).f (p + 1) =
      (roosConeFunctor.obj X).d (p + 1) (p + 1 + 1) ≫ coneHom h (p + 1 + 1) (p + 1) +
      coneHom h (p + 1) p ≫ (roosConeFunctor.obj Y).d p (p + 1) +
      (roosConeFunctor.map g).f (p + 1) := by
  apply (cancel_mono (cχ Y (p + 1)).hom).1
  simp only [Preadditive.add_comp, Category.assoc, cone_map_χ, coneHom,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, cone_d_χ, cone_d_χ Y p]
  simp only [← Category.assoc]
  simp only [Category.assoc, ← Preadditive.comp_add]
  congr 1
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp only [biprod.map_fst, biprod.map_snd, biprod.inl_fst_assoc,
      biprod.inl_snd_assoc, biprod.inr_fst_assoc, biprod.inr_snd_assoc,
      Iso.inv_hom_id_assoc, Preadditive.add_comp, Category.assoc, Preadditive.comp_neg,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.neg_comp, neg_neg,
      biprod.lift_fst, biprod.lift_snd, biprod.map_fst_assoc, biprod.map_snd_assoc,
      Preadditive.comp_add, zero_comp, zero_add, add_zero, neg_zero]
  · exact pHom_comm h (p + 1)
  · rw [pHom_u]
    abel
  · exact pHom_comm h p

private noncomputable def coneHomotopy {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy (roosConeFunctor.map f) (roosConeFunctor.map g) where
  hom := coneHom h
  zero i j hij := by
    have hij' : ¬ (ComplexShape.up ℤ).Rel (j + 1) (i + 1) := by
      dsimp at hij ⊢
      omega
    have hz {r s : ℤ} (hh : ¬ (ComplexShape.up ℤ).Rel s r) :
        pHom (h.hom r s) = 0 := by
      apply p_ext
      intro n
      simp [pHom_π, h.zero r s hh]
    dsimp only [coneHom]
    rw [hz hij, hz hij', neg_zero]
    have hm : biprod.map (0 : (roosP X).X (i + 1) ⟶ (roosP Y).X (j + 1))
        (0 : (roosP X).X i ⟶ (roosP Y).X j) = 0 := by
      apply biprod.hom_ext <;> simp
    rw [hm, zero_comp, comp_zero]
  comm i := by
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective i
    change (roosConeFunctor.map f).f (p + 1) =
      dNext (p + 1) (coneHom h) + prevD (p + 1) (coneHom h) +
        (roosConeFunctor.map g).f (p + 1)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (p + 1) (p + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)]
    exact coneHom_comm h p

omit [HasCountableProducts A] in
private theorem shift_hom_coordinates {K L : CochainComplex A ℤ} {f g : K ⟶ L}
    (H : Homotopy f g) (n i j i' j' : ℤ) (hi : i' = i + n) (hj : j' = j + n) :
    (H.shift n).hom i j ≫ (L.shiftFunctorObjXIso n j j' hj).hom =
      n.negOnePow • ((K.shiftFunctorObjXIso n i i' hi).hom ≫ H.hom i' j') := by
  subst i' j'
  simp [Homotopy.shift, CochainComplex.shiftFunctorObjXIso]

private noncomputable def roosHomotopy {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) : Homotopy (roosF.map f) (roosF.map g) :=
  (coneHomotopy h).shift (-1)

private theorem roosHomotopy_χ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {f g : X ⟶ Y} (h : Homotopy f g) (p : ℤ) :
    (roosHomotopy h).hom (p + 1 + 1) (p + 1) ≫ (roosχ Y p).hom =
      (roosχ X (p + 1)).hom ≫
        biprod.map (-pHom (h.hom (p + 1) p)) (pHom (h.hom (p + 1 + 1) (p + 1))) := by
  change ((coneHomotopy h).shift (-1)).hom (p + 1 + 1) (p + 1) ≫
      (((roosConeFunctor.obj Y).shiftFunctorObjXIso (-1) (p + 1) p (by omega)).hom ≫
        (cχ Y p).hom ≫ (biprod.braiding _ _).hom) =
    (((roosConeFunctor.obj X).shiftFunctorObjXIso (-1) (p + 1 + 1) (p + 1)
      (by omega)).hom ≫ (cχ X (p + 1)).hom ≫ (biprod.braiding _ _).hom) ≫
        biprod.map (-pHom (h.hom (p + 1) p)) (pHom (h.hom (p + 1 + 1) (p + 1)))
  simp only [Category.assoc]
  rw [← Category.assoc, shift_hom_coordinates
    (coneHomotopy h) (-1) (p + 1 + 1) (p + 1) (p + 1) p (by omega) (by omega)]
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    coneHomotopy, coneHom, Category.assoc, Iso.inv_hom_id_assoc,
    Preadditive.neg_comp]
  simp only [← Preadditive.comp_neg]
  congr 1
  congr 1
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]

/-- The fixed strict Roos cone is additive, sends a compatible tower homotopy to the
signed diagonal product homotopy, and descends to an additive functor on homotopy
categories. Both functors are linear whenever the coefficient category is linear.
The two projection equations express exactly `(-h_P y, h_P x)` in the coordinates
`roosχ`, without treating objects of an arbitrary abelian category as sets.

Source: Stacks Project, derived.tex, Tags 014E (definition-cone),
08TC (definition-derived-limit), 013H (definition-complexes-notation);
homology.tex, Tag 0112; dga.tex, Tag 09MJ (definition-linear-category).
(blueprint: lem-pur-strict-roos-homotopy-functor)

Proof plan:
1. Use the universal property of termwise products: product maps preserve identities,
composition and addition, since these equations hold after every projection.
2. Strictness gives `s_Y F = F s_X`, hence `v_Y F = F v_X`. The diagonal product maps
therefore commute with the signed cone differential and give the existing `roosF`.
3. The same projection calculation proves additivity of this cochain functor.
4. A homotopy in the tower category has natural-transformation components: these are
exactly the transition-compatible levelwise homotopies. Products give `F-G=dH+Hd`
and `v_Y H = H v_X`, without any exactness hypothesis on products.
5. For `T(y,x)=(-Hy,Hx)`, compute `DT+TD`. Its diagonal blocks are `dH+Hd`;
the off-diagonal block is `Hv_X-v_Y H=0`. This proves the two signed projection
formulas below and the homotopy equation.
6. Homotopy is a congruence: zero, negation and addition give reflexivity, symmetry
and transitivity, and composition sends a homotopy to `b h a`. All preserve tower
compatibility. Thus chain maps modulo compatible homotopy form the stated source.
7. Descend `roosF` using this congruence. Its quotient factorization gives precisely
`X ↦ R(X)` and `[f] ↦ [R(f)]`; identities, composition and addition descend as well.
8. In a linear category, products and biproduct components commute with scalars.
Multiplying a homotopy by a scalar preserves its equation and transition compatibility.
Thus both the cochain functor and its homotopy quotient preserve scalars.
The definitions used are def-weil-strict-roos-model, def-weil-inverse-system,
def-weil-abstract-derived-category, def-sp-abelian, def-weil-category-product,
and def-weil-linear-category. -/
theorem roosF_homotopy_functor
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A] :
    (roosF (A := A)).Additive ∧
    (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (f g : X ⟶ Y) (h : Homotopy f g),
      ∃ H : Homotopy (roosF.map f) (roosF.map g), ∀ (p : ℤ) (n : ℕ),
        (H.hom ((p + 1) + 1) (p + 1) ≫ (roosχ Y p).hom ≫ biprod.fst ≫
          (Pi.π (fun m : ℕ ↦ Y.asFunctor.obj (op m)) n).f p =
          -((roosχ X (p + 1)).hom ≫ biprod.fst ≫
            (Pi.π (fun m : ℕ ↦ X.asFunctor.obj (op m)) n).f (p + 1) ≫
            (h.hom (p + 1) p).app (op n))) ∧
        (H.hom ((p + 1) + 1) (p + 1) ≫ (roosχ Y p).hom ≫ biprod.snd ≫
          (Pi.π (fun m : ℕ ↦ Y.asFunctor.obj (op m)) n).f (p + 1) =
          (roosχ X (p + 1)).hom ≫ biprod.snd ≫
            (Pi.π (fun m : ℕ ↦ X.asFunctor.obj (op m)) n).f ((p + 1) + 1) ≫
            (h.hom ((p + 1) + 1) (p + 1)).app (op n))) ∧
    (∃ RF : HomotopyCategory (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        HomotopyCategory A (ComplexShape.up ℤ),
      RF.Additive ∧
      HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⋙ RF =
        roosF ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) ∧
      ∀ (k : Type w) [CommRing k] [Linear k A],
        (roosF (A := A)).Linear k ∧ RF.Linear k) := by
  have ha := roos_additive (A := A)
  refine ⟨ha, ?_, ?_⟩
  · intro X Y f g h
    refine ⟨roosHomotopy h, ?_⟩
    intro p n
    constructor
    · rw [reassoc_of% roosHomotopy_χ]
      change (roosχ X (p + 1)).hom ≫
        biprod.map (-pHom (h.hom (p + 1) p))
          (pHom (h.hom (p + 1 + 1) (p + 1))) ≫ biprod.fst ≫ pπ Y p n =
        -((roosχ X (p + 1)).hom ≫ biprod.fst ≫ pπ X (p + 1) n ≫
          (h.hom (p + 1) p).app (op n))
      simp only [biprod.map_fst_assoc, Preadditive.neg_comp, Preadditive.comp_neg,
        pHom_π]
    · rw [reassoc_of% roosHomotopy_χ]
      change (roosχ X (p + 1)).hom ≫
        biprod.map (-pHom (h.hom (p + 1) p))
          (pHom (h.hom (p + 1 + 1) (p + 1))) ≫ biprod.snd ≫ pπ Y (p + 1) n =
        (roosχ X (p + 1)).hom ≫ biprod.snd ≫ pπ X (p + 1 + 1) n ≫
          (h.hom (p + 1 + 1) (p + 1)).app (op n)
      simp only [biprod.map_snd_assoc, pHom_π]
  · let RF : HomotopyCategory (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        HomotopyCategory A (ComplexShape.up ℤ) :=
      Quotient.lift _ (roosF ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (fun X Y f g ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _ (roosHomotopy h))
    have he : HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⋙ RF =
        roosF ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) :=
      Quotient.lift_spec _ _ _
    have hRF : RF.Additive := by
      have : (HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⋙ RF).Additive := by
        rw [he]
        infer_instance
      exact Functor.additive_of_full_essSurj_comp
        (HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) RF
    refine ⟨RF, hRF, he, ?_⟩
    intro k _ _
    have hk := roos_linear (A := A) k
    refine ⟨hk, ?_⟩
    have : (HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⋙ RF).Linear k := by
      rw [he]
      infer_instance
    exact Functor.linear_of_full_essSurj_comp
      (HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) RF

end CategoryTheory
