/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Signed product Hom and a source mapping cone

Source: Stacks Project, Tag 08JC, `lemma-RHom-triangulated`, omitted termwise-split
calculation, generalized to separately additive bifunctors using the signed differential
of `WeilConjectures.Algebra.Homology.BifunctorHomComplex`.
(used for `proposition-six-operations-dctf--15`)

The two coordinate maps below use the actual shifted mapping cone, rather than a
replacement complex. Mathlib orders the source-shifted summand first in a mapping cone;
thus its `snd` becomes the `y` coordinate and its `fst` becomes the `x` coordinate.
The main statement supplies a family of chain isomorphisms with both coordinate
formulas, inverse formulas, the differential, restriction, and naturality.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Abelian A] [Abelian B] [Abelian C] [HasCountableProducts C]
  (H : Aᵒᵖ ⥤ B ⥤ C) [H.Additive] [∀ M : Aᵒᵖ, (H.obj M).Additive]
  (I : CochainComplex B ℤ)

/-- The `y : U(K)^(n-1)` projection from the actual `Cone(U(f))[-1]`.
Source: Stacks Project, Tag 08JC, omitted split Hom calculation, with the cone and shift
of Tag 014P (used for `proposition-six-operations-dctf--15`). -/
noncomputable def bifunctorHomConeY {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧).X n ⟶
      (bifunctorHomObj H K I).X (n - 1) :=
  ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f)).shiftFunctorObjXIso
    (-1) n (n - 1) rfl).hom ≫
    (mappingCone.snd (bifunctorHomMapLeft (H := H) (Y := I) f)).v
      (n - 1) (n - 1) (add_zero (n - 1))

/-- The `x : U(L)^n` projection from the actual `Cone(U(f))[-1]`.
Source: Stacks Project, Tag 08JC, omitted split Hom calculation, with the cone and shift
of Tag 014P (used for `proposition-six-operations-dctf--15`). -/
noncomputable def bifunctorHomConeX {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧).X n ⟶
      (bifunctorHomObj H L I).X n :=
  ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f)).shiftFunctorObjXIso
    (-1) n (n - 1) rfl).hom ≫
    (mappingCone.fst (bifunctorHomMapLeft (H := H) (Y := I) f)).1.v
      (n - 1) n (sub_add_cancel n 1)

open HomComplex

-- The cone cocycle has coordinates (restriction to L, minus signed restriction to K[1]).
-- Its cocycle equation is the image of δ(inl f) = f ≫ inr f under signed precomposition.
private noncomputable def signedConeHom {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    bifunctorHomObj H (mappingCone f) I ⟶
      (mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧ :=
  Cocycle.homOf ((mappingCone.liftCocycle
    (bifunctorHomMapLeft (H := H) (Y := I) f)
    (Cocycle.ofHom (bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.inr f)))
    (-bifunctorHomMapLeftCochain (H := H) (Y := I) (mappingCone.inl f))
    (by omega) (by
      rw [δ_neg, δ_bifunctorHomMapLeftCochain (-1) 0 (by omega), mappingCone.δ_inl,
        bifunctorHomMapLeftCochain_ofHom, bifunctorHomMapLeft_comp,
        Cochain.ofHom_comp, Cocycle.ofHom_coe]
      exact neg_add_cancel _)).rightShift (-1) 0 (by omega))

@[reassoc]
private lemma signedConeHom_x {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (signedConeHom H I f).f n ≫ bifunctorHomConeX H I f n =
      (bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.inr f)).f n := by
  unfold signedConeHom bifunctorHomConeX
  rw [← Cochain.ofHom_v, Cocycle.cochain_ofHom_homOf_eq_coe,
    Cocycle.rightShift_coe, Cochain.rightShift_v _ (-1) 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, mappingCone.liftCocycle_coe,
    mappingCone.liftCochain_v_fst_v, Cocycle.ofHom_coe, Cochain.ofHom_v]

@[reassoc]
private lemma signedConeHom_y {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (signedConeHom H I f).f n ≫ bifunctorHomConeY H I f n =
      -(bifunctorHomMapLeftCochain (H := H) (Y := I) (mappingCone.inl f)).v
        n (n - 1) (by omega) := by
  unfold signedConeHom bifunctorHomConeY
  rw [← Cochain.ofHom_v, Cocycle.cochain_ofHom_homOf_eq_coe,
    Cocycle.rightShift_coe, Cochain.rightShift_v _ (-1) 0 (by omega) n n (by omega)
      (n - 1) (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, mappingCone.liftCocycle_coe,
    mappingCone.liftCochain_v_snd_v, Cochain.neg_v]

@[reassoc]
private lemma signedConeHom_y_π {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (n p q : ℤ) (hpq : p + n = q) :
    (signedConeHom H I f).f n ≫ bifunctorHomConeY H I f n ≫
        bifunctorHomπ H K I (n - 1) (p + 1) q (by omega) =
      p.negOnePow • (bifunctorHomπ H (mappingCone f) I n p q hpq ≫
        (H.map ((mappingCone.inl f).v (p + 1) p (by omega)).op).app (I.X q)) := by
  rw [← Category.assoc, signedConeHom_y, Preadditive.neg_comp,
    bifunctorHomMapLeftCochain_v_π _ n (n - 1) (by omega) (p + 1) q (by omega)
      p (by omega) hpq]
  simp only [mul_neg_one, Int.negOnePow_neg, Int.negOnePow_succ, Units.neg_smul,
    neg_neg]

-- Reconstruct each product component by the two source-cone projections.
private noncomputable def signedConeInv {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (n : ℤ) :
    ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧).X n ⟶
      (bifunctorHomObj H (mappingCone f) I).X n :=
  bifunctorHomLift H (mappingCone f) I n fun p q hpq ↦
    p.negOnePow • (bifunctorHomConeY H I f n ≫
      bifunctorHomπ H K I (n - 1) (p + 1) q (by omega) ≫
      (H.map ((mappingCone.fst f).1.v p (p + 1) rfl).op).app (I.X q)) +
    bifunctorHomConeX H I f n ≫ bifunctorHomπ H L I n p q hpq ≫
      (H.map ((mappingCone.snd f).v p p (add_zero p)).op).app (I.X q)

@[reassoc]
private lemma signedConeInv_y {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (n p q : ℤ) (hpq : p + n = q) :
    signedConeInv H I f n ≫ bifunctorHomπ H (mappingCone f) I n p q hpq ≫
        (H.map ((mappingCone.inl f).v (p + 1) p (by omega)).op).app (I.X q) =
      p.negOnePow • (bifunctorHomConeY H I f n ≫
        bifunctorHomπ H K I (n - 1) (p + 1) q (by omega)) := by
  simp [signedConeInv, Preadditive.add_comp, Linear.units_smul_comp,
    ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]

@[reassoc]
private lemma signedConeInv_x {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (n p q : ℤ) (hpq : p + n = q) :
    signedConeInv H I f n ≫ bifunctorHomπ H (mappingCone f) I n p q hpq ≫
        (H.map ((mappingCone.inr f).f p).op).app (I.X q) =
      bifunctorHomConeX H I f n ≫ bifunctorHomπ H L I n p q hpq := by
  simp [signedConeInv, Preadditive.add_comp, Linear.units_smul_comp,
    ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]

private lemma signedCone_hom_inv {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (signedConeHom H I f).f n ≫ signedConeInv H I f n = 𝟙 _ := by
  apply bifunctorHomObj_hom_ext
  intro p q hpq
  simp only [signedConeInv, Category.assoc, bifunctorHomLift_π,
    Preadditive.comp_add, Linear.comp_units_smul]
  have hy := signedConeHom_y_π H I f n p q hpq
  simp only [← Category.assoc] at hy ⊢
  rw [hy, Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
    signedConeHom_x, bifunctorHomMapLeft_f_π]
  simp only [Category.assoc, ← Preadditive.comp_add, ← NatTrans.comp_app,
    ← Functor.map_comp, ← op_comp, ← NatTrans.app_add, ← Functor.map_add, ← op_add,
    mappingCone.id_X, op_id, Category.id_comp]
  simp

private lemma signedCone_to_ext {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ)
    {T : C} {a b : T ⟶
      ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧).X n}
    (hy : a ≫ bifunctorHomConeY H I f n = b ≫ bifunctorHomConeY H I f n)
    (hx : a ≫ bifunctorHomConeX H I f n = b ≫ bifunctorHomConeX H I f n) : a = b := by
  let t := bifunctorHomMapLeft (H := H) (Y := I) f
  apply (cancel_mono ((mappingCone t).shiftFunctorObjXIso (-1) n (n - 1) rfl).hom).1
  apply mappingCone.ext_to _ (n - 1) n (by omega)
  · simpa only [bifunctorHomConeX, Category.assoc] using hx
  · simpa only [bifunctorHomConeY, Category.assoc] using hy

private lemma signedCone_inv_hom {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    signedConeInv H I f n ≫ (signedConeHom H I f).f n = 𝟙 _ := by
  apply signedCone_to_ext H I f n
  · apply bifunctorHomObj_hom_ext
    intro j q hjq
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, j = p + 1 := ⟨j - 1, by omega⟩
    simp only [Category.assoc, Category.id_comp]
    rw [signedConeHom_y_π H I f n p q (by omega), Linear.comp_units_smul,
      signedConeInv_y H I f n p q (by omega), smul_smul,
      Int.units_mul_self, one_smul]
  · apply bifunctorHomObj_hom_ext
    intro p q hpq
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc _ (bifunctorHomConeX H I f n), signedConeHom_x,
      bifunctorHomMapLeft_f_π, signedConeInv_x]

private noncomputable def signedConeIso {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    bifunctorHomObj H (mappingCone f) I ≅
      (mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ { hom := (signedConeHom H I f).f n
               inv := signedConeInv H I f n
               hom_inv_id := signedCone_hom_inv H I f n
               inv_hom_id := signedCone_inv_hom H I f n })
    (fun n m _ ↦ (signedConeHom H I f).comm n m)

private lemma signedConeHom_d_y {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (bifunctorHomObj H (mappingCone f) I).d n (n + 1) ≫
        (signedConeHom H I f).f (n + 1) ≫ bifunctorHomConeY H I f (n + 1) ≫
        ((bifunctorHomObj H K I).XIsoOfEq (by omega : (n + 1) - 1 = n)).hom =
      -((signedConeHom H I f).f n ≫ bifunctorHomConeY H I f n ≫
        (bifunctorHomObj H K I).d (n - 1) n) -
      (signedConeHom H I f).f n ≫ bifunctorHomConeX H I f n ≫
        (bifunctorHomMapLeft (H := H) (Y := I) f).f n := by
  have h := Cochain.congr_v
    (δ_bifunctorHomMapLeftCochain (H := H) (Y := I) (-1) 0 (by omega)
      (mappingCone.inl f)) n n (add_zero n)
  rw [mappingCone.δ_inl, bifunctorHomMapLeftCochain_ofHom,
    bifunctorHomMapLeft_comp, Cochain.ofHom_comp, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v,
    δ_v (-1) 0 (by omega) _ n n (add_zero n) (n - 1) (n + 1) rfl rfl,
    Int.negOnePow_zero, one_smul] at h
  simp only [signedConeHom_y_assoc, signedConeHom_x_assoc,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Cochain.v_comp_XIsoOfEq_hom]
  rw [← h]
  abel

private lemma signedConeHom_d_x {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (bifunctorHomObj H (mappingCone f) I).d n (n + 1) ≫
        (signedConeHom H I f).f (n + 1) ≫ bifunctorHomConeX H I f (n + 1) =
      (signedConeHom H I f).f n ≫ bifunctorHomConeX H I f n ≫
        (bifunctorHomObj H L I).d n (n + 1) := by
  simp only [← Category.assoc, signedConeHom_x]
  exact ((bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.inr f)).comm n (n + 1)).symm

@[reassoc]
private lemma signedConeMap_x {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : bifunctorHomObj H L' I ⟶ bifunctorHomObj H L I)
    (b : bifunctorHomObj H K' I ⟶ bifunctorHomObj H K I)
    (h : bifunctorHomMapLeft (H := H) (Y := I) f' ≫ b =
      a ≫ bifunctorHomMapLeft (H := H) (Y := I) f) (n : ℤ) :
    ((mappingCone.map _ _ a b h)⟦(-1 : ℤ)⟧').f n ≫ bifunctorHomConeX H I f n =
      bifunctorHomConeX H I f' n ≫ a.f n := by
  let c := mappingCone.map _ _ a b h
  have hc : c.f (n - 1) ≫
      (mappingCone.fst (bifunctorHomMapLeft (H := H) (Y := I) f)).1.v
        (n - 1) n (by omega) =
      (mappingCone.fst (bifunctorHomMapLeft (H := H) (Y := I) f')).1.v
        (n - 1) n (by omega) ≫ a.f n := by
    dsimp only [c]
    rw [mappingCone.map, mappingCone.desc_f _ _ _ _ (n - 1) n (by omega)]
    simp [Preadditive.add_comp, Category.assoc,
      Cochain.comp_v _ _ (zero_add (-1)) n n (n - 1) (add_zero n) (by omega)]
  dsimp only [bifunctorHomConeX]
  rw [← Category.assoc, shiftFunctor_map_f']
  rw [show c.f (n + -1) ≫
      ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f)).shiftFunctorObjXIso
        (-1) n (n - 1) rfl).hom =
      ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f')).shiftFunctorObjXIso
        (-1) n (n - 1) rfl).hom ≫ c.f (n - 1) from
      HomologicalComplex.XIsoOfEq_hom_naturality c (by omega)]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f')).shiftFunctorObjXIso
      (-1) n (n - 1) rfl).hom ≫ z) hc

@[reassoc]
private lemma signedConeMap_y {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (a : bifunctorHomObj H L' I ⟶ bifunctorHomObj H L I)
    (b : bifunctorHomObj H K' I ⟶ bifunctorHomObj H K I)
    (h : bifunctorHomMapLeft (H := H) (Y := I) f' ≫ b =
      a ≫ bifunctorHomMapLeft (H := H) (Y := I) f) (n : ℤ) :
    ((mappingCone.map _ _ a b h)⟦(-1 : ℤ)⟧').f n ≫ bifunctorHomConeY H I f n =
      bifunctorHomConeY H I f' n ≫ b.f (n - 1) := by
  let c := mappingCone.map _ _ a b h
  have hc : c.f (n - 1) ≫
      (mappingCone.snd (bifunctorHomMapLeft (H := H) (Y := I) f)).v
        (n - 1) (n - 1) (add_zero _) =
      (mappingCone.snd (bifunctorHomMapLeft (H := H) (Y := I) f')).v
        (n - 1) (n - 1) (add_zero _) ≫ b.f (n - 1) := by
    dsimp only [c]
    rw [mappingCone.map, mappingCone.desc_f _ _ _ _ (n - 1) n (by omega)]
    simp [Preadditive.add_comp, Category.assoc,
      Cochain.comp_v _ _ (zero_add (-1)) n n (n - 1) (add_zero n) (by omega)]
  dsimp only [bifunctorHomConeY]
  rw [← Category.assoc, shiftFunctor_map_f']
  rw [show c.f (n + -1) ≫
      ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f)).shiftFunctorObjXIso
        (-1) n (n - 1) rfl).hom =
      ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f')).shiftFunctorObjXIso
        (-1) n (n - 1) rfl).hom ≫ c.f (n - 1) from
      HomologicalComplex.XIsoOfEq_hom_naturality c (by omega)]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ ((mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f')).shiftFunctorObjXIso
      (-1) n (n - 1) rfl).hom ≫ z) hc

private lemma signedConeHom_natural {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (u : K ⟶ K') (v : L ⟶ L')
    (comm : f ≫ v = u ≫ f') :
    bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.map f f' u v comm) ≫
        signedConeHom H I f =
      signedConeHom H I f' ≫
        (mappingCone.map (bifunctorHomMapLeft (H := H) (Y := I) f')
          (bifunctorHomMapLeft (H := H) (Y := I) f)
          (bifunctorHomMapLeft (H := H) (Y := I) v)
          (bifunctorHomMapLeft (H := H) (Y := I) u)
          (by rw [← bifunctorHomMapLeft_comp, ← bifunctorHomMapLeft_comp, comm]))⟦(-1 : ℤ)⟧' := by
  ext n
  apply signedCone_to_ext H I f n
  · apply bifunctorHomObj_hom_ext
    intro j q hjq
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, j = p + 1 := ⟨j - 1, by omega⟩
    simp only [HomologicalComplex.comp_f, Category.assoc, signedConeMap_y_assoc,
      bifunctorHomMapLeft_f_π]
    rw [signedConeHom_y_π H I f n p q (by omega), Linear.comp_units_smul,
      bifunctorHomMapLeft_f_π_assoc, signedConeHom_y_π_assoc H I f' n p q (by omega),
      Linear.units_smul_comp]
    congr 1
    simp only [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
    simp [mappingCone.map,
      Cochain.comp_v _ _ (zero_add (-1)) (p + 1) (p + 1) p (add_zero _) (by omega)]
  · apply bifunctorHomObj_hom_ext
    intro p q hpq
    simp only [HomologicalComplex.comp_f, Category.assoc, signedConeMap_x_assoc,
      signedConeHom_x_assoc, bifunctorHomMapLeft_f_π, bifunctorHomMapLeft_f_π_assoc]
    simp only [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
    simp [mappingCone.map]

/-- Signed product Hom takes a source cone to the shifted cone of precomposition,
with its specified coordinates, inverse, differential, restriction and naturality.
There are no boundedness, injectivity or product-exactness hypotheses.

Source: Stacks Project, Tag 08JC, `lemma-RHom-triangulated`, omitted termwise-split
calculation, generalized to the upstream signed bifunctor Hom complex.
(used for `proposition-six-operations-dctf--15`)

Proof plan, the eight steps of the node:
1. On each product projection the differential is s_p(D b_p - A b_(p+1)),
   s_p = (-1)^p. Its square has zero pure terms and cancelling mixed terms, by
   d_I squared = d_V squared = 0 and bifunctoriality (def-sp-abelian).
2. Precomposition by a chain map commutes with this differential, by naturality
   and the chain-map identity; it preserves identities and reverses composition.
3. Restrict along the two cone inclusions. Reconstruct a component from (x,a)
   as H(r_L,I)x + H(r_K,I)a. The biproduct identities and additivity show these
   operations are inverse (def-sp-abelian). These are morphism identities.
4. Use product uniqueness to set y_(p+1) = s_p a_p and retain x_p. The inverse
   sets a_p = s_p y_(p+1). Reindexing integers and s_p squared = 1 give inverse
   graded maps, with no exactness assumption on countable products.
5. The cone followed by shift by -1 has coordinates (y,x) and differential
   (-d_Y y - t x, d_X x), by def-weil-abstract-derived-category.
6. Restrict the source Hom differential to both cone summands. It gives
   x'_p = s_p(D x_p - H(d_L,I)x_(p+1)) and
   a'_p = s_p(D a_p - H(f,I)x_(p+1) + H(d_K,I)a_(p+1)).
7. Substitute a_p = s_p y_(p+1), using s_(p+1) = -s_p. The equations become
   y' = -d_Y y - t x and x' = d_X x. Thus the graded comparison and its inverse
   are chain maps, giving a chain isomorphism with the asserted differential.
8. Restriction along L -> Cone(f) retains x. For a commuting square (u,v),
   the cone map is diag(v,u); precomposition carries (x',a') to
   (H(v,I)x',H(u,I)a'). The same signs give (U(u)y',U(v)x'), proving naturality
   in the displayed contravariant direction. All equalities can be checked
   after projection from morphisms out of an arbitrary test object.
-/
theorem exists_signedBifunctorConeIso :
    ∃ θ : ∀ (K L : CochainComplex A ℤ) (f : K ⟶ L),
      bifunctorHomObj H (mappingCone f) I ≅
        (mappingCone (bifunctorHomMapLeft (H := H) (Y := I) f))⟦(-1 : ℤ)⟧,
      (∀ (K L : CochainComplex A ℤ) (f : K ⟶ L),
        (∀ (n p q : ℤ) (hpq : p + n = q),
          (θ K L f).hom.f n ≫ bifunctorHomConeY H I f n ≫
              bifunctorHomπ H K I (n - 1) (p + 1) q (by omega) =
            p.negOnePow • (bifunctorHomπ H (mappingCone f) I n p q hpq ≫
              (H.map ((mappingCone.inl f).v (p + 1) p (by omega)).op).app (I.X q))) ∧
        (∀ (n p q : ℤ) (hpq : p + n = q),
          (θ K L f).hom.f n ≫ bifunctorHomConeX H I f n ≫
              bifunctorHomπ H L I n p q hpq =
            bifunctorHomπ H (mappingCone f) I n p q hpq ≫
              (H.map ((mappingCone.inr f).f p).op).app (I.X q)) ∧
        (∀ (n p q : ℤ) (hpq : p + n = q),
          (θ K L f).inv.f n ≫ bifunctorHomπ H (mappingCone f) I n p q hpq ≫
              (H.map ((mappingCone.inl f).v (p + 1) p (by omega)).op).app (I.X q) =
            p.negOnePow • (bifunctorHomConeY H I f n ≫
              bifunctorHomπ H K I (n - 1) (p + 1) q (by omega))) ∧
        (∀ (n p q : ℤ) (hpq : p + n = q),
          (θ K L f).inv.f n ≫ bifunctorHomπ H (mappingCone f) I n p q hpq ≫
              (H.map ((mappingCone.inr f).f p).op).app (I.X q) =
            bifunctorHomConeX H I f n ≫ bifunctorHomπ H L I n p q hpq) ∧
        (∀ n : ℤ,
          (bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.inr f)).f n =
            (θ K L f).hom.f n ≫ bifunctorHomConeX H I f n) ∧
        (∀ n : ℤ,
          (bifunctorHomObj H (mappingCone f) I).d n (n + 1) ≫
              (θ K L f).hom.f (n + 1) ≫ bifunctorHomConeY H I f (n + 1) ≫
              ((bifunctorHomObj H K I).XIsoOfEq (by omega : (n + 1) - 1 = n)).hom =
            -((θ K L f).hom.f n ≫ bifunctorHomConeY H I f n ≫
              (bifunctorHomObj H K I).d (n - 1) n) -
            (θ K L f).hom.f n ≫ bifunctorHomConeX H I f n ≫
              (bifunctorHomMapLeft (H := H) (Y := I) f).f n) ∧
        (∀ n : ℤ,
          (bifunctorHomObj H (mappingCone f) I).d n (n + 1) ≫
              (θ K L f).hom.f (n + 1) ≫ bifunctorHomConeX H I f (n + 1) =
            (θ K L f).hom.f n ≫ bifunctorHomConeX H I f n ≫
              (bifunctorHomObj H L I).d n (n + 1))) ∧
      (∀ (K L K' L' : CochainComplex A ℤ) (f : K ⟶ L) (f' : K' ⟶ L')
          (u : K ⟶ K') (v : L ⟶ L') (comm : f ≫ v = u ≫ f'),
        bifunctorHomMapLeft (H := H) (Y := I) (mappingCone.map f f' u v comm) ≫
            (θ K L f).hom =
          (θ K' L' f').hom ≫ (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
            (mappingCone.map (bifunctorHomMapLeft (H := H) (Y := I) f')
              (bifunctorHomMapLeft (H := H) (Y := I) f)
              (bifunctorHomMapLeft (H := H) (Y := I) v)
              (bifunctorHomMapLeft (H := H) (Y := I) u)
              (by rw [← bifunctorHomMapLeft_comp, ← bifunctorHomMapLeft_comp, comm]))) := by
  refine ⟨fun _ _ f ↦ signedConeIso H I f, ?_, ?_⟩
  · intro K L f
    refine ⟨signedConeHom_y_π H I f, ?_, signedConeInv_y H I f,
      signedConeInv_x H I f, fun n ↦ (signedConeHom_x H I f n).symm,
      signedConeHom_d_y H I f, signedConeHom_d_x H I f⟩
    intro n p q hpq
    change (signedConeHom H I f).f n ≫ bifunctorHomConeX H I f n ≫ _ = _
    rw [← Category.assoc, signedConeHom_x, bifunctorHomMapLeft_f_π]
  · intro K L K' L' f f' u v comm
    exact signedConeHom_natural H I f f' u v comm

end CochainComplex
