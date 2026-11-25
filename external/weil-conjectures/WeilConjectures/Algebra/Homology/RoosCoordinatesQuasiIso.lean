/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Quasi-isomorphisms of complexes in Roos coordinates

Source: Stacks Project, Derived Categories, Tag 08TC, exact-product cone model.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private def coordinatesInclusion
    {A : Type u} [Category.{v} A] [Abelian A]
    (V L : CochainComplex A ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))) : V⟦(-1 : ℤ)⟧ ⟶ L :=
  ofHom (fun i ↦ (biprod.inr : V.X (i - 1) ⟶ V.X i ⊞ V.X (i - 1)) ≫ (e i).inv) (by
    intro i
    apply (cancel_mono (e (i + 1)).hom).1
    rw [Category.assoc, hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
      shiftFunctor_obj_d', Int.negOnePow_neg, Int.negOnePow_one,
      Units.neg_smul, one_smul]
    change (biprod.inr : V.X (i - 1) ⟶ _) ≫ _ =
      (-V.d (i - 1) ((i + 1) - 1)) ≫ biprod.inr
    apply biprod.hom_ext
    · simp [Category.assoc, Preadditive.neg_comp]
    · simp [Category.assoc, Preadditive.neg_comp])

private def coordinatesProjection
    {A : Type u} [Category.{v} A] [Abelian A]
    (V L : CochainComplex A ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))) : L ⟶ V :=
  ofHom (fun i ↦ (e i).hom ≫ biprod.fst) (by
    intro i
    rw [← Category.assoc, hd]
    simp [Category.assoc])

private def coordinatesSequence
    {A : Type u} [Category.{v} A] [Abelian A]
    (V L : CochainComplex A ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (coordinatesInclusion V L s e hd) (coordinatesProjection V L s e hd)
    (by
      ext i
      simp +instances only [coordinatesInclusion, coordinatesProjection,
        HomologicalComplex.comp_f, ofHom, HomologicalComplex.zero_f]
      simp [Category.assoc])

private theorem coordinatesSequence_shortExact
    {A : Type u} [Category.{v} A] [Abelian A]
    (V L : CochainComplex A ℤ) (s : V ⟶ V)
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))) :
    (coordinatesSequence V L s e hd).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  apply ShortComplex.Splitting.shortExact
  refine
    { r := (e i).hom ≫ biprod.snd
      s := biprod.inl ≫ (e i).inv
      f_r := ?_
      s_g := ?_
      id := ?_ }
  · change ((biprod.inr : V.X (i - 1) ⟶ V.X i ⊞ V.X (i - 1)) ≫
        (e i).inv) ≫ ((e i).hom ≫ biprod.snd) = 𝟙 _
    simp [Category.assoc]
  · change (biprod.inl ≫ (e i).inv) ≫ ((e i).hom ≫ biprod.fst) = 𝟙 _
    simp [Category.assoc]
  · change ((e i).hom ≫ biprod.snd) ≫ (biprod.inr ≫ (e i).inv) +
        ((e i).hom ≫ biprod.fst) ≫ (biprod.inl ≫ (e i).inv) = 𝟙 _
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      add_comm, biprod.total]
    simp

/-- A diagonal map of Roos coordinate complexes is a quasi-isomorphism whenever its
map on the unshifted complexes is a quasi-isomorphism.

Source: Stacks Project, Derived Categories, Tag 08TC, product-cone model, and the
mapping-cone comparison for a commuting square
(auxiliary; not a blueprint node).

Proof: Filter each displayed complex by its second coordinate. The subcomplex is the
shift by minus one of V, with differential minus d, and the quotient is V. The
coordinate inclusion and projection form a degreewise split short exact sequence.
The diagonal map gives a morphism of these sequences whose outer maps are a shifted
copy of a and a itself. Both are quasi-isomorphisms. The long exact homology sequences
and the five lemma make the middle map a quasi-isomorphism. The argument applies to
zero complexes and arbitrary endomorphisms s; it needs neither products nor a site. -/
theorem quasiIso_of_roos_coordinates
    {A : Type u} [Category.{v} A] [Abelian A]
    (V V' L L' : CochainComplex A ℤ) (s : V ⟶ V) (s' : V' ⟶ V')
    (e : ∀ i : ℤ, L.X i ≅ V.X i ⊞ V.X (i - 1))
    (e' : ∀ i : ℤ, L'.X i ≅ V'.X i ⊞ V'.X (i - 1))
    (hd : ∀ i : ℤ, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ biprod.lift (biprod.fst ≫ V.d i (i + 1))
        (biprod.fst ≫ s.f i ≫
          eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V.d (i - 1) ((i + 1) - 1)))
    (hd' : ∀ i : ℤ, L'.d i (i + 1) ≫ (e' (i + 1)).hom =
      (e' i).hom ≫ biprod.lift (biprod.fst ≫ V'.d i (i + 1))
        (biprod.fst ≫ s'.f i ≫
          eqToHom (congrArg V'.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V'.d (i - 1) ((i + 1) - 1)))
    (a : V ⟶ V') (f : L ⟶ L')
    (hf : ∀ i : ℤ, f.f i ≫ (e' i).hom =
      (e i).hom ≫ biprod.map (a.f i) (a.f (i - 1)))
    (ha : QuasiIso a) : QuasiIso f := by
  let S := coordinatesSequence V L s e hd
  let S' := coordinatesSequence V' L' s' e' hd'
  let φ : S ⟶ S' :=
    { τ₁ := a⟦(-1 : ℤ)⟧'
      τ₂ := f
      τ₃ := a
      comm₁₂ := by
        ext i : 1
        apply (cancel_mono (e' i).hom).1
        change ((a⟦(-1 : ℤ)⟧').f i ≫
            (biprod.inr ≫ (e' i).inv)) ≫ (e' i).hom =
          ((biprod.inr ≫ (e i).inv) ≫ f.f i) ≫ (e' i).hom
        simp only [Category.assoc]
        rw [hf]
        change a.f (i - 1) ≫
            ((biprod.inr : V'.X (i - 1) ⟶ V'.X i ⊞ V'.X (i - 1)) ≫
              (e' i).inv ≫ (e' i).hom) = _
        simp [biprod.inr_map]
      comm₂₃ := by
        ext i : 1
        change f.f i ≫ ((e' i).hom ≫ biprod.fst) =
          ((e i).hom ≫ biprod.fst) ≫ a.f i
        rw [← Category.assoc, hf]
        simp [Category.assoc] }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ φ
    (coordinatesSequence_shortExact V L s e hd)
    (coordinatesSequence_shortExact V' L' s' e' hd')
    ((quasiIso_shift_iff a (-1)).2 ha) ha

end CochainComplex
