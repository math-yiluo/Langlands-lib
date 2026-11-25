/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomTensorReversePair
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomProduct

/-!
# Reverse degreewise currying construction

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-reverse-construction)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

private theorem hom_product_spec (A B : CochainComplex Mod ℤ) (d : ℤ) :
    Nonempty (Limits.IsLimit (Limits.Fan.mk ((homComplex (R := R) A B).X d)
      (fun i : ℤ ↦ homTensorCurryProjection R A B d i (i + d) rfl))) :=
  (Classical.choose_spec (homComplex_projections_exists (R := R))).1 A B d

-- Do not unfold the chosen bifunctor while checking localized section formulas.
attribute [local irreducible] homComplex homComplexFunctor homTensorCurryProjection

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
/-- Reverse currying construction with its evaluation equation, without inverse laws.
Source: Stacks Project, Cohomology on Sites, Tag 0A90, inverse construction;
Modules on Sites, Tag 03EO and Section 03EK.
(blueprint: lem-sc-hom-tensor-reverse-construction).

Proof: Restrict a localized map out of the total tensor term to each (p,q)
summand. Pull it back along the presheaf-to-sheaf tensor map. Curry the resulting
bilinear map, first in y and then in x, on the localized site. These maps commute
with further restriction because restriction of a bilinear map commutes with
currying. Assemble the q components using the product cone of the inner Hom
complex, then assemble the p components using the outer Hom product cone.
Linearity in the initial localized map and restriction compatibility give a
morphism of sheaves b. Evaluating the assembled components at x and y recovers
the original bilinear map by the tensor-Hom evaluation identity. This proves
the displayed equation. There are no inverse identities in this construction,
no boundedness assumptions, and no assumption of global pure-tensor generation. -/
theorem homTensorDegreewise_reverse_construct (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ b : (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n ⟶
      (homComplex (R := R) K (homComplex (R := R) L M)).X n,
      ∀ (p q : ℤ) (U : Cᵒᵖ)
    (s : (homComplex (R := R)
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
    (y : (L.X q).val.obj (op W.unop.left)),
    let φ := ((homTensorCurryProjection R
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
      n (p + q) (p + q + n) rfl).val.app U).hom s
    let ψ := ((homTensorCurryProjection R K (homComplex (R := R) L M)
      n p (p + n) rfl).val.app U).hom ((b.val.app U).hom s)
    let χ := ((homTensorCurryProjection R L M (p + n) q (p + q + n)
      (by omega)).val.app (op W.unop.left)).hom ((ψ.app W).hom x)
    (φ.app W).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        p q (p + q) rfl).val.app (op W.unop.left)).hom
        (((homTensorCurrySectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y
 := by
  classical
  let := SheafOfModules.monoidalCategory R
  let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
  let S := (homComplex (R := R) T M).X n
  have hprod := hom_product_spec R
  have hpair (p q : ℤ) :
      ∃ b : S ⟶ SheafOfModules.homObj (R := R) (K.X p)
          (SheafOfModules.homObj (R := R) (L.X q) (M.X (q + (p + n)))),
        ∀ (U : Cᵒᵖ) (s : S.val.obj U) (W : (Over U.unop)ᵒᵖ)
          (x : (K.X p).val.obj (op W.unop.left))
          (y : (L.X q).val.obj (op W.unop.left)),
          ((((homTensorCurryProjection R T M n (p + q) (q + (p + n))
            (by omega)).val.app U).hom s).app W).hom
            (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
              p q (p + q) rfl).val.app (op W.unop.left)).hom
              (((homTensorCurrySectionMap R (K.X p) (L.X q)).app
                (op W.unop.left)).hom (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
          (((((b.val.app U).hom s).app W).hom x).app
            (op (Over.mk (𝟙 W.unop.left)))).hom y := by
    obtain ⟨b, hb⟩ := SheafOfModules.homTensorReversePair_construct R S (K.X p) (L.X q)
      (M.X (q + (p + n)))
      (homTensorCurryProjection R T M n (p + q) (q + (p + n)) (by omega) ≫
        SheafOfModules.homObjMap (R := R)
          (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q (p + q) rfl)
          (𝟙 _))
    refine ⟨b, ?_⟩
    intro U s W x y
    exact hb U s W x y
  choose c hc using hpair
  let innerFan (p : ℤ) := Limits.Fan.mk ((homComplex (R := R) L M).X (p + n))
    (fun q : ℤ ↦ homTensorCurryProjection R L M (p + n) q (q + (p + n)) rfl)
  have innerLimit (p : ℤ) : Limits.IsLimit (Limits.Fan.mk
      (SheafOfModules.homObj (R := R) (K.X p) ((homComplex (R := R) L M).X (p + n)))
      (fun q : ℤ ↦ SheafOfModules.homObjMap (R := R) (𝟙 (K.X p))
        (homTensorCurryProjection R L M (p + n) q (q + (p + n)) rfl))) :=
    (SheafOfModules.internalHomProductFanIsLimit R (K.X p)
    (fun q ↦ SheafOfModules.homObj (R := R) (L.X q) (M.X (q + (p + n))))
    (innerFan p) (hprod L M (p + n)).some).some
  let a (p : ℤ) : S ⟶ SheafOfModules.homObj (R := R) (K.X p)
      ((homComplex (R := R) L M).X (p + n)) :=
    Limits.Fan.IsLimit.lift (innerLimit p) (c p)
  have ha (p q : ℤ) :
      a p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (K.X p))
        (homTensorCurryProjection R L M (p + n) q (q + (p + n)) rfl) = c p q :=
    Limits.Fan.IsLimit.fac (innerLimit p) (c p) q
  have outerLimit := (hprod K (homComplex (R := R) L M) n).some
  let b : S ⟶ (homComplex (R := R) K (homComplex (R := R) L M)).X n :=
    Limits.Fan.IsLimit.lift outerLimit a
  have hb (p : ℤ) :
      b ≫ homTensorCurryProjection R K (homComplex (R := R) L M)
        n p (p + n) rfl = a p :=
    Limits.Fan.IsLimit.fac outerLimit a p
  refine ⟨b, ?_⟩
  intro p q U s W x y
  have h := (congrArg (fun z ↦ z ≫ SheafOfModules.homObjMap (R := R) (𝟙 (K.X p))
    (homTensorCurryProjection R L M (p + n) q (q + (p + n)) rfl)) (hb p)).trans
      (ha p q)
  have he := congrArg
    (fun z : S ⟶ SheafOfModules.homObj (R := R) (K.X p)
        (SheafOfModules.homObj (R := R) (L.X q) (M.X (q + (p + n)))) ↦
      (((((z.val.app U).hom s).app W).hom x).app
        (op (Over.mk (𝟙 W.unop.left)))).hom y) h
  have hfinal (r : ℤ) (hr : q + (p + n) = r) :
      let φ := ((homTensorCurryProjection R T M n (p + q) r
        (by omega)).val.app U).hom s
      let ψ := ((homTensorCurryProjection R K (homComplex (R := R) L M)
        n p (p + n) rfl).val.app U).hom ((b.val.app U).hom s)
      let χ := ((homTensorCurryProjection R L M (p + n) q r hr).val.app
        (op W.unop.left)).hom ((ψ.app W).hom x)
      (φ.app W).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          p q (p + q) rfl).val.app (op W.unop.left)).hom
          (((homTensorCurrySectionMap R (K.X p) (L.X q)).app
            (op W.unop.left)).hom (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
        (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y := by
    subst r
    set_option backward.isDefEq.respectTransparency false in
      exact (hc p q U s W x y).trans he.symm
  exact hfinal (p + q + n) (by omega)

end CategoryTheory
