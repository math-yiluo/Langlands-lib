/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomTensorPair
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Forward degreewise currying construction

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-degreewise-construction)
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

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
/-- Forward degreewise construction, without uniqueness or invertibility.
Source: Stacks Project, Tag 0A90, degreewise construction 
(blueprint: lem-sc-hom-tensor-degreewise-construction).

Proof: Expand the product projections in both Hom complexes. For each p and q,
evaluate the outer localized map on x and the inner map on y. These evaluations
are linear in x, y and the input section, and commute with restrictions. Descend
the balanced bilinear map through the presheaf tensor and its sheafification.
For fixed total degree, combine these maps by the coproduct universal property;
then combine the resulting maps into M by the Hom product universal property.
This constructs a sheaf morphism and gives the displayed pure-tensor equation.
No uniqueness or inverse assertion is used in this construction. -/
theorem homTensorDegreewise_construct (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ a : (homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n,
      HomTensorDegreewiseEquation R K L M n a := by
  classical
  let := SheafOfModules.monoidalCategory R
  let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
  let S := (homComplex (R := R) K (homComplex (R := R) L M)).X n
  have hpair (t p q : ℤ) (hpq : p + q = t) :
      ∃ b : S ⟶ SheafOfModules.homObj (R := R) (K.X p ⊗ L.X q) (M.X (t + n)),
        ∀ (U : Cᵒᵖ) (s : S.val.obj U) (W : (Over U.unop)ᵒᵖ)
          (x : (K.X p).val.obj (op W.unop.left))
          (y : (L.X q).val.obj (op W.unop.left)),
          (((b.val.app U).hom s).app W).hom
            (((homTensorCurrySectionMap R (K.X p) (L.X q)).app
              (op W.unop.left)).hom (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) =
          ((((homTensorCurryProjection R L M (p + n) q (t + n) (by omega)).val.app
            (op W.unop.left)).hom
              ((((homTensorCurryProjection R K (homComplex (R := R) L M)
                n p (p + n) rfl).val.app U).hom s).app W |>.hom x)).app
                  (op (Over.mk (𝟙 W.unop.left)))).hom y := by
    exact SheafOfModules.homTensorPair_construct R S (K.X p)
      ((homComplex (R := R) L M).X (p + n)) (L.X q) (M.X (t + n))
      (homTensorCurryProjection R K (homComplex (R := R) L M) n p (p + n) rfl)
      (homTensorCurryProjection R L M (p + n) q (t + n) (by omega))
  let b := fun t p q hpq ↦ Classical.choose (hpair t p q hpq)
  have hb := fun t p q hpq ↦ Classical.choose_spec (hpair t p q hpq)
  have hcomponent (t : ℤ) :
      ∃ c : S ⟶ SheafOfModules.homObj (R := R) (T.X t) (M.X (t + n)),
        ∀ (p q : ℤ) (hpq : p + q = t),
          c ≫ SheafOfModules.homObjMap (R := R)
            (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t hpq)
            (𝟙 (M.X (t + n))) = b t p q hpq := by
    let I := {x : ℤ × ℤ // x.1 + x.2 = t}
    let A : I → Mod := fun x ↦ K.X x.1.1 ⊗ L.X x.1.2
    let c : Limits.Cofan A := Limits.Cofan.mk (T.X t) (fun x ↦
      CochainComplex.ιMapBifunctor K L (curriedTensor Mod) x.1.1 x.1.2 t x.2)
    have hc : Limits.IsColimit c := by
      refine Limits.Cofan.IsColimit.mk c
        (fun s ↦ HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
          (fun p q hpq ↦ s.inj ⟨(p, q), hpq⟩)) ?_ ?_
      · intro s x
        exact HomologicalComplex.ι_mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
          (fun p q hpq ↦ s.inj ⟨(p, q), hpq⟩) x.1.1 x.1.2 x.2
      · intro s m hm
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        exact (hm ⟨(p, q), hpq⟩).trans
          (HomologicalComplex.ι_mapBifunctorDesc
            (K₁ := K) (K₂ := L) (F := curriedTensor Mod)
            (fun p q hpq ↦ s.inj ⟨(p, q), hpq⟩) p q hpq).symm
    obtain ⟨hcHom⟩ := SheafOfModules.internalHomCoproductFanIsLimit R A c hc (M.X (t + n))
    refine ⟨Limits.Fan.IsLimit.lift hcHom (fun x ↦ b t x.1.1 x.1.2 x.2), ?_⟩
    intro p q hpq
    exact Limits.Fan.IsLimit.fac hcHom (fun x ↦ b t x.1.1 x.1.2 x.2) ⟨(p, q), hpq⟩
  let c := fun t ↦ Classical.choose (hcomponent t)
  have hc := fun t ↦ Classical.choose_spec (hcomponent t)
  have hprod : Nonempty (Limits.IsLimit (Limits.Fan.mk
      ((homComplex (R := R) T M).X n)
      (fun t : ℤ ↦ homTensorCurryProjection R T M n t (t + n) rfl))) := by
    exact (Classical.choose_spec (homComplex_projections_exists (R := R))).1 T M n
  obtain ⟨hprod⟩ := hprod
  let a := Limits.Fan.IsLimit.lift hprod c
  have ha (t : ℤ) : a ≫ homTensorCurryProjection R T M n t (t + n) rfl = c t :=
    Limits.Fan.IsLimit.fac hprod c t
  refine ⟨a, ?_⟩
  intro p q U s W x y
  have he := congrArg
    (fun z : S ⟶ SheafOfModules.homObj (R := R)
        (K.X p ⊗ L.X q) (M.X (p + q + n)) ↦
      (((z.val.app U).hom s).app W).hom
        (((homTensorCurrySectionMap R (K.X p) (L.X q)).app
          (op W.unop.left)).hom (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)))
    ((congrArg (fun z ↦ z ≫ SheafOfModules.homObjMap (R := R)
      (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q (p + q) rfl)
      (𝟙 (M.X (p + q + n)))) (ha (p + q))).trans (hc (p + q) p q rfl))
  exact he.trans (hb (p + q) p q rfl U s W x y)

end CategoryTheory
