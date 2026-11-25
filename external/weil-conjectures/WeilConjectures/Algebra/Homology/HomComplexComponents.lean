/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Components of the Hom complex

The product projections `homComplexπ L M n p q : (homComplex L M)^n ⟶ 𝓗om(L^p, M^q)` of the
Hom complex of two complexes of sheaves of modules (`p + n = q`), with the formulas for its
differential (`homComplex_d_π`) and for its functoriality (`homComplexFunctor_map_f_π`).

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-projections).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w r
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

section API

set_option backward.isDefEq.respectTransparency true

/-- The product projections `(homComplex L M)^n ⟶ 𝓗om(L^p, M^q)`, for `p + n = q`, specified
together with `homComplexFunctor` (`homComplex_projections_exists`).
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-projections). -/
noncomputable def homComplexπ
    (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n p q : ℤ)
    (h : p + n = q) :
    (homComplex L M).X n ⟶ SheafOfModules.homObj (L.X p) (M.X q) :=
  Classical.choose (homComplex_projections_exists.{u, v, w, r} (C := C) (J := J) (R := R))
    L M n p q h

/-- The projections `homComplexπ` exhibit `(homComplex L M)^n` as the product of the
`𝓗om(L^p, M^(p+n))`. -/
noncomputable def homComplexIsLimit
    (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n : ℤ) :
    IsLimit (Fan.mk ((homComplex L M).X n) (fun p : ℤ ↦ homComplexπ L M n p (p + n) rfl)) :=
  ((Classical.choose_spec
    (homComplex_projections_exists.{u, v, w, r} (C := C) (J := J) (R := R))).1 L M n).some

lemma homComplex_hom_ext
    {L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} {n : ℤ}
    {A : SheafOfModules.{max u v w} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    {f g : A ⟶ (homComplex L M).X n}
    (h : ∀ p q (hpq : p + n = q), f ≫ homComplexπ L M n p q hpq = g ≫ homComplexπ L M n p q hpq) :
    f = g :=
  (homComplexIsLimit L M n).hom_ext fun ⟨p⟩ ↦ h p (p + n) rfl

/-- The differential of `homComplex L M` is `d_M f - (-1)^n f d_L` on components. -/
lemma homComplex_d_π
    (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q) (hq' : p + n = q')
    (hp' : p' + n = q) :
    (homComplex L M).d n m ≫ homComplexπ L M m p q hpq =
      homComplexπ L M n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (M.d q' q) -
        n.negOnePow • (homComplexπ L M n p' q hp' ≫
          SheafOfModules.homObjMap (L.d p p') (𝟙 (M.X q))) :=
  (Classical.choose_spec (homComplex_projections_exists.{u, v, w, r} (C := C) (J := J)
    (R := R))).2.1 L M n m p q q' p' hnm hpq hq' hp'

/-- The action of `homComplexFunctor` on morphisms is componentwise pre- and post-composition. -/
lemma homComplexFunctor_map_f_π
    {L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} (f : L' ⟶ L)
    (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q) :
    (((homComplexFunctor.map f.op).app M) ≫ (homComplexFunctor.obj (op L')).map g).f n ≫
        homComplexπ L' M' n p q hpq =
      homComplexπ L M n p q hpq ≫ SheafOfModules.homObjMap (f.f p) (g.f q) :=
  (Classical.choose_spec (homComplex_projections_exists.{u, v, w, r} (C := C) (J := J)
    (R := R))).2.2 L L' M M' f g n p q hpq

/-- The action of `homComplexFunctor` in the second variable is componentwise
post-composition. -/
lemma homComplexFunctor_obj_map_f_π
    {L M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q) :
    ((homComplexFunctor.obj (op L)).map g).f n ≫ homComplexπ L M' n p q hpq =
      homComplexπ L M n p q hpq ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (g.f q) := by
  have h := homComplexFunctor_map_f_π (𝟙 L) g n p q hpq
  rwa [op_id, homComplexFunctor.map_id, NatTrans.id_app, Category.id_comp,
    HomologicalComplex.id_f] at h

end API

end CategoryTheory
