/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex

/-! # HomComplexProjections

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

set_option backward.isDefEq.respectTransparency true in
/-- The chosen Hom-complex functor admits the specified product projections.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-projections).
Proof: apply `Classical.choose_spec` to `homComplex_exists`; its chosen first
component is precisely `homComplexFunctor`. This exposes the projection
specification without repeatedly reducing the large bifunctor existence type. -/
theorem homComplex_projections_exists :
    let F := homComplexFunctor.{u, v, w, r} (C := C) (J := J) (R := R);
    ∃ π : ∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n p q : ℤ), p + n = q →
        (((F.obj (op L)).obj M).X n ⟶ SheafOfModules.homObj (L.X p) (M.X q)),
        (∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
            (fun p : ℤ ↦ π L M n p (p + n) rfl)))) ∧
        (∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m p q q' p' : ℤ)
          (_hnm : n + 1 = m) (hpq : p + m = q)
          (hq' : p + n = q') (hp' : p' + n = q),
          ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
            π L M n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (M.d q' q) -
              n.negOnePow • (π L M n p' q hp' ≫
                SheafOfModules.homObjMap (L.d p p') (𝟙 (M.X q)))) ∧
        (∀ (L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (f : L' ⟶ L) (g : M ⟶ M')
          (n p q : ℤ) (hpq : p + n = q),
          (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
            π L M n p q hpq ≫ SheafOfModules.homObjMap (f.f p) (g.f q)) := by
  exact Classical.choose_spec (homComplex_exists (C := C) (J := J) (R := R))

end CategoryTheory
