/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit

/-!
# Section projections respect the external Hom differential

Source: Stacks Project, Tag 0A8X, differential of the Hom complex.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v r
open CategoryTheory Opposite
namespace CategoryTheory

private lemma section_sub_units
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R₀ : Sheaf J RingCat.{max u v r}} (U : C)
    {M N : SheafOfModules.{max u v r} R₀} (f g : M ⟶ N)
    (n : ℤˣ) (x : M.val.obj (op U)) :
    ((f - n • g).val.app (op U)) x =
      (f.val.app (op U)) x - n • (g.val.app (op U)) x := by
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U)
  change (V.map (f - n • g)).hom x = _
  rw [Functor.map_sub]
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private lemma sheaf_units_smul_val
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {R₀ : Sheaf K RingCat.{max u v r}}
    {M N : SheafOfModules.{max u v r} R₀} (n : ℤˣ) (f : M ⟶ N) :
    (n • f).val = n • f.val := by
  change (SheafOfModules.forget R₀).map (n • f) = _
  simp only [Units.smul_def, Functor.map_zsmul]
  rfl

private lemma sheaf_add_units_app
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    {R₀ : Sheaf K RingCat.{max u v r}}
    {M N : SheafOfModules.{max u v r} R₀} (f g : M ⟶ N) (n : ℤˣ) (W : Dᵒᵖ) :
    (f + n • g).val.app W = f.val.app W + n • g.val.app W := by
  rw [SheafOfModules.add_val, sheaf_units_smul_val.{u, v, r}, PresheafOfModules.add_app]
  simp only [Units.smul_def, PresheafOfModules.zsmul_app]

private lemma section_sub_units_component
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    {A B M : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)}
    (f g : M ⟶ SheafOfModules.homObj (R := R) A B) (n : ℤˣ)
    (x : M.val.obj (op U)) (W : (Over U)ᵒᵖ) :
    (((f - n • g).val.app (op U)) x).app W =
      ((f.val.app (op U)) x).app W - n • ((g.val.app (op U)) x).app W := by
  rw [section_sub_units.{u, v, r}]
  change (((f.val.app (op U)) x - (n : ℤ) • (g.val.app (op U)) x) :
    (PresheafOfModules.restrictOver R.obj U).obj A.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj B.val).app W = _
  rw [PresheafOfModules.sub_app, PresheafOfModules.zsmul_app]
  rfl

/-- Any degreewise identification given by the section projections respects differentials.
Source: Stacks Project, Tag 0A8X, differential of the Hom complex; Tag 0A8Y.
(auxiliary; not a blueprint node)

Proof: compare the two external cochains on each component p,q with p+j=q.
For j=i+1, apply the differential projection identity of homComplex_exists at
q'=p+i and p'=p+1, then evaluate at U and at each localized object W.
Evaluation preserves subtraction and integer scalar multiplication. Internal Hom
postcomposition and precomposition evaluate to composition with the restricted
differentials. Substitute the given component formulas for e in degree i and j.
Mathlib's external differential is the first composite plus j.negOnePow times
the second composite; j=i+1 gives j.negOnePow=-i.negOnePow, exactly the internal
Hom differential. Extensionality of module-sheaf morphisms and cochains proves
the equality. No bijectivity or cycle condition is used, so this step is separate
from the product universal property and the homology quotient argument. At zero
complexes both sides vanish; at i=0 the formula is d_I f - f d_L; at i=-1 it is
 d_I f + f d_L. Products allow arbitrary unbounded families. -/
theorem homComplex_sections_cochains_commOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    (L I : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let S := E.obj (homComplex (R := R) L I)
    let π := Classical.choose
      (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))
    ∀ (e : ∀ n : ℤ, S.X n ≃+
        CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n),
      (∀ (n : ℤ) (x : S.X n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((e n x).v p q hpq).val.app W =
          (((π L I n p q hpq).val.app (op U)) x).app W) →
      ∀ (i j : ℤ), i + 1 = j → ∀ x : S.X i,
        e j (S.d i j x) = CochainComplex.HomComplex.δ i j (e i x) := by
  classical
  intro R₀ E res S π e he i j hij x
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  apply SheafOfModules.hom_ext
  ext W y
  rw [he]
  have hd := (Classical.choose_spec
    (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))).2.1
    L I i j p q (p + i) (p + 1) hij hpq rfl (by omega)
  change (homComplex (R := R) L I).d i j ≫ π L I j p q hpq = _ at hd
  have hx := congrArg (fun f ↦ ((f.val.app (op U)) x).app W) hd
  conv_rhs at hx =>
    rw [section_sub_units_component.{u, v, r}]
  conv_rhs =>
    rw [CochainComplex.HomComplex.δ_v i j hij (e i x) p q hpq
      (p + i) (p + 1) (by omega) rfl]
  simp only [sheaf_add_units_app.{max u v, v, r}, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, he]
  have hs : j.negOnePow = -i.negOnePow := by rw [← hij, Int.negOnePow_succ]
  simp only [hs, Units.neg_smul, ← sub_eq_add_neg]
  exact congrArg (fun f ↦ f.hom y) hx

end CategoryTheory
