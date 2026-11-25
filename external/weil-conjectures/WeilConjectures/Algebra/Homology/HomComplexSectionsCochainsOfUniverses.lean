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
# Degreewise sections of the sheaf Hom complex

Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v r
open CategoryTheory Opposite
namespace CategoryTheory

private theorem fan_projection_bijective.{t} {ι : Type} {X : ι → Type t}
    {P : Type t} (π : ∀ i, P ⟶ X i) (h : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (fun x i ↦ π i x) := by
  let e := h.conePointUniqueUpToIso (Limits.Types.productLimitCone X).isLimit
  have he (x : P) (i : ι) : e.hom x i = π i x :=
    ConcreteCategory.congr_hom (h.conePointUniqueUpToIso_hom_comp
      (Limits.Types.productLimitCone X).isLimit ⟨i⟩) x
  have hf : (fun x i ↦ π i x) = e.toEquiv := by
    funext x i
    exact (he x i).symm
  rw [hf]
  exact e.toEquiv.bijective

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionToLocalizedHom
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))
    (φ : (SheafOfModules.homObj (R := R) A B).val.obj (op U)) :
    (SheafOfModules.overFunctor _ U).obj A ⟶
      (SheafOfModules.overFunctor _ U).obj B := ⟨φ⟩

private theorem sectionToLocalizedHom_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) :
    sectionToLocalizedHom.{u, v, r} R U A B 0 = 0 := rfl

private theorem sectionToLocalizedHom_add
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))
    (φ ψ : (SheafOfModules.homObj (R := R) A B).val.obj (op U)) :
    sectionToLocalizedHom.{u, v, r} R U A B (φ + ψ) =
      sectionToLocalizedHom.{u, v, r} R U A B φ + sectionToLocalizedHom.{u, v, r} R U A B ψ := rfl

private noncomputable def sectionToLocalizedHomEquiv
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    (A B : SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) :
    (SheafOfModules.homObj (R := R) A B).val.obj (op U) ≃
      ((SheafOfModules.overFunctor _ U).obj A ⟶
        (SheafOfModules.overFunctor _ U).obj B) where
  toFun := sectionToLocalizedHom.{u, v, r} R U A B
  invFun φ := φ.val
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency true in
/-- Product projections identify degreewise sections with all localized cochains.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(auxiliary; not a blueprint node)

Proof: the product cone specified by homComplex_exists remains a product after
forgetting module sheaves, evaluating at U, and forgetting to abelian groups.
Its factors are localized presheaf-module morphisms by the construction of
internal Hom. The fully faithful forgetful functor from localized module sheaves
to presheaf modules identifies each factor with localized sheaf-module morphisms.
A degree-n external cochain is exactly a family of these morphisms indexed by p,
with target degree p+n. The product universal property supplies the forward map
and inverse; the projection formulas prove both inverse laws. Each projection and
the inverse preserve addition, so this is an additive equivalence. Reindexing q
along p+n=q gives the displayed formula. No finite support or boundedness is
required. If either complex is zero every factor and the product are zero, and
for n=0 the same construction gives arbitrary degree-preserving families. -/
theorem homComplex_sections_cochainsOfUniverses
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
    ∃ e : ∀ n : ℤ, S.X n ≃+
        CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n,
      ∀ (n : ℤ) (x : S.X n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((e n x).v p q hpq).val.app W =
          (((π L I n p q hpq).val.app (op U)) x).app W := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
  let := module_overFunctor_preservesZero R₀ U
  let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let E := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat
  let S : CochainComplex AddCommGrpCat.{max u v r} ℤ :=
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj (homComplex (R := R) L I)
  let π := Classical.choose
      (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))
  let f (n : ℤ) : S.X n →+ CochainComplex.HomComplex.Cochain (res.obj L) (res.obj I) n :=
    { toFun := fun x ↦ CochainComplex.HomComplex.Cochain.mk
        (fun p q hpq ↦ sectionToLocalizedHom.{u, v, r} R U (L.X p) (I.X q)
          (((π L I n p q hpq).val.app (op U)) x))
      map_zero' := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        change sectionToLocalizedHom.{u, v, r} R U (L.X p) (I.X q)
          (((π L I n p q hpq).val.app (op U)).hom 0) = 0
        rw [map_zero, sectionToLocalizedHom_zero.{u, v, r}]
      map_add' := by
        intro x y
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        change sectionToLocalizedHom.{u, v, r} R U (L.X p) (I.X q)
          (((π L I n p q hpq).val.app (op U)).hom (x + y)) =
            sectionToLocalizedHom.{u, v, r} R U (L.X p) (I.X q)
              (((π L I n p q hpq).val.app (op U)).hom x) +
            sectionToLocalizedHom.{u, v, r} R U (L.X p) (I.X q)
              (((π L I n p q hpq).val.app (op U)).hom y)
        exact (congrArg (sectionToLocalizedHom.{u, v, r} R U (L.X p) (I.X q))
          (((π L I n p q hpq).val.app (op U)).hom.map_add x y)).trans
            (sectionToLocalizedHom_add.{u, v, r} R U (L.X p) (I.X q) _ _) }
  have hf (n : ℤ) : Function.Bijective (f n) := by
    let H := fun p : ℤ ↦ SheafOfModules.homObj (L.X p) (I.X (p + n))
    have hlim := (Classical.choose_spec
      (homComplex_projections_exists.{u, v, max u v r, max u v r}
        (J := J) (R := R))).1 L I n
    let h := Limits.isLimitFanMkObjOfIsLimit (E ⋙ forget AddCommGrpCat) H
      (fun p ↦ π L I n p (p + n) rfl) hlim.some
    have hb := fan_projection_bijective.{max u v r} _ h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hb.1
      funext p
      apply (sectionToLocalizedHomEquiv.{u, v, r} R U (L.X p) (I.X (p + n))).injective
      exact CochainComplex.HomComplex.Cochain.congr_v hxy p (p + n) rfl
    · intro c
      obtain ⟨x, hx⟩ := hb.2 (fun p ↦
        (sectionToLocalizedHomEquiv.{u, v, r} R U (L.X p) (I.X (p + n))).symm
          (c.v p (p + n) rfl))
      refine ⟨x, ?_⟩
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      subst q
      exact (congrArg (sectionToLocalizedHomEquiv.{u, v, r} R U (L.X p) (I.X (p + n)))
        (congrFun hx p)).trans
          ((sectionToLocalizedHomEquiv.{u, v, r} R U (L.X p) (I.X (p + n))).apply_symm_apply _)
  refine ⟨fun n ↦ AddEquiv.ofBijective (f n) (hf n), ?_⟩
  intro n x p q hpq W
  rfl

end CategoryTheory
