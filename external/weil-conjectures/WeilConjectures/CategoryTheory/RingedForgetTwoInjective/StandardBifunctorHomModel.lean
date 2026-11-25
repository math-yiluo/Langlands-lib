/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveModels

/-! # Standard-sign projections on the native Hom complex

Source: Stacks, Sites Cohomology, section-hom-complexes; BifunctorHomComplex.lean.
(blueprint: def-sf-standard-bifunctor-hom-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe b vb
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedForgetTwoInjective

variable {B : Type b} [Category.{vb} B] [Preadditive B] [HasCountableProducts B]
  (H : Bᵒᵖ ⥤ B ⥤ B) [H.Additive] [∀ P, (H.obj P).Additive]

/-- The native complex-Hom, made simultaneous in both variables.
Source: BifunctorHomComplex.lean (blueprint: def-sf-standard-bifunctor-hom-model). -/
def nativeHomComplex :
    (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ where
  obj P := CochainComplex.bifunctorHomObj H P.1.unop P.2
  map {P Q} f := CochainComplex.bifunctorHomMapLeft (H := H) (Y := P.2) f.1.unop ≫
    CochainComplex.bifunctorHomMapRight (H := H) (K := Q.1.unop) f.2
  map_id P := by
    change CochainComplex.bifunctorHomMapLeft (H := H) (Y := P.2) (𝟙 P.1.unop) ≫
      CochainComplex.bifunctorHomMapRight (H := H) (K := P.1.unop) (𝟙 P.2) = 𝟙 _
    rw [CochainComplex.bifunctorHomMapLeft_id, CochainComplex.bifunctorHomMapRight_id]
    exact Category.id_comp _
  map_comp f g := by
    dsimp only [prod_comp_fst, prod_comp_snd, unop_comp]
    rw [CochainComplex.bifunctorHomMapLeft_comp, CochainComplex.bifunctorHomMapRight_comp]
    apply HomologicalComplex.Hom.ext
    funext n
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    simp only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.bifunctorHomMapRight_f_π,
      CochainComplex.bifunctorHomMapRight_f_π_assoc,
      CochainComplex.bifunctorHomMapLeft_f_π_assoc]
    rw [← NatTrans.naturality_assoc]

/-- Rescaling the projections, rather than choosing another product, converts the native
row-sign differential to the standard differential. Thus the native-to-standard map is the
identity on the underlying complex and has exactly the required signed product components.
Source: Stacks, section-hom-complexes, and BifunctorHomComplex.lean
(blueprint: def-sf-standard-bifunctor-hom-model). -/
def standardHomModel : StandardModel H where
  complex := nativeHomComplex H
  π K I n p q hpq :=
    (n * p).negOnePow • CochainComplex.bifunctorHomπ H K I n p q hpq
  product K I n := by
    refine Fan.IsLimit.mk _
      (fun s ↦ CochainComplex.bifunctorHomLift H K I n (fun p q hpq ↦ by
        subst q
        exact (n * p).negOnePow • s.proj p)) ?_ ?_
    · intro s p
      change _ ≫ ((n * p).negOnePow • _) = _
      rw [Linear.comp_units_smul, CochainComplex.bifunctorHomLift_π,
        smul_smul, Int.units_mul_self, one_smul]
    · intro s f hf
      apply CochainComplex.bifunctorHomObj_hom_ext
      intro p q hpq
      subst q
      rw [CochainComplex.bifunctorHomLift_π]
      have h := congrArg (fun a ↦ (n * p).negOnePow • a) (hf p)
      simpa only [Fan.proj, Fan.mk_π_app, Linear.comp_units_smul,
        smul_smul, Int.units_mul_self, one_smul] using h
  differential K I n m p q q' p' hnm hpq hq' hp' := by
    change (CochainComplex.bifunctorHomObj H K I).d n m ≫
      ((m * p).negOnePow • CochainComplex.bifunctorHomπ H K I m p q hpq) = _
    rw [Linear.comp_units_smul,
      CochainComplex.bifunctorHomObj_d_π H K I n m p q hpq q' p' hq' hp']
    have hp' : p' = p + 1 := by omega
    subst m
    subst p'
    simp only [smul_sub, Linear.units_smul_comp, smul_smul]
    have h₁ : ((n + 1) * p).negOnePow * p.negOnePow = (n * p).negOnePow := by
      rw [Int.add_mul, one_mul, Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
    have h₂ : n.negOnePow * (n * (p + 1)).negOnePow = (n * p).negOnePow := by
      rw [Int.mul_add, mul_one, Int.negOnePow_add, mul_left_comm,
        Int.units_mul_self, mul_one]
    rw [h₁, h₂]
  map_projection K K' I I' f g n p q hpq := by
    change (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) f ≫
      CochainComplex.bifunctorHomMapRight (H := H) (K := K') g).f n ≫
        ((n * p).negOnePow • _) = _
    simp only [HomologicalComplex.comp_f, Linear.comp_units_smul, Category.assoc,
      CochainComplex.bifunctorHomMapRight_f_π,
      CochainComplex.bifunctorHomMapLeft_f_π_assoc, Linear.units_smul_comp]

end CategoryTheory.RingedForgetTwoInjective
