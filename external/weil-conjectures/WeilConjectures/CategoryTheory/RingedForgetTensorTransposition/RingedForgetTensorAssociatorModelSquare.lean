/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorAssociatorDetection
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorModelAssociativity

/-! # The associativity square for ringed tensor chain models

Source: Stacks Project, Tags 0FPT and 06YU.
(blueprint: lem-sf-ringed-forget-associator-model-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTotalTensor

namespace CategoryTheory.RingedForgetTensorTransposition

attribute [local irreducible] tensorSummand

private theorem inverse_assoc {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (X Y Z : B)
    (h : F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (𝟙 (F.obj X) ⊗ₘ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ⊗ₘ 𝟙 (F.obj Z)) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom) :
    (μ.inv.app (X, Y) ▷ F.obj Z) ≫ μ.inv.app (X ⊗ Y, Z) ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        (F.obj X ◁ μ.inv.app (Y, Z)) ≫ μ.inv.app (X, Y ⊗ Z) := by
  apply (cancel_epi (μ.hom.app (X ⊗ Y, Z) ≫
    (μ.hom.app (X, Y) ▷ F.obj Z))).1
  apply (cancel_mono (μ.hom.app (X, Y ⊗ Z) ≫
    (F.obj X ◁ μ.hom.app (Y, Z)))).1
  have hr : (μ.hom.app (X, Y) ▷ F.obj Z) ≫ (μ.inv.app (X, Y) ▷ F.obj Z) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight]
  have hl : (F.obj X ◁ μ.inv.app (Y, Z)) ≫ (F.obj X ◁ μ.hom.app (Y, Z)) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
      MonoidalCategory.whiskerLeft_id]
  simp only [Category.assoc, reassoc_of% hr, hl,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]
  erw [id_tensorHom, tensorHom_id] at h
  exact h

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive]

/-- The two local pure-triple formulas imply the ringed chain associativity square.
Source: Stacks Project, Tags 0FPT and 06YU.
(blueprint: lem-sf-ringed-forget-associator-model-square)

Proof: the sheafification detection theorem identifies both supplied model
associators with the native complex associators from their local pure-triple
formulas. Install the canonical monoidal structures on both sites and expand
only the total-tensor and summand aliases in the comparison data. Cancel the
underived comparison to express its associativity in inverse form, and apply the
abstract model-chain associativity theorem. The result concerns only chain
complexes and is independent of derived representatives and their normalization.
-/
theorem ringed_associator_model_square
    (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (aB : (coefficientTotalTensor.{r, c, v} J R).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N)))
    (aA : (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((coefficientTotalTensor.{s, d, vd} J' R').obj
          ((U.mapHomologicalComplex (.up ℤ)).obj P, (U.mapHomologicalComplex (.up ℤ)).obj Q),
          (U.mapHomologicalComplex (.up ℤ)).obj N) ≅
      (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((U.mapHomologicalComplex (.up ℤ)).obj P,
          (coefficientTotalTensor.{s, d, vd} J' R').obj
            ((U.mapHomologicalComplex (.up ℤ)).obj Q, (U.mapHomologicalComplex (.up ℤ)).obj N)))
    (haB : ∀ (p q t pq qt n : ℤ) (hpq : p + q = pq) (hqt : q + t = qt)
      (hn : pq + t = n) (hn' : p + qt = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X t).val.obj V),
      (aB.hom.f n).val.app V
        (coefficientTensorGenerator.{r, c, v} J R
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N pq t n hn V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q pq hpq V x y) z) =
      coefficientTensorGenerator.{r, c, v} J R P
        ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N)) p qt n hn' V x
        (coefficientTensorGenerator.{r, c, v} J R Q N q t qt hqt V y z))
    (haA : ∀ (p q t pq qt n : ℤ) (hpq : p + q = pq) (hqt : q + t = qt)
      (hn : pq + t = n) (hn' : p + qt = n) (V : Dᵒᵖ)
      (x : (((U.mapHomologicalComplex (.up ℤ)).obj P).X p).val.obj V)
      (y : (((U.mapHomologicalComplex (.up ℤ)).obj Q).X q).val.obj V)
      (z : (((U.mapHomologicalComplex (.up ℤ)).obj N).X t).val.obj V),
      (aA.hom.f n).val.app V
        (coefficientTensorGenerator.{s, d, vd} J' R'
          ((coefficientTotalTensor.{s, d, vd} J' R').obj
            (((U.mapHomologicalComplex (.up ℤ)).obj P), ((U.mapHomologicalComplex (.up ℤ)).obj Q)))
          ((U.mapHomologicalComplex (.up ℤ)).obj N) pq t n hn V
          (coefficientTensorGenerator.{s, d, vd} J' R'
            ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj Q)
            p q pq hpq V x y) z) =
      coefficientTensorGenerator.{s, d, vd} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
        ((coefficientTotalTensor.{s, d, vd} J' R').obj
          (((U.mapHomologicalComplex (.up ℤ)).obj Q), ((U.mapHomologicalComplex (.up ℤ)).obj N)))
        p qt n hn' V x
        (coefficientTensorGenerator.{s, d, vd} J' R'
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) ((U.mapHomologicalComplex (.up ℤ)).obj N)
          q t qt hqt V y z)) :
    let V := U.mapHomologicalComplex (.up ℤ)
    let B := coefficientTotalTensor.{r, c, v} J R
    let A := coefficientTotalTensor.{s, d, vd} J' R'
    V.map aB.hom ≫ chain.hom.app (P, B.obj (Q, N)) ≫
        A.map (X := (V.obj P, V.obj (B.obj (Q, N))))
          (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
          (𝟙 (V.obj P), chain.hom.app (Q, N)) =
      chain.hom.app (B.obj (P, Q), N) ≫
        A.map (X := (V.obj (B.obj (P, Q)), V.obj N))
          (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
          (chain.hom.app (P, Q), 𝟙 (V.obj N)) ≫ aA.hom := by
  have hB := coefficientAssociator_eq_native.{c, v, r} J R P Q N aB haB
  have hA := coefficientAssociator_eq_native.{d, vd, s} J' R'
    ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj Q)
    ((U.mapHomologicalComplex (.up ℤ)).obj N) aA haA
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{d, vd, max d vd s} R'
  let := SheafOfModules.monoidalCategory R'
  unfold tensorSummand at summand
  unfold coefficientTotalTensor at chain summand aB aA hB hA
  dsimp only
  delta coefficientTotalTensor
  exact tensorComparison_model_chain_associativity U u.tensor chain summand
    (fun X Y Z ↦ inverse_assoc U u.tensor X Y Z (u.coherence.associativity X Y Z))
    P Q N aB aA hB hA

end CategoryTheory.RingedForgetTensorTransposition
