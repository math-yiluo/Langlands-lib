/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.InjectiveCechAugmentationQuasiIso
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Total Čech cohomology of a complex of injective sheaves

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 3; Stacks Project Tags 03AW
and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private noncomputable def restriction₀
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C] {X : C}
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    F.obj (op X) ⟶
      ((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
        ((Over.forget X).op ⋙ F)).X 0 :=
  Pi.lift (fun t : Fin 1 → ι ↦
    F.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op)

private theorem restriction₀_naturality
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C] {X : C}
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (f : F ⟶ G) :
    restriction₀ π F ≫
      ((cechComplexFunctor (fun i ↦ Over.mk (π i))).map
        (Functor.whiskerLeft (Over.forget X).op f)).f 0 =
      f.app (op X) ≫ restriction₀ π G := by
  apply Pi.hom_ext
  intro t
  dsimp [restriction₀, cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map, Limits.FormalCoproduct.evalOp]
  simp only [Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc]
  exact f.naturality _

set_option backward.isDefEq.respectTransparency false in
private theorem restriction₀_d
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C] {X : C}
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    restriction₀ π F ≫
      ((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
        ((Over.forget X).op ⋙ F)).d 0 1 = 0 := by
  change restriction₀ π F ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
      Pi.lift (fun t : Fin 2 → ι ↦
        Pi.π (fun s : Fin 1 → ι ↦
          F.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) (t ∘ j.succAbove) ≫
        F.map (Pi.lift (fun k : Fin 1 ↦
          Pi.π (fun k : Fin 2 ↦ Over.mk (π (t k))) (j.succAbove k))).left.op)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  apply Pi.hom_ext
  intro t
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, Pi.lift_comp_π,
    restriction₀, zero_comp]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π_assoc]
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  simp

/-- Row augmentation before extension by zero.
Source: blueprint lem-sc-injective-cech-total-sections, proof Steps 1--3.
(blueprint: lem-sc-injective-cech-total-sections-nat)
Proof: Apply injective Čech acyclicity and the chosen-product comparison to each
row, then apply the first-quadrant column augmentation criterion. -/
theorem injective_cech_total_sections_nat
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
    (hK : ∀ q : ℕ, Injective (K.X q)) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X) (n : ℕ) :
    Nonempty
      (((HomologicalComplex₂.flip
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op ⋙
          cechComplexFunctor (fun i ↦ Over.mk (π i))).mapHomologicalComplex
            (.up ℕ)).obj K)).total (.up ℕ)).homology n ≅
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
            (.up ℕ)).obj K).homology n) := by
  let D := HomologicalComplex₂.flip
    (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op ⋙
      cechComplexFunctor (fun i ↦ Over.mk (π i))).mapHomologicalComplex (.up ℕ)).obj K)
  let A := (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex (.up ℕ)).obj K)
  let a : A ⟶ D.X 0 :=
    { f := fun q ↦ restriction₀ π (K.X q).obj
      comm' := by
        intro q r h
        exact restriction₀_naturality π (K.d q r).hom }
  have ha : a ≫ D.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    exact restriction₀_d π (K.X q).obj
  let b : A ⟶ D.total (.up ℕ) :=
    { f := fun q ↦ a.f q ≫ D.ιTotal (.up ℕ) 0 q q (by simp)
      comm' := by
        intro q r h
        have hr : q + 1 = r := h
        subst r
        simp only [HomologicalComplex₂.total_d, Category.assoc,
          Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
        rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
          q (q + 1) (by simp [Nat.add_comm]),
          D.d₂_eq (.up ℕ) 0
            (by simp : (ComplexShape.up ℕ).Rel q (q + 1)) (q + 1) (by simp)]
        have hz := congrArg (fun f ↦ f.f q) ha
        simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
        have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
        have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
          change (-1 : ℤˣ) ^ 0 = 1
          exact pow_zero _
        simp only [hs₁, hs₂, one_smul, ← Category.assoc, hz, zero_comp, zero_add]
        rw [a.comm q (q + 1)] }
  have hcol : ∀ q : ℕ, QuasiIso
      ((CochainComplex.fromSingle₀Equiv (D.flip.X q) (A.X q)).symm
        ⟨a.f q, by simpa using congrArg (fun f ↦ f.f q) ha⟩) := by
    intro q
    have : Injective (K.X q) := hK q
    apply injective_cech_augmentation_quasiIso (K.X q) X π hπ
    intro t
    simp only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    change restriction₀ π (K.X q).obj ≫ Pi.π _ t = _
    dsimp [restriction₀]
    erw [Pi.lift_comp_π]
  have : QuasiIso b := HomologicalComplex₂.quasiIso_of_column_augmentation
    D A a ha b (fun _ ↦ rfl) hcol
  exact ⟨(isoOfQuasiIsoAt b n).symm⟩

/-- Row augmentation identifies total Čech cohomology with section-complex cohomology.
This is a statement about any nonnegative complex of injective sheaves, with no
resolution, Ext, or sheaf-cohomology hypothesis.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 3;
lem-sc-cech-resolution-total, Steps 1--2; Stacks Project Tags 03AW and 03F6.
(blueprint: lem-sc-injective-cech-total-sections)

Proof: Regard J as its associated precoverage. Choose iterated fibre products of the
covering; the comparison with Mathlib's Čech complex intertwines the alternating
coface maps. In resolution degree q augment the Čech row by K^q(X), mapping a
section to its restrictions to the covering members. The sheaf condition identifies
row cohomology in degree zero with K^q(X); injective Čech acyclicity gives zero in
all positive degrees. The Hom-set, covering-index and group-value universes are v,
so the free abelian representables used for injective acyclicity have the required
size. The augmentations are natural in K^q, and consequently commute with K's
differential. They define a map from the section complex to the total complex;
its degree-q component is the restriction map into the (0,q) summand. The horizontal
differential annihilates this restriction map, and the vertical sign on this
summand is (-1)^0 = 1. Filter the mapping cone by resolution degree. Its associated
rows are the augmented Čech rows, which are exact. The augmented Čech index starts
at -1 and the resolution index starts at 0, so in each total degree the filtration
is finite. The row spectral sequence therefore has zero first page and zero
abutment; the cone is acyclic, and the section-to-total map is a quasi-isomorphism.
Invert its homology isomorphism and identify nonnegative section cohomology with
that of the extension of K by zero to integer degrees. At n = 0 this extension
has zero incoming differential, as does the original section complex. If the
covering family is empty, the covering sheaf condition forces all K^q(X) to be
zero; both complexes are then acyclic, so the same argument still applies. -/
theorem injective_cech_total_sections
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
    (hK : ∀ q : ℕ, Injective (K.X q)) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X) (n : ℕ) :
    Nonempty
      (((HomologicalComplex₂.flip
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget X).op ⋙
          cechComplexFunctor (fun i ↦ Over.mk (π i))).mapHomologicalComplex
            (.up ℕ)).obj K)).total (.up ℕ)).homology n ≅
        (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
            (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ)) := by
  obtain ⟨e⟩ := injective_cech_total_sections_nat K hK X π hπ n
  let S := ((sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
      (.up ℕ)).obj K
  let G := sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)
  let m := HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat G
  exact ⟨e ≪≫ (S.extendHomologyIso ComplexShape.embeddingUpNat (by rfl)).symm ≪≫
    (asIso (HomologicalComplex.homologyMap m.hom (n : ℤ))).symm⟩

end CategoryTheory
