/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCechResolutionDoubleComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # Total homology of the étale open Čech resolution

Source: Stacks Project, Tags 03AW, 03F6 and 03AZ.
(blueprint: lem-sc-etale-open-cech-resolution-total)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def restriction₀
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale) {ι : Type u} (U : ι → X.Opens)
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op (i.obj ⊤)) ⟶ ((cechComplexFunctor U).obj (i.op ⋙ F)).X 0 :=
  Pi.lift (fun _t : Fin 1 → ι ↦ F.map (i.map (homOfLE le_top)).op)

private theorem restriction₀_naturality
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale) {ι : Type u} (U : ι → X.Opens)
    {F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    restriction₀ X i U F ≫
      ((cechComplexFunctor U).map (Functor.whiskerLeft i.op f)).f 0 =
      f.app (op (i.obj ⊤)) ≫ restriction₀ X i U G := by
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
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale) {ι : Type u} (U : ι → X.Opens)
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    restriction₀ X i U F ≫ ((cechComplexFunctor U).obj (i.op ⋙ F)).d 0 1 = 0 := by
  change restriction₀ X i U F ≫
    (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
      Pi.lift (fun t : Fin 2 → ι ↦
        Pi.π (fun s : Fin 1 → ι ↦
          F.obj (op (i.obj (∏ᶜ fun k ↦ U (s k))))) (t ∘ j.succAbove) ≫
        F.map (i.map (Pi.lift (fun k : Fin 1 ↦
          Pi.π (fun k : Fin 2 ↦ U (t k)) (j.succAbove k)))).op)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  apply Pi.hom_ext
  intro t
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, Pi.lift_comp_π,
    restriction₀, zero_comp]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π_assoc]
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ← i.map_comp, ← i.map_comp]
  change F.map (i.map (homOfLE (show (∏ᶜ fun k : Fin 2 ↦ U (t k)) ≤ ⊤ from le_top))).op +
    -F.map (i.map (homOfLE (show (∏ᶜ fun k : Fin 2 ↦ U (t k)) ≤ ⊤ from le_top))).op = 0
  exact add_neg_cancel _

/-- The total Čech complex of an injective resolution over an open covering
computes derived evaluation, without affineness or acyclicity of G on opens.

Source: Stacks Project, Tags 03AW, 03F6 and 03AZ, the augmentation comparison.
(blueprint: lem-sc-etale-open-cech-resolution-total)

Proof: Cover preservation sends the open covering to a covering of i(top).
Preservation of finite limits identifies iterated fibre products of this image
cover with i of the intersections of opens, compatibly with all projections.
Thus each horizontal Čech row of the displayed double complex is the Čech
complex of the corresponding injective étale sheaf on this cover. Augment it by
its sections at i(top). The sheaf condition identifies degree-zero homology with
those sections, and injective Čech acyclicity (03AW, 03F6) gives zero positive
homology. The restriction augmentations commute with the resolution differential
and define a map from the evaluated resolution to the total complex. The
horizontal differential on its image is zero and the vertical sign in Čech
degree zero is +1. Filter its cone by resolution degree: its rows are exact
augmented Čech complexes. The first-quadrant boundedness makes the filtration
finite in each total degree, so the row spectral sequence of the cone has zero
abutment. Therefore the augmentation is a quasi-isomorphism. Finally the
injective-resolution computation of rightDerived identifies homology of the
evaluated resolution with derived evaluation. Compose with the inverse of the
augmentation homology isomorphism. This includes empty coverings: the sheaf
condition then forces sections at i(top) of all resolution terms to be zero.
No separatedness or affine vanishing is involved. -/
theorem nonempty_etale_openCech_resolution_total_iso
    (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (I : InjectiveResolution G) (n : ℕ) :
    Nonempty (((etaleOpenCechResolutionDoubleComplex X i U I).total (.up ℕ)).homology n ≅
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (i.obj ⊤))).rightDerived n).obj G)) := by
  let D := etaleOpenCechResolutionDoubleComplex X i U I
  let F := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op (i.obj ⊤))
  let A := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let a : A ⟶ D.X 0 :=
    { f := fun q ↦ restriction₀ X i U (I.cocomplex.X q).obj
      comm' := by
        intro q r h
        exact restriction₀_naturality X i U (I.cocomplex.d q r).hom }
  have ha : a ≫ D.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    exact restriction₀_d X i U (I.cocomplex.X q).obj
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
    apply etaleOpenCechInjectiveAugmentation_quasiIso X i hc ht U hcover (I.cocomplex.X q)
    intro t
    simp only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    change restriction₀ X i U (I.cocomplex.X q).obj ≫ Pi.π _ t = _
    dsimp [restriction₀]
    erw [Pi.lift_comp_π]
  have : QuasiIso b := HomologicalComplex₂.quasiIso_of_column_augmentation
    D A a ha b (fun _ ↦ rfl) hcol
  exact ⟨(isoOfQuasiIsoAt b n).symm ≪≫ (I.isoRightDerivedObj F n).symm⟩

end AlgebraicGeometry.Scheme
