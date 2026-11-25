/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# Finite free coordinates for internal scalar extension

Source: blueprint main-20261015, `chap-The-pro-etale-site`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).

The formulas are equalities of morphisms involving the canonical coequalizer projection.
They consequently specify the formulas on local elementary tensors without identifying
sections of a tensor sheaf with objectwise tensors. Finite products represent the finite
powers and, in an additive category, also the finite direct sums.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

/-- The finite-free coordinate assertion, including existence of the coequalizers and
preservation properties needed to form scalar extension. The quantification over their
instances merely allows the statement to use these consequences; it is independent of
proof choices. The finite-power functor is the constant-diagram functor followed by limit.
The chosen free module and its basis inclusions use `Mod.finiteFree` and `biproduct.ι`.

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).
-/
def FiniteFreeScalarCoordinates
    {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
    [Abelian H] : Prop :=
  Nonempty (MonoidalPreadditive H) ∧
  HasCoequalizers H ∧
  (∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
    PreservesColimitsOfSize.{0, 0} (tensorRight X)) ∧
  ∀ [MonoidalPreadditive H] [HasCoequalizers H]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (R B : H) [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
    (φ : R ⟶ B) [IsMonHom φ] (n : ℕ)
    (θ : finiteFree R n ≅ (comap φ).obj (regular B)),
    ∃ Φ : extendScalars φ ⋙ comap φ ≅
        Functor.const (Discrete (Fin n)) ⋙ lim,
      ∀ M : Mod H R,
        (∀ i : Fin n,
          extendπ φ M ≫ (Φ.hom.app M).hom ≫
              (Pi.π (fun _ : Fin n ↦ M) i).hom =
            (θ.inv ≫ biproduct.π (fun _ : Fin n ↦ regular R) i).hom ▷ M.X ≫ γ[R,M.X]) ∧
        (Φ.inv.app M).hom =
          ∑ i : Fin n,
            (Pi.π (fun _ : Fin n ↦ M) i).hom ≫ (λ_ M.X).inv ≫
              (η[R] ≫ (biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ θ.hom).hom) ▷ M.X ≫
              extendπ φ M

section Coordinates

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [Abelian H] [MonoidalPreadditive H] [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R B : H} [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
  (φ : R ⟶ B) [IsMonHom φ]

omit [Abelian H] [MonoidalPreadditive H] [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [MonObj R] [IsCommMonObj R] [IsMonHom φ] in
private lemma scalar_right_action :
    (β_ B R).hom ≫ φ ▷ B ≫ μ[B] = B ◁ φ ≫ μ[B] := by
  rw [← BraidedCategory.braiding_naturality_right_assoc, IsCommMonObj.mul_comm]

private noncomputable def scalarTensorIso (M : Mod H R) :
    (comap φ).obj (extendScalarsObj φ M) ≅ (comap φ).obj (regular B) ⊗ M := by
  let N := (comap φ).obj (regular B)
  have h : ((β_ B R).hom ≫ γ[R,N.X]) = B ◁ φ ≫ μ[B] :=
    scalar_right_action φ
  let f : (extendScalarsObj φ M).X ⟶ (N ⊗ M).X :=
    extendDescHom φ (tensorObjπ N M) (by
      rw [← h]
      exact tensorObjπ_condition N M)
  let g : (N ⊗ M).X ⟶ (extendScalarsObj φ M).X :=
    coequalizer.desc (extendπ φ M) (by
      change ((β_ B R).hom ≫ γ[R,N.X]) ▷ M.X ≫ extendπ φ M = _
      rw [h]
      exact extendπ_condition φ M)
  have hf : extendπ φ M ≫ f = tensorObjπ N M :=
    extendπ_extendDescHom φ _ _
  have hg : tensorObjπ N M ≫ g = extendπ φ M := coequalizer.π_desc _ _
  let e : (extendScalarsObj φ M).X ≅ (N ⊗ M).X :=
    { hom := f
      inv := g
      hom_inv_id := by
        rw [← cancel_epi (extendπ φ M)]
        simp only [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        rw [← cancel_epi (tensorObjπ N M)]
        simp only [← Category.assoc, hg, hf, Category.comp_id] }
  refine isoMk (M := (comap φ).obj (extendScalarsObj φ M)) (N := N ⊗ M) e ?_
  change (φ ▷ _ ≫ γ[B,(extendScalarsObj φ M).X]) ≫ f = R ◁ f ≫ γ[R,(N ⊗ M).X]
  simp only [Category.assoc]
  rw [← cancel_epi (R ◁ extendπ φ M)]
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc,
    ← whiskerLeft_comp_assoc, hf, whiskerLeft_tensorπ_smul]
  erw [associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]
  rfl

omit [Abelian H] [MonoidalPreadditive H] in
private lemma scalarTensorIso_hom (M : Mod H R) :
    extendπ φ M ≫ (scalarTensorIso φ M).hom.hom =
      tensorObjπ ((comap φ).obj (regular B)) M := by
  dsimp only [scalarTensorIso]
  exact extendπ_extendDescHom φ _ _

omit [Abelian H] [MonoidalPreadditive H] in
private lemma scalarTensorIso_naturality {M N : Mod H R} (f : M ⟶ N) :
    (comap φ).map ((extendScalars φ).map f) ≫ (scalarTensorIso φ N).hom =
      (scalarTensorIso φ M).hom ≫ ((comap φ).obj (regular B) ◁ f) := by
  apply hom_ext
  rw [← cancel_epi (extendπ φ M)]
  change extendπ φ M ≫ (extendScalarsMap φ f).hom ≫ (scalarTensorIso φ N).hom.hom =
    extendπ φ M ≫ (scalarTensorIso φ M).hom.hom ≫ _
  rw [extendπ_extendScalarsMap_assoc, scalarTensorIso_hom,
    ← Category.assoc, scalarTensorIso_hom, tensorObjπ_whiskerLeft]
  rfl

variable {φ} {n : ℕ} (θ : finiteFree R n ≅ (comap φ).obj (regular B))

private noncomputable def finiteCoordinateIso (M : Mod H R) :
    (comap φ).obj (extendScalarsObj φ M) ≅ ∏ᶜ (fun _ : Fin n ↦ M) :=
  scalarTensorIso φ M ≪≫ whiskerRightIso θ.symm M ≪≫
    rightDistributor (fun _ : Fin n ↦ regular R) M ≪≫
    biproduct.mapIso (fun _ : Fin n ↦ λ_ M) ≪≫ biproduct.isoProduct _

private lemma finiteCoordinateIso_π (M : Mod H R) (i : Fin n) :
    (finiteCoordinateIso θ M).hom ≫ Pi.π (fun _ : Fin n ↦ M) i =
      (scalarTensorIso φ M).hom ≫
        ((θ.inv ≫ biproduct.π (fun _ : Fin n ↦ regular R) i) ▷ M) ≫ (λ_ M).hom := by
  simp [finiteCoordinateIso, biproduct.isoProduct_hom, comp_whiskerRight, Category.assoc]

private lemma finiteCoordinateIso_naturality {M N : Mod H R} (f : M ⟶ N) :
    (comap φ).map ((extendScalars φ).map f) ≫ (finiteCoordinateIso θ N).hom =
      (finiteCoordinateIso θ M).hom ≫
        (Functor.const (Discrete (Fin n)) ⋙ lim).map f := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, finiteCoordinateIso_π]
  have hp : (Functor.const (Discrete (Fin n)) ⋙ lim).map f ≫
      Pi.π (fun _ : Fin n ↦ N) i = Pi.π (fun _ : Fin n ↦ M) i ≫ f :=
    limMap_π ((Functor.const (Discrete (Fin n))).map f) ⟨i⟩
  rw [hp]
  rw [← Category.assoc (finiteCoordinateIso θ M).hom (Pi.π _ i) f,
    finiteCoordinateIso_π]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality]
  erw [← whisker_exchange_assoc]
  rw [← Category.assoc, scalarTensorIso_naturality]
  simp only [Category.assoc]

end Coordinates

end CategoryTheory.Mod
