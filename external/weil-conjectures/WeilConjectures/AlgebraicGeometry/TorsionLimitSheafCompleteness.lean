/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.TorsionCompletionDefinitions
import WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections

set_option linter.privateModule false

/-! # Completeness of limits of power-torsion pro-etale sheaves

Source: Stacks Project, Tags 099P and 099Q (1), (4), (5)
(auxiliary; not a blueprint node).

We use the existing coefficient-sized small model of the unchanged small pro-etale site.
It is equivalent via AsSmall.down to X.ProEt; its topology is the induced topology.
Thus this changes sizes only, not objects, covers, slices, or coefficient sheaves up to
canonical equivalence. Local completeness is the existing slice internal-Hom definition.
The extended ideal is constructed as the kernel of the constant quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] torsionCompletionQuotient torsionCompletionQuotientOne
  torsionCompletionQuotientMap torsionCompletionIdeal torsionCompletionIdealInclusion

private theorem isIso_on_limit {B : Type u} [Category.{v} B]
    {D : Type*} [Category* D] (F : D ⥤ B) [HasLimit F]
    (P : B ⥤ B) [PreservesLimit F P] (δ : P ⟶ P)
    (hδ : ∀ d, IsIso (δ.app (F.obj d))) : IsIso (δ.app (limit F)) := by
  let α := Functor.whiskerLeft F δ
  have (d : D) : IsIso (α.app d) := hδ d
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let hc := isLimitOfPreserves P (limit.isLimit F)
  let e := IsLimit.conePointsIsoOfNatIso hc hc (asIso α)
  have he : δ.app (limit F) = e.hom := by
    apply hc.hom_ext
    intro d
    change δ.app (limit F) ≫ P.map (limit.π F d) = _
    rw [← δ.naturality]
    exact (IsLimit.conePointsIsoOfNatIso_hom_comp hc hc (asIso α) d).symm
  rw [he]
  infer_instance

private theorem isoLocus_of_iso {B : Type*} [Category* B] (P : B ⥤ B)
    (δ : P ⟶ P) {M N : B} (e : M ≅ N) (h : IsIso (δ.app N)) :
    IsIso (δ.app M) := by
  have := h
  have he : δ.app M = P.map e.hom ≫ δ.app N ≫ P.map e.inv := by
    rw [← Category.assoc, δ.naturality, Category.assoc, ← P.map_comp,
      e.hom_inv_id, P.map_id, Category.comp_id]
  rw [he]
  infer_instance

private theorem difference_iso_of_nilpotent {B : Type*} [Category* B]
    [Preadditive B] {M : B} [HasProduct (fun _ : ℕ ↦ M)]
    (a : End M) (ha : IsNilpotent a) :
    IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ M) (fun _ ↦ a.asHom)) := by
  let s : End (∏ᶜ fun _ : ℕ ↦ M) :=
    .of (towerProductShift (K := fun _ : ℕ ↦ M) (fun _ ↦ a.asHom))
  have hs (r j : ℕ) : (s ^ r).asHom ≫ Pi.π (fun _ : ℕ ↦ M) j =
      Pi.π (fun _ : ℕ ↦ M) (j + r) ≫ (a ^ r).asHom := by
    induction r generalizing j with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, End.mul_asHom, Category.assoc, ih, ← Category.assoc]
      simp only [s, towerProductShift, Pi.lift_comp_π]
      rw [Category.assoc, ← End.mul_asHom, ← pow_succ]
      simp only [Nat.add_assoc]
  obtain ⟨e, he⟩ := ha
  have hnil : IsNilpotent s := by
    refine ⟨e, End.ext (Pi.hom_ext _ _ fun j ↦ ?_)⟩
    simp only [hs, he, End.zero_asHom, comp_zero, zero_comp]
  exact (isUnit_iff_isIso (1 - s)).mp hnil.isUnit_one_sub

private def endPower {B : Type*} [Category* B] {M : B} (a : End M) (n : ℕ) :
    End M := a ^ n

private theorem sectionMultiplication_pow {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat) (U : C)
    (f : O.obj.obj (op U))
    (M : SheafOfModules ((localCoefficientRings O).over U))
    (n : ℕ) (V : (Over U)ᵒᵖ) (x : M.val.obj V) :
    ((endPower (.of (localSectionMultiplication O U f M)) n).asHom.val.app V) x =
      (O.obj.map V.unop.hom.op f) ^ n • x := by
  induction n generalizing x with
  | zero => change x = _; simp
  | succ n ih =>
    change ((endPower (.of (localSectionMultiplication O U f M)) n).asHom.val.app V)
      ((localSectionMultiplication O U f M).val.app V x) = _
    rw [ih]
    change (O.obj.map V.unop.hom.op f) ^ n • ((O.obj.map V.unop.hom.op f) • x) = _
    rw [smul_smul, pow_succ]

end AlgebraicGeometry.Scheme
