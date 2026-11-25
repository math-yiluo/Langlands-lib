/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPowAddIso_assoc_inv {X : Scheme.{u}} (L : X.Modules) (i j k : ℕ) :
    (L.tensorPowAddIso i j).inv ▷ L.tensorPow k ≫
      (L.tensorPowAddIso (i + j) k).inv =
    (α_ (L.tensorPow i) (L.tensorPow j) (L.tensorPow k)).hom ≫
      L.tensorPow i ◁ (L.tensorPowAddIso j k).inv ≫
      (L.tensorPowAddIso i (j + k)).inv ≫
      eqToHom (congrArg L.tensorPow (Nat.add_assoc i j k).symm) := by
  induction i with
  | zero =>
    dsimp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv]
    rw [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc,
      ← eqToHom_iso_inv_naturality (fun n ↦ L.tensorPowAddIso n k) (Nat.zero_add j).symm]
    simp only [Category.assoc, eqToHom_trans]
    simp only [← Category.assoc]
    congr 1
    monoidal
  | succ i ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorPow_succ, tensorIso_inv, Iso.refl_inv, id_tensorHom]
    rw [comp_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight,
      Category.assoc, Category.assoc,
      ← eqToHom_iso_inv_naturality (fun n ↦ L.tensorPowAddIso n k)
        (Nat.succ_add i j).symm]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, id_tensorHom, Category.assoc, eqToHom_trans]
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, ih]
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom, eqToHom_trans]
    simp only [← Category.assoc]
    congr 1
    monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPowMulIso_add_inv
    {X : Scheme.{u}} (L : X.Modules) (d n b : ℕ) :
    ((L.tensorPowMulIso d n).inv ⊗ₘ (L.tensorPowMulIso d b).inv) ≫
        (L.tensorPowAddIso (d * n) (d * b)).inv ≫
        eqToHom (congrArg L.tensorPow (Nat.mul_add d n b).symm) =
      ((L.tensorPow d).tensorPowAddIso n b).inv ≫
        (L.tensorPowMulIso d (n + b)).inv := by
  induction n with
  | zero =>
    simp only [tensorPowMulIso, tensorPowAddIso, Iso.trans_inv, Iso.symm_inv,
      eqToIso.inv, Nat.mul_zero, eqToHom_refl, id_tensorHom, Category.assoc, tensorPow_zero]
    rw [← eqToHom_iso_inv_naturality (fun k ↦ L.tensorPowMulIso d k)
      (Nat.zero_add b).symm]
    simp only [eqToHom_trans]
    rw [leftUnitor_naturality_assoc]
  | succ n ih =>
    have ih' :
        ((L.tensorPowMulIso d n).inv ⊗ₘ (L.tensorPowMulIso d b).inv) ≫
          (L.tensorPowAddIso (d * n) (d * b)).inv =
        ((L.tensorPow d).tensorPowAddIso n b).inv ≫
          (L.tensorPowMulIso d (n + b)).inv ≫
          eqToHom (congrArg L.tensorPow (Nat.mul_add d n b)) := by
      rw [← Category.assoc, ← ih]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, tensorPow_succ, Category.assoc]
    rw [← eqToHom_iso_inv_naturality (fun k ↦ L.tensorPowMulIso d k)
      (Nat.succ_add n b).symm]
    simp only [tensorPowMulIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
      eqToIso.inv, tensorPow_succ]
    simp only [tensorHom_def', comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
    rw [← eqToHom_iso_inv_naturality_assoc
      (fun k ↦ L.tensorPowAddIso k (d * b)) (by ring : d + d * n = d * (n + 1))]
    simp only [id_whiskerRight, Category.id_comp]
    rw [reassoc_of% tensorPowAddIso_assoc_inv L d (d * n) (d * b),
      associator_naturality_middle_assoc,
      associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← tensorHom_def', ← whiskerLeft_comp_assoc, ih']
    simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_eqToHom]
    rw [← eqToHom_iso_inv_naturality_assoc
      (fun k ↦ L.tensorPowAddIso d k) (Nat.mul_add d n b)]
    simp only [eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem block_one {Z : Scheme.{u}} {M : Z.Modules}
    (f : 𝟙_ Z.Modules ⟶ M) (b : ℕ) (x : 𝟙_ Z.Modules ⟶ M.tensorPow b) :
    (tensorPowSection f 1 ⊗ₘ x) ≫ (M.tensorPowAddIso 1 b).inv ≫
      eqToHom (congrArg M.tensorPow (Nat.one_add b)) = f ⊗ₘ x := by
  simp only [tensorPowSection, tensorPowAddIso, Iso.trans_inv, Iso.symm_inv,
    eqToIso.inv, tensorIso_inv, Iso.refl_inv, tensorPow_succ, tensorPow_zero,
    Category.assoc]
  simp only [id_tensorHom, whiskerLeft_comp, whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [tensorHom_def, comp_whiskerRight,
    Category.assoc]
  monoidal


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem power_add_aux {X Z : Scheme.{u}} (F : X.Modules ⥤ Z.Modules)
    [F.LaxMonoidal] (L : X.Modules)
    (P : ∀ d : ℕ, F.obj (L.tensorPow d) ≅ (F.obj L).tensorPow d)
    (h0 : (P 0).inv = Functor.LaxMonoidal.ε F)
    (hs : ∀ d : ℕ, (P (d + 1)).inv =
      (𝟙 (F.obj L) ⊗ₘ (P d).inv) ≫ Functor.LaxMonoidal.μ F L (L.tensorPow d))
    (a b : ℕ) :
    ((P a).inv ⊗ₘ (P b).inv) ≫
      Functor.LaxMonoidal.μ F (L.tensorPow a) (L.tensorPow b) ≫
      F.map (L.tensorPowAddIso a b).inv =
    ((F.obj L).tensorPowAddIso a b).inv ≫ (P (a + b)).inv := by
  induction a with
  | zero =>
    rw [h0]
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Functor.map_comp, Category.assoc]
    change (Functor.LaxMonoidal.ε F ⊗ₘ
      (P b).inv) ≫
        Functor.LaxMonoidal.μ F (𝟙_ X.Modules) (L.tensorPow b) ≫
          F.map (λ_ (L.tensorPow b)).hom ≫
          F.map (eqToHom _) = _
    rw [Functor.LaxMonoidal.ε_tensorHom_comp_μ_assoc]
    simp only [← Functor.map_comp]
    rw [← eqToHom_iso_inv_naturality (P)
      (Nat.zero_add b).symm]
    rw [leftUnitor_naturality_assoc]
    simp only [Iso.inv_hom_id_assoc, eqToHom_map]
  | succ a ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      tensorIso_inv, Iso.refl_inv, Functor.map_comp, Category.assoc]
    rw [← eqToHom_iso_inv_naturality (P)
      (Nat.succ_add a b).symm]
    rw [hs a, hs (a + b)]
    simp only [Category.assoc]
    simp only [tensorHom_def, comp_whiskerRight, id_whiskerRight,
      Category.id_comp, Category.assoc]
    rw [← whisker_exchange_assoc]
    erw [Functor.LaxMonoidal.associativity_assoc F L (L.tensorPow a) (L.tensorPow b)]
    rw [associator_naturality_right_assoc, associator_naturality_middle_assoc]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← tensorHom_def,
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [ih]
    simp only [whiskerLeft_comp, Category.assoc, eqToHom_map]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_power_add {X Z : Scheme.{u}} (j : Z ⟶ X)
    (L : X.Modules) (a b : ℕ) :
    ((boundaryPullbackPowIso j L a).inv ⊗ₘ (boundaryPullbackPowIso j L b).inv) ≫
      (boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow b)).inv ≫
      (tensorPullback j).map (L.tensorPowAddIso a b).inv =
    (((tensorPullback j).obj L).tensorPowAddIso a b).inv ≫
      (boundaryPullbackPowIso j L (a + b)).inv := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hT (A B : X.Modules) : (boundaryPullbackTensorIso j A B).inv =
      Functor.LaxMonoidal.μ (tensorPullback j) A B := by
    rfl
  have he : (pullbackObjUnitIso j).inv = Functor.LaxMonoidal.ε (pullback j) := by
    apply (cancel_mono (pullbackObjUnitIso j).hom).mp
    rw [Iso.inv_hom_id, ← pullback_monoidal_unit_comparison j]
    exact (Functor.Monoidal.ε_η (pullback j)).symm
  have h0 : (boundaryPullbackPowIso j L 0).inv =
      Functor.LaxMonoidal.ε (tensorPullback j) := by
    change (pullbackObjUnitIso j).inv ≫ (boundaryPullbackComparison j).inv.app _ =
      Functor.LaxMonoidal.ε (pullback j) ≫ (boundaryPullbackComparison j).inv.app _
    rw [he]
    rfl
  rw [hT]
  exact power_add_aux (tensorPullback j) L (boundaryPullbackPowIso j L) h0
    (fun d ↦ by
      change (𝟙 _ ⊗ₘ (boundaryPullbackPowIso j L d).inv) ≫
        (boundaryPullbackTensorIso j L (L.tensorPow d)).inv = _
      rw [hT]) a b


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility of the canonical section-degree comparison with multiplication.
Source: Stacks Project, Tag 01CD, tensor pullback, and Tag 09MS, tensor powers.
(blueprint: lem-sc-square-zero-tensor-section-product-comparison).
Proof: Replace D by canonicalTensorBoundaryComparisons using hD. Its section
comparison is boundaryPullbackPowIso followed by tensorPowMulIso. Expand these
recursive isomorphisms, and use naturality of boundaryPullbackComparison and the
monoidal pullback tensorator. The tensor-power addition map groups the first n
factors and the remaining n(e+1) factors; the tensor-power multiplication map groups
the same factors into blocks of n. Associator coherence identifies these groupings.
The degree-one power tensorPowSection f 1 is f followed by the inverse right unitor;
its unitor cancels the degree-one tensorPowMulIso. Evaluate the resulting morphism
equality at 1, using tensorHom_app_tmulSection and the inverse left unitor formula.
The arithmetic equality hdeg only transports the target degree. For n=0 all factors
are units and the same triangle and unitor identities apply; for e=0 the argument
is the two-block case. No graded presentation or cohomology property is used. -/
theorem tensorSectionProduct_comparison {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (hdeg : n * (0 + 1) + n * (e + 1) = n * ((e + 1) + 1)) :
    ((tensorPullback j).map (eqToHom (congrArg L.tensorPow hdeg))).app ⊤
      (((tensorPullback j).map
        (L.tensorPowAddIso (n * (0 + 1)) (n * (e + 1))).inv).app ⊤
        ((boundaryPullbackTensorIso j (L.tensorPow (n * (0 + 1)))
          (L.tensorPow (n * (e + 1)))).inv.app ⊤
          (tmulSection
            ((tensorPowSection f 1 ≫ (D.a 0).inv).app ⊤ (1 : Γ(Z, ⊤)))
            ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))))) =
      ((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤
        (1 : Γ(Z, ⊤))) := by
  subst D
  let M := (tensorPullback j).obj L
  have h :
      ((tensorPowSection f 1 ≫ (boundarySectionDegreeIso j L n 0).inv) ⊗ₘ
        (x ≫ (boundarySectionDegreeIso j L n e).inv)) ≫
        (boundaryPullbackTensorIso j (L.tensorPow (n * (0 + 1)))
          (L.tensorPow (n * (e + 1)))).inv ≫
        (tensorPullback j).map (L.tensorPowAddIso (n * (0 + 1)) (n * (e + 1))).inv ≫
        (tensorPullback j).map (eqToHom (congrArg L.tensorPow hdeg)) =
      (f ⊗ₘ x) ≫ (boundarySectionDegreeIso j L n (e + 1)).inv := by
    dsimp only [boundarySectionDegreeIso]
    simp only [Iso.trans_inv]
    rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [reassoc_of% pullback_power_add j L (n * 1) (n * (e + 1))]
    rw [eqToHom_map]
    rw [eqToHom_iso_inv_naturality (boundaryPullbackPowIso j L) hdeg]
    have hc : eqToHom (congrArg M.tensorPow hdeg) =
        eqToHom (congrArg M.tensorPow (Nat.mul_add n 1 (e + 1)).symm) ≫
          eqToHom (congrArg M.tensorPow (congrArg (n * ·) (Nat.one_add (e + 1)))) := by
      rw [eqToHom_trans]
    rw [hc]
    simp only [Category.assoc]
    rw [reassoc_of% tensorPowMulIso_add_inv M n 1 (e + 1)]
    rw [reassoc_of% eqToHom_iso_inv_naturality (fun k ↦ M.tensorPowMulIso n k)
      (Nat.one_add (e + 1))]
    rw [reassoc_of% block_one f (e + 1) x]
  have heval := congrArg
    (fun k ↦ ((λ_ (𝟙_ Z.Modules)).inv ≫ k).app ⊤ (unitSectionsEquiv ⊤ 1)) h
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, leftUnitor_inv_app,
    tensorHom_app_tmulSection] at heval
  have hu : unitSectionsEquiv (X := Z) ⊤ 1 = (1 : Γ(Z, ⊤)) := rfl
  simpa only [canonicalTensorBoundaryComparisons, hu, Hom.comp_app, ConcreteCategory.comp_apply,
    leftUnitor_inv_app, tensorHom_app_tmulSection] using heval

end
end AlgebraicGeometry.Scheme.Modules
