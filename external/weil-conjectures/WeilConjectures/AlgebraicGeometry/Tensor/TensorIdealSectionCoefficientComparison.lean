/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorHomogeneousKernelAction
import WeilConjectures.AlgebraicGeometry.TensorPullbackPowerAppend
import all WeilConjectures.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition
import all WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit

/-! # Coefficient coordinates for homogeneous ideal multiplication

Source: Stacks Project, Tag 09MS, tensor powers in the graded ideal sequence;
Tag 01CD, monoidal pullback of modules.
(blueprint: lem-sc-tensor-ideal-section-coefficient-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] tensorPullback boundaryPullbackComparison
  canonicalTensorBoundaryComparisons tensorIdealSectionMultiply boundarySectionDegreeIso
  boundaryCoefficientDegreeIso boundaryPullbackPowIso boundaryTensorPowIso
  tensorPowAddIso tensorPowMulIso Scheme.IdealSheafData.toModules
noncomputable section

-- The regrouping lemmas below use the proved private tensor-power identities in
-- InvertibleSectionRing and SectionRingVeroneseNumeratorTransition.

private theorem beta_eq {X Z : Scheme.{u}} (j : Z ⟶ X) (A B : X.Modules) :
    let := Functor.Monoidal.transport (boundaryPullbackComparison j).symm
    (boundaryPullbackTensorIso j A B).hom =
      Functor.OplaxMonoidal.δ (tensorPullback j) A B := by
  simp only [Functor.Monoidal.transport_δ, boundaryPullbackTensorIso, Iso.trans_hom,
    Iso.symm_hom, tensorIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_inv,
    Functor.Monoidal.μIso_inv]
private theorem beta_inv_eq {X Z : Scheme.{u}} (j : Z ⟶ X) (A B : X.Modules) :
    let := Functor.Monoidal.transport (boundaryPullbackComparison j).symm
    (boundaryPullbackTensorIso j A B).inv =
      Functor.LaxMonoidal.μ (tensorPullback j) A B := by
  rw [← cancel_epi (boundaryPullbackTensorIso j A B).hom, Iso.hom_inv_id, beta_eq,
    Functor.Monoidal.δ_μ]

private def blockIso {X : Scheme.{u}} (I L : X.Modules) (n e : ℕ) :
    I ⊗ L.tensorPow (n * (e + 1)) ≅ (I ⊗ L.tensorPow n) ⊗ (L.tensorPow n).tensorPow e :=
  (Iso.refl I ⊗ᵢ L.tensorPowMulIso n (e + 1)) ≪≫ (α_ _ _ _).symm

private theorem block_concat_inv {X : Scheme.{u}} (I L : X.Modules) (n e : ℕ)
    (h : n * (e + 1) + n * (0 + 1) = n * ((e + 1) + 1)) :
    (α_ (I ⊗ L.tensorPow n) ((L.tensorPow n).tensorPow e)
        ((L.tensorPow n).tensorPow 1)).hom ≫
      (I ⊗ L.tensorPow n) ◁ ((L.tensorPow n).tensorPowAddIso e 1).inv ≫
      (blockIso I L n (e + 1)).inv =
    ((blockIso I L n e).inv ⊗ₘ (L.tensorPowMulIso n 1).inv) ≫
      (α_ I (L.tensorPow (n * (e + 1))) (L.tensorPow (n * (0 + 1)))).hom ≫
      I ◁ (L.tensorPowAddIso (n * (e + 1)) (n * (0 + 1))).inv ≫
      I ◁ eqToHom (congrArg L.tensorPow h) := by
  have hh := tensorPowMulIso_add_inv L n (e + 1) 1
  simp only [blockIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
    Category.assoc, tensorHom_def, comp_whiskerRight,
    id_whiskerRight, Category.id_comp, tensorPow_succ]
  conv_rhs =>
    erw [associator_naturality_right_assoc, associator_naturality_middle_assoc]
  erw [← whiskerLeft_comp_assoc, ← tensorHom_def, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp, hh]
  simp only [whiskerLeft_comp]
  simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
    eqToIso.inv, id_tensorHom, eqToHom_refl, Category.comp_id, whiskerLeft_comp,
    Category.assoc]
  erw [associator_naturality_right_assoc]
  erw [pentagon_assoc]

private theorem powIso_add {Z : Scheme.{u}} {A B : Z.Modules} (t : A ≅ B) (a b : ℕ) :
    (A.tensorPowAddIso a b).inv ≫ (boundaryTensorPowIso t (a + b)).hom =
      ((boundaryTensorPowIso t a).hom ⊗ₘ (boundaryTensorPowIso t b).hom) ≫
        (B.tensorPowAddIso a b).inv := by
  induction a with
  | zero =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      boundaryTensorPowIso, Iso.refl_hom, Category.assoc]
    erw [← eqToHom_iso_hom_naturality (fun k ↦ boundaryTensorPowIso t k)
      (Nat.zero_add b).symm]
    simp only [id_tensorHom]
    erw [leftUnitor_naturality_assoc]
  | succ a ih =>
    simp only [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
      Category.assoc]
    erw [← eqToHom_iso_hom_naturality (fun k ↦ boundaryTensorPowIso t k)
      (Nat.succ_add a b).symm]
    simp only [boundaryTensorPowIso, tensorIso_hom, tensorIso_inv, Iso.refl_inv]
    erw [associator_naturality_assoc]
    simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, ih]

private theorem powIso_append {Z : Scheme.{u}} {A B : Z.Modules} (t : A ≅ B) (e : ℕ) :
    A.tensorPow e ◁ (ρ_ A).inv ≫ (A.tensorPowAddIso e 1).inv ≫
        (boundaryTensorPowIso t (e + 1)).hom =
      ((boundaryTensorPowIso t e).hom ⊗ₘ t.hom) ≫
        B.tensorPow e ◁ (ρ_ B).inv ≫ (B.tensorPowAddIso e 1).inv := by
  erw [powIso_add]
  simp only [boundaryTensorPowIso, tensorIso_hom, Iso.refl_hom]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, tensorHom_id]
  erw [rightUnitor_inv_naturality]
  rfl

private theorem block_append {X : Scheme.{u}} (I L : X.Modules) (n e : ℕ)
    (h : n * (e + 1) + n = n * ((e + 1) + 1)) :
    (blockIso I L n e).inv ▷ L.tensorPow n ≫
        (α_ I (L.tensorPow (n * (e + 1))) (L.tensorPow n)).hom ≫
        I ◁ (L.tensorPowAddIso (n * (e + 1)) n).inv ≫
        I ◁ eqToHom (congrArg L.tensorPow h) ≫ (blockIso I L n (e + 1)).hom =
      (α_ (I ⊗ L.tensorPow n) ((L.tensorPow n).tensorPow e) (L.tensorPow n)).hom ≫
        (I ⊗ L.tensorPow n) ◁
          (((L.tensorPow n).tensorPow e ◁ (ρ_ (L.tensorPow n)).inv) ≫
            ((L.tensorPow n).tensorPowAddIso e 1).inv) := by
  have hh := congrArg
    (fun k ↦ ((I ⊗ L.tensorPow n) ⊗ (L.tensorPow n).tensorPow e) ◁
      (ρ_ (L.tensorPow n)).inv ≫ k ≫ (blockIso I L n (e + 1)).hom)
    (block_concat_inv I L n e (by simpa only [Nat.zero_add, Nat.mul_one] using h))
  simp only [tensorPowMulIso_one_inv, Category.comp_id, Category.assoc,
    Iso.inv_hom_id, tensorHom_def] at hh
  erw [whisker_exchange_assoc] at hh
  simp only [← whiskerLeft_comp_assoc] at hh
  erw [associator_naturality_right_assoc] at hh
  simp only [← whiskerLeft_comp] at hh
  simp only [Nat.reduceAdd, Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp] at hh
  erw [associator_naturality_right_assoc] at hh
  simp only [whiskerLeft_eqToHom, ← whiskerLeft_comp] at hh
  have hc := eqToHom_iso_inv_naturality
    (fun k ↦ Iso.refl I ⊗ᵢ L.tensorPowAddIso (n * (e + 1)) k) (Nat.mul_one n).symm
  simp only [tensorIso_inv, Iso.refl_inv, id_tensorHom] at hc
  erw [← reassoc_of% hc] at hh
  simpa only [Category.assoc, eqToHom_trans_assoc, whiskerLeft_eqToHom] using hh.symm

private theorem section_one {Z : Scheme.{u}} {N : Z.Modules} (f : 𝟙_ Z.Modules ⟶ N) :
    tensorPowSection f 1 = f ≫ (ρ_ N).inv := by
  simp only [tensorPowSection, tensorHom_id]
  erw [rightUnitor_inv_naturality]
  congr 1
  exact unitors_inv_equal

private theorem pullback_pow_append_iso {X Z : Scheme.{u}} (j : Z ⟶ X)
    (B : X.Modules) {N : Z.Modules} (t : (tensorPullback j).obj B ≅ N) (e : ℕ) :
    (boundaryPullbackTensorIso j (B.tensorPow e) B).inv ≫
        (tensorPullback j).map
          ((B.tensorPow e ◁ (ρ_ B).inv) ≫ (B.tensorPowAddIso e 1).inv) ≫
        (boundaryPullbackPowIso j B (e + 1) ≪≫
          boundaryTensorPowIso t (e + 1)).hom =
      ((boundaryPullbackPowIso j B e ≪≫ boundaryTensorPowIso t e).hom ⊗ₘ t.hom) ≫
        (N.tensorPow e ◁ (ρ_ N).inv) ≫ (N.tensorPowAddIso e 1).inv := by
  simp only [Iso.trans_hom]
  have hh := congrArg (fun k ↦ k ≫ (boundaryTensorPowIso t (e + 1)).hom)
    (boundaryPullbackPowIso_append j B e)
  simp only [Category.assoc] at hh
  erw [hh, powIso_append]
  simp only [tensorHom_def, Category.assoc, comp_whiskerRight]

private def coeffIso {X Z : Scheme.{u}} (j : Z ⟶ X) (Q B : X.Modules)
    {N : Z.Modules} (t : (tensorPullback j).obj B ≅ N) (e : ℕ) :
    (tensorPullback j).obj (Q ⊗ B.tensorPow e) ≅
      (tensorPullback j).obj Q ⊗ N.tensorPow e :=
  boundaryPullbackTensorIso j Q (B.tensorPow e) ≪≫
    (Iso.refl _ ⊗ᵢ (boundaryPullbackPowIso j B e ≪≫ boundaryTensorPowIso t e))

private theorem coefficient_append {X Z : Scheme.{u}} (j : Z ⟶ X) (Q B : X.Modules)
    {N : Z.Modules} (t : (tensorPullback j).obj B ≅ N)
    (f : 𝟙_ Z.Modules ⟶ N) (e : ℕ) :
    (coeffIso j Q B t e).inv ≫
        (ρ_ ((tensorPullback j).obj (Q ⊗ B.tensorPow e))).inv ≫
        (tensorPullback j).obj (Q ⊗ B.tensorPow e) ◁ (f ≫ t.inv) ≫
        (boundaryPullbackTensorIso j (Q ⊗ B.tensorPow e) B).inv ≫
        (tensorPullback j).map ((α_ Q (B.tensorPow e) B).hom ≫
          Q ◁ ((B.tensorPow e ◁ (ρ_ B).inv) ≫ (B.tensorPowAddIso e 1).inv)) ≫
        (coeffIso j Q B t (e + 1)).hom =
      mulTensorPowSection f ((tensorPullback j).obj Q) e 1 := by
  let := Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hb := beta_eq j
  have hb' := beta_inv_eq j
  simp only [coeffIso, Iso.trans_inv, Iso.trans_hom, tensorIso_inv, tensorIso_hom,
    Iso.refl_inv, Iso.refl_hom, id_tensorHom, Category.assoc, Functor.map_comp, hb, hb']
  erw [rightUnitor_inv_naturality_assoc]
  erw [← whisker_exchange_assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  erw [Functor.LaxMonoidal.associativity_assoc]
  simp only [Functor.Monoidal.μ_δ_assoc, ← whiskerLeft_comp_assoc]
  have hp := pullback_pow_append_iso j B t e
  simp only [Iso.trans_hom, hb'] at hp
  erw [← whiskerLeft_comp]
  simp only [Category.assoc]
  erw [hp]
  erw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_naturality_middle_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  erw [associator_naturality_right_assoc]
  simp only [tensorHom_def, comp_whiskerRight, Category.assoc]
  simp only [← whiskerLeft_comp_assoc, ← whiskerLeft_comp, Category.assoc,
    inv_hom_whiskerRight_assoc]
  rw [mulTensorPowSection, section_one]
  simp only [whiskerLeft_comp, Category.assoc]
  have hcancel : (tensorPullback j).obj Q ◁ N.tensorPow e ◁ t.inv ≫
      (tensorPullback j).obj Q ◁ N.tensorPow e ◁ t.hom = 𝟙 _ := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, Iso.inv_hom_id,
      whiskerLeft_id, whiskerLeft_id]
  erw [reassoc_of% hcancel]
  conv_rhs => erw [associator_naturality_right_assoc]

private theorem section_degree_zero {X Z : Scheme.{u}} (j : Z ⟶ X) (L : X.Modules)
    (n : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n) :
    tensorPowSection f 1 ≫ (boundarySectionDegreeIso j L n 0).inv =
      f ≫ (boundaryPullbackPowIso j L n).inv ≫
        (tensorPullback j).map
          (eqToHom (congrArg L.tensorPow (by omega : n = n * (0 + 1)))) := by
  simp only [boundarySectionDegreeIso, Iso.trans_inv, section_one,
    tensorPowMulIso_one_inv, Nat.reduceAdd, Category.assoc, Iso.inv_hom_id_assoc]
  erw [← eqToHom_iso_inv_naturality (fun k ↦ boundaryPullbackPowIso j L k)
    (Nat.mul_one n).symm]
  rw [eqToHom_map]

private theorem raw_cast {X Z : Scheme.{u}} (j : Z ⟶ X) (L : X.Modules)
    (a a' d t : ℕ) (q : a = a') (h : d + a = t) (h' : d + a' = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a')) :
    tensorIdealSectionMultiply j L a d t h
        (s ≫ (tensorPullback j).map (eqToHom (congrArg L.tensorPow q.symm))) =
      tensorIdealSectionMultiply j L a' d t h' s := by
  subst a'
  simp only [eqToHom_refl]
  rw [(tensorPullback j).map_id (L.tensorPow a), Category.comp_id]

/-- Coefficient-degree coordinates turn raw ideal multiplication into multiplication
by f on the last tensor-power factor. This is solely a monoidal comparison on Z:
no graded algebra, ideal action, kernel, pushforward, or cohomology map occurs.
Source: Stacks Project, Tag 09MS, tensor powers; Tag 01CD, tensor pullback.
(blueprint: lem-sc-tensor-ideal-section-coefficient-comparison).
Proof: Substitute the canonical comparisons for D using hD. Expand the
section-degree comparison as boundaryPullbackPowIso followed by tensorPowMulIso,
and the coefficient-degree comparison as its three explicit factors. Naturality
of boundaryPullbackTensorIso moves the section through the pullback tensorator.
The definition tensorPowSection f 1 is f followed by the inverse right unitor;
its extra unit factor cancels the degree-one tensorPowMulIso. The inverse
coefficient comparison then groups the ideal factor and the first n factors,
followed by e blocks of n factors. Raw multiplication appends one further block
of n factors. This is exactly mulTensorPowSection f F e 1. To check the grouping
identity, induct on e and on n in boundaryPullbackPowIso and tensorPowMulIso;
the successor steps use tensorator naturality and the associator pentagon, and
the zero steps use the unit comparison and the triangle identity. Naturality
of the associators leaves the ideal factor unchanged, so it need not be
invertible. The arithmetic equality h identifies the two output degrees and
proof irrelevance makes the result independent of its proof. In particular n=0
and e=0 use the same unit and associativity identities, without a positivity
assumption. -/
theorem tensorIdealSectionMultiply_coefficient_comparison {X Z : Scheme.{u}}
    (j : Z ⟶ X) [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (hI : j.ker ^ 2 = ⊥) (n : ℕ) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D) (e : ℕ)
    (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (h : n * (e + 1) + n * (0 + 1) = n * ((e + 1) + 1)) :
    tensorIdealSectionMultiply j L (n * (0 + 1)) (n * (e + 1))
        (n * ((e + 1) + 1)) h (tensorPowSection f 1 ≫ (D.a 0).inv) =
      (boundaryCoefficientDegreeIso j L n e).hom ≫
        mulTensorPowSection f ((tensorPullback j).obj
          (j.ker.toModules ⊗ L.tensorPow n)) e 1 ≫
        (boundaryCoefficientDegreeIso j L n (e + 1)).inv := by
  subst D
  simp only [canonicalTensorBoundaryComparisons]
  rw [section_degree_zero]
  have hn : n * (0 + 1) = n := by omega
  have h' : n * (e + 1) + n = n * ((e + 1) + 1) := by omega
  have hr := raw_cast j L (n * (0 + 1)) n (n * (e + 1))
    (n * ((e + 1) + 1)) hn h h' (f ≫ (boundaryPullbackPowIso j L n).inv)
  simp only [Category.assoc] at hr
  rw [hr]
  rw [← cancel_epi (boundaryCoefficientDegreeIso j L n e).inv,
    ← cancel_mono (boundaryCoefficientDegreeIso j L n (e + 1)).hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  let := Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hc (k : ℕ) : boundaryCoefficientDegreeIso j L n k =
      (tensorPullback j).mapIso (blockIso j.ker.toModules L n k) ≪≫
        coeffIso j (j.ker.toModules ⊗ L.tensorPow n) (L.tensorPow n)
          (boundaryPullbackPowIso j L n) k := by
    unfold boundaryCoefficientDegreeIso coeffIso blockIso
    apply Iso.ext
    simp only [Iso.trans_hom]
  simp only [hc, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, tensorIdealSectionMultiply, Category.assoc]
  erw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
  simp only [beta_inv_eq]
  erw [Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [← Functor.map_comp_assoc, Category.assoc]
  erw [block_append j.ker.toModules L n e h']
  simp only [← beta_inv_eq]
  exact coefficient_append j (j.ker.toModules ⊗ L.tensorPow n) (L.tensorPow n)
    (boundaryPullbackPowIso j L n) f e

end
end AlgebraicGeometry.Scheme.Modules
