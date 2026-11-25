/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Inverting the transition on the fibre of a scalar tower

Source: Stacks Project, Tags 0941 and 0A0E.
(blueprint: lem-pbc-scalar-tower-product-fibre).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

private noncomputable def coneContract (P : CochainComplex A ℤ) (d c e h : P ⟶ P)
    (w : d ≫ e = c ≫ d) (h₁ : d ≫ h = 𝟙 P - c) (h₂ : h ≫ d = 𝟙 P - e) :
    Homotopy (𝟙 (CochainComplex.mappingCone d))
      (CochainComplex.mappingCone.map d d c e w) := by
  open CochainComplex CochainComplex.HomComplex in
  refine mappingCone.descHomotopy d _ _ 0
    ((Cochain.ofHom h).comp (mappingCone.inl d) (zero_add _)) ?_ ?_
  · ext p q hpq
    have hp : p = q + 1 := by omega
    subst p
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      HomologicalComplex.id_f, Category.comp_id, δ_zero, zero_add, Cochain.add_v,
      Cochain.zero_cochain_comp_v,
      mappingCone.map, mappingCone.inl_v_desc_f]
    have hh := congrArg (fun f : P ⟶ P ↦ f.f (q + 1)) h₁
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f] at hh
    rw [← Category.assoc, hh, Preadditive.sub_comp, Category.id_comp]
    abel
  · simp only [Category.comp_id, δ_ofHom_comp, mappingCone.δ_inl,
      ← Cochain.ofHom_comp, mappingCone.map, mappingCone.inr_desc]
    rw [← Category.assoc, h₂, Preadditive.sub_comp, Category.id_comp,
      Cochain.ofHom_sub]
    abel

/-- Multiplication by the transition on the Roos fibre of a constant-object scalar
system is a quasi-isomorphism.

Source: Stacks Project, Tags 0941 and 0A0E
(blueprint: lem-pbc-scalar-tower-product-fibre).
Proof: let a be the diagonal scalar on the product and b the index shift. They commute.
The fibre is Cone(-(1-ba))[-1]. Both a and b induce diagonal cone maps. The identity
minus their composite is nullhomotopic, with off-diagonal homotopy minus the identity
of the product. Thus the two induced cone maps are homotopy inverses. Shifting their
homotopy equivalence gives the assertion. No condition on the scalar is needed;
in particular zero and invertible scalars are included. -/
private theorem scalarTowerProductFibre_quasiIso (P : CochainComplex A ℤ) (μ : End P) :
    let V := ∏ᶜ (fun _ : ℕ ↦ P)
    let a : V ⟶ V := Limits.Pi.map (fun _ : ℕ ↦ μ.asHom)
    let b : V ⟶ V := Limits.Pi.lift (fun n : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ P) (n + 1))
    let d := -(𝟙 V - b ≫ a)
    ∃ (w : d ≫ a = a ≫ d),
      QuasiIso ((mappingCone.map d d a a w)⟦(-1 : ℤ)⟧') := by
  let V := ∏ᶜ (fun _ : ℕ ↦ P)
  let a : V ⟶ V := Limits.Pi.map (fun _ : ℕ ↦ μ.asHom)
  let b : V ⟶ V := Limits.Pi.lift (fun n : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ P) (n + 1))
  have hab : a ≫ b = b ≫ a := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [a, b, Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.map_π,
      Limits.Pi.lift_comp_π_assoc]
  let t := b ≫ a
  let d := -(𝟙 V - t)
  have hat : a ≫ t = t ≫ a := by
    dsimp only [t]
    rw [← Category.assoc, hab, Category.assoc]
  have hbt : b ≫ t = t ≫ b := by
    dsimp only [t]
    rw [Category.assoc, hab, ← Category.assoc]
  have wa : d ≫ a = a ≫ d := by
    simp only [d, Preadditive.neg_comp, Preadditive.comp_neg, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, Category.comp_id, hat]
  have wb : d ≫ b = b ≫ d := by
    simp only [d, Preadditive.neg_comp, Preadditive.comp_neg, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, Category.comp_id, hbt]
  have wt : d ≫ t = t ≫ d := by
    simp [d, Preadditive.sub_comp, Preadditive.comp_sub]
  let c := mappingCone.map d d a a wa
  let s := mappingCone.map d d b b wb
  have hcs : c ≫ s = mappingCone.map d d t t wt := by
    dsimp only [c, s]
    rw [← mappingCone.map_comp]
    simp only [hab]
    rfl
  have hsc : s ≫ c = mappingCone.map d d t t wt := by
    dsimp only [c, s]
    rw [← mappingCone.map_comp]
  have h := coneContract V d t t (-𝟙 V) wt
    (by simp [d]) (by simp [d]; abel)
  let e : HomotopyEquiv (mappingCone d) (mappingCone d) :=
    { hom := c
      inv := s
      homotopyHomInvId := (Homotopy.ofEq hcs).trans h.symm
      homotopyInvHomId := (Homotopy.ofEq hsc).trans h.symm }
  have hc : QuasiIso c := e.quasiIso_hom
  exact ⟨wa, (quasiIso_shift_iff c (-1)).2 hc⟩

/-- The scalar acts invertibly on the fibre of its own inverse tower.
Source: Stacks Project, Tags 0941 and 0A0E
(blueprint: lem-pbc-scalar-tower-product-fibre).
Proof: the diagonal scalar on the product is scalar multiplication of the identity.
The induced diagonal cone map is scalar multiplication on the cone, since its two
components have this value. Its shift is scalar multiplication on the fibre. Apply
the product-shift homotopy equivalence proved above. -/
theorem scalarTowerProductFibre_scalar_quasiIso
    {R : Type*} [Ring R] [Linear R A] (P : CochainComplex A ℤ) (r : R) :
    let V := ∏ᶜ (fun _ : ℕ ↦ P)
    let a : V ⟶ V := Limits.Pi.map (fun _ : ℕ ↦ (r • 𝟙 P))
    let b : V ⟶ V := Limits.Pi.lift (fun n : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ P) (n + 1))
    QuasiIso (r • 𝟙 (mappingCocone (-(𝟙 V - b ≫ a)))) := by
  let V := ∏ᶜ (fun _ : ℕ ↦ P)
  let a : V ⟶ V := Limits.Pi.map (fun _ : ℕ ↦ (r • 𝟙 P))
  let b : V ⟶ V := Limits.Pi.lift (fun n : ℕ ↦ Limits.Pi.π (fun _ : ℕ ↦ P) (n + 1))
  let d := -(𝟙 V - b ≫ a)
  have ha : a = r • 𝟙 V := by
    apply Limits.Pi.hom_ext
    intro n
    simp [a, Linear.smul_comp, Linear.comp_smul]
  obtain ⟨w, hw⟩ := scalarTowerProductFibre_quasiIso P (End.of (r • 𝟙 P))
  have he : mappingCone.map d d a a w = r • 𝟙 (mappingCone d) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply mappingCone.ext_from d (j + 1) j rfl
    · simp [mappingCone.map, ha, HomologicalComplex.smul_f_apply,
        Linear.smul_comp, Linear.comp_smul]
    · simp [mappingCone.map, ha, HomologicalComplex.smul_f_apply,
        Linear.smul_comp, Linear.comp_smul]
  rw [he, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id] at hw
  exact hw

end CochainComplex
