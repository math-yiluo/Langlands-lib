/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.CommRingCat

/-! # Affine sections present a quasi-coherent stalk by a tensor product

Source: Stacks Project, Tags 01IA and 01HV (6), (7).
(blueprint: lem-pc-intrinsic-flat-module-stalk-tensor-presentation)
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a quasi-coherent module is extension of its affine section scalars.
Source: Stacks Project, Tags 01IA and 01HV (6), (7).
(blueprint: lem-pc-intrinsic-flat-module-stalk-tensor-presentation)

Proof: Use the ordinary section action, since the equal-open appLE of the identity
is the identity ring homomorphism. Let S be the complement of the prime of x in
A = O(V), and let f : G(V) -> G_x be the germ map with scalars restricted along
A -> O_x. The affine stalk ring is the localization of A at S, so every s in S
acts invertibly on G_x. For surjectivity, represent a stalk element by a germ on
an open W and shrink to a basic open D(g) inside W. Quasi-coherence extends its
section to V after multiplying by a power of g; since x is in D(g), g is in S.
For equality, shrink equality of two germs to a basic open D(g). The difference
of their restrictions is zero, so the affine basic-open torsion theorem kills
their difference by a power of g. These verify all three IsLocalizedModule axioms.
The germ scalar action gives the required scalar tower. Mathlib's
IsLocalizedModule.isBaseChange and IsBaseChange.equiv now give the O_x-linear
tensor equivalence. This requires no flatness, finite generation or nonzero
assumption. Empty V has no x in V; for the zero module both sides are zero. -/
theorem affine_sections_stalk_tensor_presentation {Y : Scheme.{u}} (G : Y.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G] (V : Y.affineOpens) (x : Y)
    (hx : x ∈ V.1) :
    letI : Module Γ(Y, V.1) Γ(G, V.1) :=
      Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom
    letI : Algebra Γ(Y, V.1) (Y.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x, hx⟩
    Nonempty (TensorProduct Γ(Y, V.1) (Y.presheaf.stalk x) Γ(G, V.1)
      ≃ₗ[Y.presheaf.stalk x]
        (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj G) := by
  have hid : ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom =
      RingHom.id Γ(Y, V.1) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact congrArg CommRingCat.Hom.hom (Y.presheaf.map_id (Opposite.op V.1))
  have hmod : Module.compHom Γ(G, V.1)
      ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom =
      (inferInstance : Module Γ(Y, V.1) Γ(G, V.1)) := by
    rw [hid]
    rfl
  rw [hmod]
  let A := Γ(Y, V.1)
  let S := (V.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : Module (Y.presheaf.stalk x) (G.presheaf.stalk x) :=
    inferInstanceAs (Module (Y.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y)
      (G.val : _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ _ _)).presheaf x))
  let : Algebra A (Y.presheaf.stalk x) := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : Module A (G.presheaf.stalk x) :=
    Module.compHom _ (Y.presheaf.germ V.1 x hx).hom
  let f : Γ(G, V.1) →ₗ[A] G.presheaf.stalk x :=
    { toFun := G.presheaf.germ V.1 x hx
      map_add' := map_add _
      map_smul' := fun r m ↦ PresheafOfModules.germ_smul (R := Y.presheaf) G.val x V.1 hx r m }
  have hprime (g : A) (hxg : x ∈ Y.basicOpen g) : g ∈ S := by
    change V.2.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen g
    rw [← V.2.fromSpec_preimage_basicOpen]
    change V.2.fromSpec (V.2.primeIdealOf ⟨x, hx⟩) ∈ Y.basicOpen g
    rwa [V.2.fromSpec_primeIdealOf]
  have hloc : IsLocalizedModule S f := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      have := V.2.isLocalization_stalk ⟨x, hx⟩
      have hu : IsUnit (Y.presheaf.germ V.1 x hx s.1) :=
        IsLocalization.map_units (Y.presheaf.stalk x) s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun m : G.presheaf.stalk x ↦
        Y.presheaf.germ V.1 x hx s.1 • m)
      exact ⟨(fun a b h ↦ hu.smul_left_cancel.mp h), fun m ↦
        ⟨hu.unit⁻¹ • m, smul_inv_smul hu.unit m⟩⟩
    · intro y
      obtain ⟨W, hxW, m, rfl⟩ := G.presheaf.exists_germ_eq y
      obtain ⟨g, hgV, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hx
      obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen G V.2 g
        (G.presheaf.map (homOfLE hgV).op m)
      refine ⟨⟨t, ⟨g ^ n, S.pow_mem (hprime g hxg) n⟩⟩, ?_⟩
      have h := congrArg (G.presheaf.germ (Y.basicOpen g) x hxg) ht
      erw [PresheafOfModules.germ_smul (R := Y.presheaf) G.val] at h
      rw [_root_.map_pow] at h
      erw [Y.presheaf.germ_res_apply, G.presheaf.germ_res_apply,
        G.presheaf.germ_res_apply] at h
      change Y.presheaf.germ V.1 x hx (g ^ n) • G.presheaf.germ W x hxW m =
        G.presheaf.germ V.1 x hx t
      rw [_root_.map_pow]
      exact h.symm
    · intro m₁ m₂ hm
      obtain ⟨W, hxW, i₁, i₂, heq⟩ := G.presheaf.germ_eq x hx hx m₁ m₂ hm
      obtain ⟨g, hgV, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hx
      have hz : G.presheaf.map (homOfLE (Y.basicOpen_le g)).op (m₁ - m₂) = 0 := by
        have h := congrArg (G.presheaf.map (homOfLE hgV).op) heq
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at h
        rw [map_sub, sub_eq_zero]
        convert h using 1
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen G V.2 g (m₁ - m₂) hz
      refine ⟨⟨g ^ n, S.pow_mem (hprime g hxg) n⟩, ?_⟩
      exact sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hn)
  have := hloc
  have := V.2.isLocalization_stalk ⟨x, hx⟩
  have : IsScalarTower A (Y.presheaf.stalk x) (G.presheaf.stalk x) :=
    .of_algebraMap_smul (fun _ _ ↦ rfl)
  exact
    (Nonempty.intro (IsLocalizedModule.isBaseChange S (Y.presheaf.stalk x) f).equiv)

end AlgebraicGeometry
