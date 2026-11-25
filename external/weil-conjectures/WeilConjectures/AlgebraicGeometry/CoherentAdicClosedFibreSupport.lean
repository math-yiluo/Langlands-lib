/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.RingTheory.Nakayama

/-! # Coherent support on an adic closed fibre

Source: Stacks Project, Theorem 088E, displayed support equation after projective existence.
(blueprint: new-coherent-adic-closed-fibre-support)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem stalkIdeal_le_maximal {X : Scheme.{u}} (K : X.IdealSheafData)
    (x : X) (hx : x ∈ K.support)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hxU : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hxU r) = X.presheaf.germ U x hxU r) :
    (LinearMap.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
      K.toModulesι ≫ e.hom).hom : Ideal (X.presheaf.stalk x)) ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  intro r hr
  obtain ⟨m, rfl⟩ := hr
  obtain ⟨V, hxV, m, rfl⟩ := K.toModules.presheaf.exists_germ_eq m
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  rw [← K.toModules.presheaf.germ_res_apply (homOfLE hUV) x hxU m]
  change e.hom ((RingedSpace.stalkAddMap X.toRingedSpace x K.toModulesι) _) ∈ _
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [he]
  rw [IsLocalRing.mem_maximalIdeal]
  have hzero := (X.mem_zeroLocus_iff (K.ideal ⟨U, hU⟩ : Set Γ(X, U)) x).mp
    ((K.mem_support_iff_of_mem hxU).mp hx)
  apply fun hu ↦ hzero _ ?_ ((X.toRingedSpace.mem_basicOpen _ x hxU).mpr hu)
  rw [← K.range_toModulesι_app ⟨U, hU⟩]
  exact Set.mem_range_self _

set_option backward.isDefEq.respectTransparency false in
private theorem support_inter_ideal_subset_quotient {X : Scheme.{u}} [IsNoetherian X]
    (K : X.IdealSheafData) (F : CoherentModules X) :
    {x : X | ¬ Subsingleton (F.obj.presheaf.stalk x)} ∩ (K.support : Set X) ⊆
      {x : X | ¬ Subsingleton ((formalModuleQuotient K 1 F.obj).presheaf.stalk x)} := by
  intro x hx hquot
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have hcoh := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X F.obj).mp F.property
  let _ := hcoh.1
  let _ := hcoh.2
  let _ : Module.Finite (X.presheaf.stalk x) (S.obj F.obj) :=
    Scheme.Modules.finite_stalk_from_affine F.obj x
  obtain ⟨e, he, _, _, _, ⟨φ, _⟩, _⟩ :=
    Scheme.ideal_module_product_stalk K.toModulesι F.obj x
  let L : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map K.toModulesι ≫ e.hom).hom
  have hL : L ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact stalkIdeal_le_maximal K x hx.2 e he
  let _ : Subsingleton (S.obj (cokernel (Scheme.idealModuleProductι K.toModulesι F.obj))) :=
    hquot
  have hquot' : Subsingleton
      (S.obj F.obj ⧸ L • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F.obj))) :=
    φ.toEquiv.injective.subsingleton
  have htop : L • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F.obj)) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hquot'
  have hz : (⊤ : Submodule (X.presheaf.stalk x) (S.obj F.obj)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot L ⊤ Module.Finite.fg_top
      htop.ge hL
  apply hx.1
  change Subsingleton (S.obj F.obj)
  refine ⟨fun a b ↦ ?_⟩
  have ha : a = 0 := by
    have h : a ∈ (⊤ : Submodule (X.presheaf.stalk x) (S.obj F.obj)) := trivial
    rw [hz] at h
    exact h
  have hb : b = 0 := by
    have h : b ∈ (⊤ : Submodule (X.presheaf.stalk x) (S.obj F.obj)) := trivial
    rw [hz] at h
    exact h
  exact ha.trans hb.symm

/-- On the closed fibre, support is detected by the first ideal quotient.
Source: Stacks Project, Theorem 088E, displayed support equation, and Algebra, Tag 00DV.
(blueprint: new-coherent-adic-closed-fibre-support)

Proof: Write K = I O_X. The stalk of the first quotient is F_x/K_x F_x by exactness
of stalks and the ideal-product stalk formula. If p(x) lies in V(I), K_x is contained
in the maximal ideal of the local ring O_{X,x}. The coherent stalk F_x is finite,
so Nakayama implies that a zero quotient forces F_x = 0. Conversely, a quotient of
a zero stalk is zero. Off p inverse V(I), some element of I is a unit at x, so
K_x = O_{X,x} and the quotient is zero. These observations give the set equality.
No completeness or properness is required. For I = 0 it is the identity; for I = 1
both sides are empty; the zero module and empty scheme give empty supports. -/
theorem coherent_adic_closed_fibre_support
    (A : Type u) [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Spec (.of A))
    (F : CoherentModules X) :
    {x : X | ¬ Subsingleton (F.obj.presheaf.stalk x)} ∩
        p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆
      {x : X | ¬ Subsingleton ((formalModuleQuotient
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap p)
        1 F.obj).presheaf.stalk x)} := by
  let K := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap p
  have hK : (K.support : Set X) = p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    dsimp only [K]
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
    congr 2
    rw [← Ideal.coe_comap]
    congr 1
    exact I.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)
  rw [← hK]
  exact support_inter_ideal_subset_quotient K F

end AlgebraicGeometry
