/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.AnnihilatorAffineBasicOpen

/-! # Scheme-theoretic support

Source: Stacks Project, Morphisms, Lemma 05JU and Definition 05JV
(blueprint: lem-weil-pbc-scheme-theoretic-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private theorem kernel_restrict
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U V : X.Opens) (h : V ≤ U)
    (a : Γ(X, U)) (ha : a ∈ RingHom.ker (i.app U).hom) :
    X.presheaf.map (homOfLE h).op a ∈ RingHom.ker (i.app V).hom := by
  rw [RingHom.mem_ker] at ha ⊢
  have hn := congrArg (fun f ↦ f a) (i.naturality (homOfLE h).op)
  change (i.app V).hom (X.presheaf.map (homOfLE h).op a) =
    Z.presheaf.map ((Opens.map i.base).map (homOfLE h)).op ((i.app U).hom a) at hn
  rw [ha, map_zero] at hn
  exact hn

private theorem kernel_of_affine_restrictions
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) (a : Γ(X, U))
    (ha : ∀ (V : X.affineOpens) (h : V.1 ≤ U),
      X.presheaf.map (homOfLE h).op a ∈ RingHom.ker (i.app V.1).hom) :
    a ∈ RingHom.ker (i.app U).hom := by
  rw [RingHom.mem_ker]
  apply Z.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hVU : V ≤ U := hVU
  have hp : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U := (Opens.map i.base).map (homOfLE hVU) |>.le
  refine ⟨i ⁻¹ᵁ V, hp, hxV, ?_⟩
  rw [map_zero]
  have hn := congrArg (fun f ↦ f a) (i.naturality (homOfLE hVU).op)
  change (i.app V).hom (X.presheaf.map (homOfLE hVU).op a) =
    Z.presheaf.map (homOfLE hp).op ((i.app U).hom a) at hn
  rw [← hn]
  exact RingHom.mem_ker.mp (ha ⟨V, hV⟩ hVU)

private theorem annihilator_kernel_iff
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens,
      I.ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1))
    (U : X.Opens) (a : Γ(X, U)) :
    a ∈ RingHom.ker (I.subschemeι.app U).hom ↔
      ∀ (V : X.Opens) (h : V ≤ U) (s : Γ(F, V)),
        X.presheaf.map (homOfLE h).op a • s = 0 := by
  constructor
  · intro ha V h s
    apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
    intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    have hWV : W ≤ V := hWV
    refine ⟨W, hWV, hxW, ?_⟩
    have hk := kernel_restrict I.subschemeι U W (hWV.trans h) a ha
    rw [I.ker_subschemeι_app ⟨W, hW⟩, hI] at hk
    change F.val.map (homOfLE hWV).op (_ • s) = F.val.map (homOfLE hWV).op 0
    rw [map_zero, F.val.map_smul]
    change X.presheaf.map (homOfLE hWV).op
      (X.presheaf.map (homOfLE h).op a) • F.presheaf.map (homOfLE hWV).op s = 0
    have hr : X.presheaf.map (homOfLE hWV).op
        (X.presheaf.map (homOfLE h).op a) =
        X.presheaf.map (homOfLE (hWV.trans h)).op a := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hr]
    exact Module.mem_annihilator.mp hk _
  · intro ha
    apply kernel_of_affine_restrictions I.subschemeι U a
    intro V h
    rw [I.ker_subschemeι_app V, hI]
    exact Module.mem_annihilator.mpr (ha V.1 h)

/-- The annihilator ideal sheaf cuts out the scheme-theoretic support of a finite type
quasi-coherent module. Its sections on an arbitrary open are the kernel of the closed
immersion's map on sections; the displayed equivalence identifies these with the rule
of annihilating every section on every smaller open.
Source: Stacks Project, Morphisms, Lemma 05JU and Definition 05JV, with Lemma 01QQ
(blueprint: lem-weil-pbc-scheme-theoretic-support).

Proof (the node's seven steps):
1. The rule on arbitrary opens is an ideal, stable under restriction, and membership is
   local by the sheaf property (situation-conventions); hence it is an ideal sheaf.
2. On an affine open it equals the annihilator of sections: use the principal-open basis
   (lem-weil-pbc-affine-open-spec-points, def-weil-affine-spectrum,
   lem-weil-pbc-affine-ideals-closed-subscheme) and the quasi-coherent section base-change
   formula (lem-weil-pbc-quasi-coherent-affine-section-base-change), then sheaf locality.
3. Finite type makes the affine section module finite
   (lem-weil-pbc-quasi-coherent-finite-type-affine). The annihilator localizes
   (def-weil-pbc-module-localization-away),
   so the affine ideals satisfy basic-open compatibility.
4. The compatible ideals cut out a closed subscheme with the stated quotient charts
   (lem-weil-pbc-affine-ideals-closed-subscheme, def-weil-closed-immersion,
   def-sbc-closed-immersion-ideal-sheaf).
5. Its kernel ideal sheaf equals the annihilator sheaf on affine opens, hence on every
   open by sheaf locality. It is therefore quasi-coherent (def-pc-scheme,
   def-sbc-closed-immersion-ideal-sheaf).
6. The image equals the nonzero-stalk locus on affine opens by the finite-module support
   formula (lem-weil-pbc-finite-type-module-support-closed,
   lem-weil-pbc-affine-open-spec-points, def-weil-pbc-closed-subset-proper-over-base),
   hence globally because affine opens cover (def-pc-scheme).
7. Taking the smaller open equal to the given open proves annihilation. Any closed
   immersion's ideal sheaf annihilating F is contained in this sheaf, since its sections
   restrict to sections of that ideal on every smaller open
   (def-sbc-closed-immersion-ideal-sheaf). -/
theorem schemeTheoreticSupport
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (I : X.IdealSheafData),
      (∀ (U : X.affineOpens),
        I.ideal U = Module.annihilator (X.presheaf.obj (Opposite.op U.1))
          (F.presheaf.obj (Opposite.op U.1))) ∧
      IsClosedImmersion I.subschemeι ∧
      I.subschemeι.ker = I ∧
      (∀ (U : X.Opens) (a : X.presheaf.obj (Opposite.op U)),
        a ∈ RingHom.ker (I.subschemeι.app U).hom ↔
          ∀ (V : X.Opens) (h : V ≤ U) (s : F.presheaf.obj (Opposite.op V)),
            X.presheaf.map (homOfLE h).op a • s = 0) ∧
      (∀ (U : X.affineOpens),
        IsPullback (I.subschemeCover.f U)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
          I.subschemeι U.2.fromSpec) ∧
      Set.range I.subschemeι = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ (V : X.Opens) (a : RingHom.ker (I.subschemeι.app V).hom)
        (s : F.presheaf.obj (Opposite.op V)), a • s = 0) ∧
      (∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X), IsClosedImmersion i' →
        (∀ (V : X.Opens) (a : RingHom.ker (i'.app V).hom)
          (s : F.presheaf.obj (Opposite.op V)), a • s = 0) →
        ∀ (U : X.Opens),
          RingHom.ker (i'.app U).hom ≤ RingHom.ker (I.subschemeι.app U).hom) := by
  let I : X.IdealSheafData :=
    { ideal := fun U ↦ Module.annihilator Γ(X, U.1) Γ(F, U.1)
      map_ideal_basicOpen := Modules.annihilator_affine_basicOpen X F }
  have hI (U : X.affineOpens) :
      I.ideal U = Module.annihilator Γ(X, U.1) Γ(F, U.1) := rfl
  have hker := annihilator_kernel_iff X F I hI
  refine ⟨I, hI, inferInstance, I.ker_subschemeι, hker, ?_, ?_, ?_, ?_⟩
  · intro U
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback
    · exact (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
    · rw [IsAffineOpen.opensRange_fromSpec, I.opensRange_subschemeCover_map]
  · rw [I.range_subschemeι]
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hloc := (Modules.finite_type_module_support_closed X F).2.2.1 ⟨U, hU⟩
    rw [hU.fromSpec_image_zeroLocus] at hloc
    have hs := I.coe_support_inter ⟨U, hU⟩
    rw [hI] at hs
    have he := hs.trans hloc.symm
    have hx := congrArg (fun S : Set X ↦ x ∈ S) he
    simpa only [Set.mem_inter_iff, hxU, and_true, Set.mem_ofPred_eq] using hx.to_iff
  · intro V a s
    have ha := (hker V a.1).mp a.2 V le_rfl s
    change a.1 • s = 0
    simpa using ha
  · intro Z' i' _ hkill U a ha
    apply (hker U a).mpr
    intro V h s
    exact hkill V ⟨X.presheaf.map (homOfLE h).op a,
      kernel_restrict i' U V h a ha⟩ s

end AlgebraicGeometry.Scheme
