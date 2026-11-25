/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Extending integral sections from a dense open of a normal scheme

## References

* Stacks Project, Tags 0357 and 0AB1, affine integral-closure argument
* Stacks Project, Tags 0357 (normal components) and 0AB1 (integral birational comparison), the
  affine integral-closure argument
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme

private theorem integral_section_extends {X : Scheme.{u}} [IsIntegral X]
    (hnormal : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    {U W : X.Opens} [Nonempty W] (hWU : W ≤ U)
    (s : Γ(X, W))
    (hs : letI := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra;
      _root_.IsIntegral Γ(X, U) s) :
    ∃ t : Γ(X, U), X.presheaf.map (homOfLE hWU).op t = s := by
  have : Nonempty U := by
    obtain ⟨x⟩ := ‹Nonempty W›
    exact ⟨⟨x.1, hWU x.2⟩⟩
  let := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  let φ : Γ(X, W) →ₐ[Γ(X, U)] X.functionField :=
    { (X.germToFunctionField W).hom with
      commutes' := fun a ↦ X.presheaf.germ_res_apply (homOfLE hWU) _ _ a }
  have hg := hs.map φ
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq U (φ s) fun x hx ↦ by
    have := hnormal x
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    have := functionField_isScalarTower X U (⟨x, hx⟩ : U)
    exact (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk x)).mp
      (hg.tower_top (A := X.presheaf.stalk x))
  refine ⟨t, X.germToFunctionField_injective W ?_⟩
  exact (X.presheaf.germ_res_apply (homOfLE hWU) _ _ t).trans ht

private theorem component_isIntegral {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z)) (x : X) :
    let C : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
    IsIntegral C.toScheme ∧
      ∀ z : C.toScheme, IsIntegrallyClosed (C.toScheme.presheaf.stalk z) := by
  dsimp only
  let C : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have : ConnectedSpace C.toScheme := Subtype.connectedSpace isConnected_connectedComponent
  have hdom (z : C.toScheme) : IsDomain (C.toScheme.presheaf.stalk z) := by
    have := (hnormal (C.ι z)).1
    exact MulEquiv.isDomain _
      (asIso (C.ι.stalkMap z)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  have : IrreducibleSpace C.toScheme := irreducibleSpace_of_isDomain_stalk C.toScheme hdom
  have (z : C.toScheme) : _root_.IsReduced (C.toScheme.presheaf.stalk z) := by
    have := hdom z
    infer_instance
  have : IsReduced C.toScheme := isReduced_of_isReduced_stalk C.toScheme
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced C.toScheme, fun z ↦ ?_⟩
  have := (hnormal (C.ι z)).2
  exact IsIntegrallyClosed.of_equiv
    (asIso (C.ι.stalkMap z)).commRingCatIsoToRingEquiv

private theorem integral_section_extends_locally {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    {U W : X.Opens} (hWU : W ≤ U)
    (hW : ∀ T : X.Opens, T ≤ U → Nonempty T → Nonempty (T ⊓ W : X.Opens))
    (s : Γ(X, W))
    (hs : letI := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra;
      _root_.IsIntegral Γ(X, U) s) (x : U) :
    ∃ (T : X.Opens) (_hTU : T ≤ U), x.1 ∈ T ∧ ∃ t : Γ(X, T),
      X.presheaf.map (homOfLE (inf_le_left : T ⊓ W ≤ T)).op t =
        X.presheaf.map (homOfLE (inf_le_right : T ⊓ W ≤ W)).op s := by
  let C : X.Opens := ⟨connectedComponent x.1, isOpen_connectedComponent⟩
  obtain ⟨hC, hnC⟩ := component_isIntegral hnormal x.1
  have : IsIntegral C.toScheme := hC
  let UC := C.ι ⁻¹ᵁ U
  let WC := C.ι ⁻¹ᵁ W
  let T := C.ι ''ᵁ UC
  have hTU : T ≤ U := Set.image_preimage_subset _ _
  have hxT : x.1 ∈ T := ⟨⟨x.1, mem_connectedComponent⟩, x.2, rfl⟩
  have hTW : T ⊓ W = C.ι ''ᵁ WC := by
    simp only [T, UC, WC, Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι]
    rw [inf_assoc, inf_eq_right.mpr hWU]
  have : Nonempty WC := by
    obtain ⟨y⟩ := hW T hTU ⟨⟨x.1, hxT⟩⟩
    have hy : y.1 ∈ C.ι ''ᵁ WC := hTW ▸ y.2
    obtain ⟨z, hz, -⟩ := hy
    exact ⟨⟨z, hz⟩⟩
  let := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  let := (C.toScheme.presheaf.map (homOfLE (C.ι.preimage_mono hWU)).op).hom.toAlgebra
  have hsC : _root_.IsIntegral Γ(C, UC) (C.ι.app W s) := by
    apply hs.map_of_comp_eq (C.ι.app U).hom (C.ι.app W).hom
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (C.ι.naturality (homOfLE hWU).op).symm
  obtain ⟨t, ht⟩ := integral_section_extends hnC (C.ι.preimage_mono hWU) (C.ι.app W s) hsC
  refine ⟨T, hTU, hxT, t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToIso hTW).inv.op)).1
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
  exact ht

/-- A section on a dense open integral over an affine chart extends over that chart. -/
theorem exists_integral_section_denseOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    (V : X.Opens) (hV : Dense (V : Set X))
    (U : X.Opens) (_hU : IsAffineOpen U)
    (s : Γ(V, V.ι ⁻¹ᵁ U))
    (hs : letI := (V.ι.app U).hom.toAlgebra; _root_.IsIntegral Γ(X, U) s) :
    ∃ t : Γ(X, U), V.ι.app U t = s := by
  classical
  have (z : X) : IsDomain (X.presheaf.stalk z) := (hnormal z).1
  have (z : X) : _root_.IsReduced (X.presheaf.stalk z) := inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsDominant V.ι := by
    rw [isDominant_iff, DenseRange, Opens.range_ι]
    exact hV
  have := IsSchemeTheoreticallyDominant.of_isDominant V.ι
  let W := V.ι ''ᵁ (V.ι ⁻¹ᵁ U)
  have hWU : W ≤ U := Set.image_preimage_subset _ _
  let := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have hW (T : X.Opens) (hTU : T ≤ U) (hne : Nonempty T) :
      Nonempty (T ⊓ W : X.Opens) := by
    obtain ⟨y, hyV, hyT⟩ := hV.exists_mem_open T.isOpen (by obtain ⟨z⟩ := hne; exact ⟨z.1, z.2⟩)
    exact ⟨⟨y, hyT, ⟨⟨y, hyV⟩, hTU hyT, rfl⟩⟩⟩
  have hinj (T : X.Opens) (hTU : T ≤ U) : Function.Injective
      (X.presheaf.map (homOfLE (inf_le_left : T ⊓ W ≤ T)).op) := by
    have hTW : T ⊓ W = V.ι ''ᵁ (V.ι ⁻¹ᵁ T) := by
      simp only [W, Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι]
      rw [inf_left_comm, inf_eq_left.mpr hTU]
    intro a b hab
    apply V.ι.app_injective T
    have hh := congrArg (X.presheaf.map (eqToIso hTW).inv.op) hab
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at hh
    exact hh
  have H (x : U) := integral_section_extends_locally hnormal hWU hW s hs x
  choose T hTU hxT t ht using H
  obtain ⟨tU, htU, -⟩ := X.sheaf.existsUnique_gluing' T U (fun x ↦ homOfLE (hTU x))
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxT _⟩) t fun i j ↦ by
      change X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (t i) =
        X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (t j)
      apply hinj (T i ⊓ T j) (inf_le_left.trans (hTU i))
      have hi := congrArg (X.presheaf.map
        (homOfLE (inf_le_inf (inf_le_left : T i ⊓ T j ≤ T i) le_rfl)).op) (ht i)
      have hj := congrArg (X.presheaf.map
        (homOfLE (inf_le_inf (inf_le_right : T i ⊓ T j ≤ T j) le_rfl)).op) (ht j)
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at hi hj ⊢
      exact hi.trans hj.symm
  refine ⟨tU, ?_⟩
  change X.presheaf.map (homOfLE hWU).op tU = s
  apply X.IsSheaf.section_ext
  intro x hxW
  let y : U := ⟨x, hWU hxW⟩
  refine ⟨T y ⊓ W, inf_le_right, ⟨hxT y, hxW⟩, ?_⟩
  have hty := htU y
  change X.presheaf.map (homOfLE (hTU y)).op tU = t y at hty
  have hh := congrArg (X.presheaf.map
    (homOfLE (inf_le_left : T y ⊓ W ≤ T y)).op) hty
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at hh ⊢
  exact hh.trans (ht y)

end AlgebraicGeometry.Scheme
