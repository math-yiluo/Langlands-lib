/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Detecting vanishing of an ideal-power product on an affine cover

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01Y9, and
Schemes, Lemma 01I8 (blueprint: lem-weil-pbc-ideal-power-product-zero-affine-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem affine_zero_of_sections {X : Scheme.{u}} (H : X.Modules)
    [H.IsQuasicoherent] (U : X.affineOpens) [Subsingleton Γ(H, U.1)] :
    IsZero (H.restrict U.1.ι) := by
  let N := H.restrict U.2.fromSpec
  have : N.IsQuasicoherent := Modules.isQuasicoherent_restrictFunctor _ H
  have hi : U.2.fromSpec ''ᵁ ⊤ = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  have : Subsingleton Γ(N, ⊤) := by
    have : Subsingleton Γ(H, U.2.fromSpec ''ᵁ ⊤) := hi.symm ▸ inferInstance
    exact (H.restrictAppIso U.2.fromSpec ⊤).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  have hz : IsZero N := by
    have : Subsingleton ((moduleSpecΓFunctor (R := Γ(X, U.1))).obj N) :=
      (inferInstance : Subsingleton Γ(N, ⊤))
    have : IsIso N.fromTildeΓ := Modules.isIso_fromTildeΓ_of_isQuasicoherent N
    have hz := (tilde.functor Γ(X, U.1)).map_isZero
      (ModuleCat.isZero_of_subsingleton ((moduleSpecΓFunctor (R := Γ(X, U.1))).obj N))
    exact hz.of_iso (asIso N.fromTildeΓ).symm
  have hsec (V : X.Opens) (hV : V ≤ U.1) : Subsingleton Γ(H, V) := by
    have : Subsingleton Γ(N, U.2.fromSpec ⁻¹ᵁ V) := ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.evaluation _ (Opposite.op (U.2.fromSpec ⁻¹ᵁ V))).map_isZero hz)
    have hv : U.2.fromSpec ''ᵁ (U.2.fromSpec ⁻¹ᵁ V) = V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, U.2.opensRange_fromSpec,
        inf_eq_right.mpr hV]
    have hs : Subsingleton Γ(H, U.2.fromSpec ''ᵁ (U.2.fromSpec ⁻¹ᵁ V)) :=
      (H.restrictAppIso U.2.fromSpec _).addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
    exact hv ▸ hs
  refine (IsZero.iff_id_eq_zero _).mpr (Modules.hom_ext _ _ fun V ↦ ?_)
  have : Subsingleton Γ(H, U.1.ι ''ᵁ V) :=
    hsec _ (by simpa using U.1.ι.image_le_opensRange V)
  have : Subsingleton Γ(H.restrict U.1.ι, V) :=
    (H.restrictAppIso U.1.ι V).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  ext a
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- An ideal-power product of a quasi-coherent module vanishes if and only if the
corresponding powers of ideals of affine sections annihilate the section modules
on an affine open cover. Neither finiteness nor Noetherianity is needed here.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01Y9; Schemes,
Lemma 01I8 (blueprint: lem-weil-pbc-ideal-power-product-zero-affine-cover).

Proof: On each affine open identify the ideal and module with the tilde sheaves
of their sections by the tilde/global-sections adjunction. The tensor comparison
and preservation of images identify the product with the tilde of I^t M; induction
on t identifies the power with I^t. For t = 0 the power inclusion is the identity
of the structure sheaf, and multiplication is the left unitor, so the product is M.
The submodule I^t M is zero exactly when every element of I^t annihilates every
section, equivalently I^t is contained in Ann(M). A quasi-coherent sheaf on an
affine is zero exactly when its section module is zero, by the counit isomorphism
and preservation of zero by tilde. Finally a sheaf zero on an open cover is zero:
restrict any section to its intersections with the covering opens and use the
uniqueness clause of the sheaf axiom. The reverse implication follows by restricting
a zero sheaf. This also covers an empty cover of the empty scheme. -/
theorem idealPowerProduct_isZero_iff_affine_cover (X : Scheme.{u})
    (F : X.Modules) [F.IsQuasicoherent] (K : X.IdealSheafData)
    (S : Set X.affineOpens) (hS : ∀ x : X, ∃ U ∈ S, x ∈ U.1) (t : ℕ) :
    IsZero (idealModuleProduct (idealSheafPower K.toModulesι t).2 F) ↔
      ∀ U ∈ S, K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  let J := (idealSheafPower K.toModulesι t).1
  let ι : J ⟶ SheafOfModules.unit X.ringCatSheaf := (idealSheafPower K.toModulesι t).2
  have hj : J.IsQuasicoherent := by
    cases t with
    | zero =>
      dsimp [J, idealSheafPower]
      exact SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    | succ n => exact (Modules.ideal_times_quasiCoherent_affine_sections K F).2.2.1 _ (by omega)
  let φ : MonoidalCategory.tensorObj J F ⟶ F :=
    MonoidalCategory.whiskerRight ι F ≫ (MonoidalCategory.leftUnitor F).hom
  have ht : (MonoidalCategory.tensorObj J F).IsQuasicoherent :=
    (Modules.quasiCoherent_tensor_product_affine_sections J F).1
  have him := Modules.quasiCoherent_cokernel_image φ
  have hq : (Abelian.image φ).IsQuasicoherent := him.2.2.2.2.2.2.2.1
  have hp (U : X.affineOpens) :
      Set.range (ι.app U.1) = {a | a ∈ K.ideal U ^ t} := by
    cases t with
    | zero =>
      dsimp [ι, J, idealSheafPower]
      simp
    | succ n =>
      exact ((Modules.ideal_times_quasiCoherent_affine_sections K F).2.2.2.1 U).2.2.2 _ (by omega)
  have hm (U : X.Opens) (a : Γ(J, U)) (s : Γ(F, U)) :
      φ.app U (Modules.tmulSection a s) = (show Γ(X, U) from ι.app U a) • s := by
    change (MonoidalCategory.leftUnitor F).hom.app U
      ((MonoidalCategory.whiskerRight ι F).app U (Modules.tmulSection a s)) = _
    rw [Modules.whiskerRight_app_tmulSection, Modules.leftUnitor_hom_app_tmulSection']
    rfl
  change IsZero (image φ) ↔ _
  constructor
  · intro hz U hU a ha
    obtain ⟨b, hb⟩ := (Set.ext_iff.mp (hp U) a).mpr ha
    apply Module.mem_annihilator.mpr
    intro s
    have he : φ = 0 := eq_zero_of_image_eq_zero (hz.eq_of_src _ _)
    have hh := congrArg
      (fun f : MonoidalCategory.tensorObj J F ⟶ F ↦ f.app U.1 (Modules.tmulSection b s)) he
    rw [hm, hb] at hh
    simpa using hh
  · intro h
    have hs (U : S) : Subsingleton Γ(Abelian.image φ, U.1.1) := by
      have hz : ∀ z : Γ(MonoidalCategory.tensorObj J F, U.1.1), φ.app U.1.1 z = 0 := by
        intro z
        obtain ⟨w, rfl⟩ :=
          (Modules.quasiCoherent_tensor_product_affine_sections J F).2 _ U.1.2 |>.2 z
        induction w using TensorProduct.inductionOn with
        | tmul a s =>
          rw [Modules.tensorSectionsMap_tmul, hm]
          exact Module.mem_annihilator.mp (h U.1 U.2
            ((Set.ext_iff.mp (hp U.1) _).mp ⟨a, rfl⟩)) s
        | add a b ha hb => simp only [map_add, ha, hb, add_zero]
      have hinj : Function.Injective ((Abelian.image.ι φ).app U.1.1) := by
        exact (ModuleCat.mono_iff_injective _).mp
          ((SheafOfModules.evaluation _ (Opposite.op U.1.1)).map_mono _)
      refine ⟨fun a b ↦ hinj ?_⟩
      have hr := (him.2.2.2.2.2.2.2.2 U.1).1
      have hh (a : Γ(Abelian.image φ, U.1.1)) :
          (Abelian.image.ι φ).app U.1.1 a = 0 := by
        obtain ⟨z, he⟩ := (Set.ext_iff.mp hr _).mp ⟨a, rfl⟩
        exact he.symm.trans (hz z)
      rw [hh, hh]
    have hc : (⨆ U : S, U.1.1) = ⊤ := by
      apply top_unique
      intro x hx
      obtain ⟨U, hU, hxU⟩ := hS x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
    have hz : IsZero (Abelian.image φ) := Modules.isZero_of_iSup_eq_top _
      (fun U : S ↦ U.1.1) hc (fun U ↦ @affine_zero_of_sections _ _ hq U.1 (hs U))
    exact hz.of_iso (Abelian.imageIsoImage φ).symm

end AlgebraicGeometry.Scheme
