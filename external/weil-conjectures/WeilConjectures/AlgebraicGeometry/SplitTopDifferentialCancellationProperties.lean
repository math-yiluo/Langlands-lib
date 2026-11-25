/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Sheaf properties preserved by a retraction

Source: Stacks Project, Tags 01PC and 00NX; affine direct summands.
(blueprint: lem-pc-split-top-differential-cancellation-properties)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Retracts preserve the three termwise properties used in split cancellation.

Source: Stacks Project, Tags 01PC and 00NX; affine direct summands.
(blueprint: lem-pc-split-top-differential-cancellation-properties).

Proof: Let i:M→N and r:N→M be the supplied retraction, so i ≫ r = id.
Quasi-coherence of M follows by identifying it with the kernel of id_N - r ≫ i,
whose source and target are quasi-coherent. On every affine open U the section
maps make Γ(M,U) a retract of Γ(N,U). The affine finite-presentation criterion
makes Γ(N,U) finitely presented. Flatness over the identity, evaluated at U=V,
makes it flat over Γ(S,U), hence finite projective. Its retract is finite
projective and therefore finitely presented; the affine criterion gives finite
presentation of M. For arbitrary affine U⊆V, restrict scalars along Γ(S,V)→Γ(S,U).
The section retraction is still linear and still splits, so flatness of Γ(N,U)
over Γ(S,V) implies that of Γ(M,U) by Module.Flat.of_retract. This is exactly
IsFlatOver (id S). The zero sheaf and the empty scheme cause no exception. -/
theorem split_top_differential_cancellation_properties
    (S : Scheme.{u}) (M N : S.Modules) (h : Retract M N)
    (hflat : N.IsFlatOver (𝟙 S)) (hqc : N.IsQuasicoherent)
    (hfp : N.IsFinitePresentation) :
    M.IsFlatOver (𝟙 S) ∧ M.IsQuasicoherent ∧ M.IsFinitePresentation  := by
  classical
  let := hqc
  let := hfp
  let f : N ⟶ N := 𝟙 N - h.r ≫ h.i
  have hi : h.i ≫ f = 0 := by
    simp [f, Preadditive.comp_sub, ← Category.assoc, h.retract]
  let e : M ≅ kernel f :=
    { hom := kernel.lift f h.i hi
      inv := kernel.ι f ≫ h.r
      hom_inv_id := by simp [← Category.assoc, h.retract]
      inv_hom_id := by
        apply (cancel_mono (kernel.ι f)).1
        simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
        have hf := kernel.condition f
        dsimp [f] at hf
        have he : kernel.ι f = kernel.ι f ≫ h.r ≫ h.i := by
          apply sub_eq_zero.mp
          simpa only [Preadditive.comp_sub, Category.comp_id, Category.assoc] using hf
        exact he.symm }
  have : (kernel f).IsQuasicoherent := isQuasicoherent_kernel f
  have hMqc : M.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso e.symm inferInstance
  have hMflat : M.IsFlatOver (𝟙 S) := by
    intro V U hu
    let : Module Γ(S, V.1) Γ(N, U.1) := Module.compHom _ ((𝟙 S : S ⟶ S).appLE V.1 U.1 hu).hom
    have : Module.Flat Γ(S, V.1) Γ(N, U.1) := hflat V U hu
    let : Module Γ(S, V.1) Γ(M, U.1) :=
      Module.compHom _ ((𝟙 S : S ⟶ S).appLE V.1 U.1 hu).hom
    let F := SheafOfModules.evaluation (R := S.ringCatSheaf) (Opposite.op U.1) ⋙
      ModuleCat.restrictScalars ((𝟙 S : S ⟶ S).appLE V.1 U.1 hu).hom
    have : Module.Flat Γ(S, V.1) (F.obj N) := hflat V U hu
    let r := h.map F
    apply Module.Flat.of_retract
      ((F.map h.i).hom : Γ(M, U.1) →ₗ[Γ(S, V.1)] Γ(N, U.1))
      ((F.map h.r).hom : Γ(N, U.1) →ₗ[Γ(S, V.1)] Γ(M, U.1))
    exact congrArg ModuleCat.Hom.hom r.retract
  have hMfp : M.IsFinitePresentation := by
    have hsections (U : S.affineOpens) :
        Module.FinitePresentation Γ(S, U.1) Γ(M, U.1) := by
      have := (quasicoherent_finite_type_affine.{u, u} S).2 N hqc |>.2.2 hfp U.1 U.2
      have hNflat := hflat U U (by simp)
      have hid : (𝟙 S : S ⟶ S).appLE U.1 U.1 (by simp) = 𝟙 Γ(S, U.1) := by
        simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, homOfLE_refl,
          op_id, Category.id_comp]
        exact S.presheaf.map_id _
      have : Module.Flat Γ(S, U.1) Γ(N, U.1) := by
        change @Module.Flat Γ(S, U.1) Γ(N, U.1) _ _
          (Module.compHom Γ(N, U.1) ((𝟙 S : S ⟶ S).appLE U.1 U.1 (by simp)).hom)
          at hNflat
        rw [hid] at hNflat
        exact hNflat
      have : Module.Projective Γ(S, U.1) Γ(N, U.1) :=
        Module.Flat.projective_of_finitePresentation
      let i : Γ(M, U.1) →ₗ[Γ(S, U.1)] Γ(N, U.1) :=
        (h.i.val.app (Opposite.op U.1)).hom
      let r : Γ(N, U.1) →ₗ[Γ(S, U.1)] Γ(M, U.1) :=
        (h.r.val.app (Opposite.op U.1)).hom
      have hr : r.comp i = LinearMap.id := by
        ext x
        exact congrArg (fun k : M ⟶ M ↦ k.val.app (Opposite.op U.1) x) h.retract
      have : Module.Projective Γ(S, U.1) Γ(M, U.1) := Module.Projective.of_split i r hr
      have : Module.Finite Γ(S, U.1) Γ(M, U.1) :=
        Module.Finite.of_surjective r (fun x ↦ ⟨i x, DFunLike.congr_fun hr x⟩)
      exact Module.finitePresentation_of_projective _ _
    have (U : S.affineOpens) : (M.over U.1).IsFinitePresentation :=
      ((quasicoherent_finite_type_affine.{u, u} S).2 M hMqc |>.1 U.1 U.2).2.mpr (hsections U)
    exact SheafOfModules.IsFinitePresentation.of_coversTop M (fun U : S.affineOpens ↦ U.1)
      ((Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top S))
  exact ⟨hMflat, hMqc, hMfp⟩

end AlgebraicGeometry.Scheme.Modules
