/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # The tilde comparison for the symmetric algebra on an affine open

Source: Stacks Project, Schemes, Lemma 01I7 and Modules, Lemma 01CG.
(blueprint: def-weil-pbc-symmetric-algebra-affine-comparison-map).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

variable {X : Scheme.{u}}

/-- The sheafification unit, viewed as a linear map on sections. -/
noncomputable def sectionLinearMap (F : X.Modules) (U : X.Opensᵒᵖ) :
    sections F U →ₗ[X.presheaf.obj U] (algebra F).toModule.val.obj U where
  toFun := sectionMap F U
  map_add' := map_add _
  map_smul' := by
    intro r a
    change sectionMap F U (r • a) = (algebra F).hom.hom.app U r * sectionMap F U a
    rw [Algebra.smul_def, map_mul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison obtained from the affine tilde-Gamma adjunction.
Source: Stacks Project, Schemes, Lemma 01I7, applied to the sectionwise symmetric algebra
of Modules, Lemma 01CG.
(blueprint: def-weil-pbc-symmetric-algebra-affine-comparison-map). -/
noncomputable def affineComparison (F : X.Modules) {W : X.Opens} (hU : IsAffineOpen W) :
    tilde (R := Γ(X, W))
      (ModuleCat.of Γ(X, W) (sections F (op W))) ⟶
        Scheme.Modules.restrict ((algebra F).toModule : X.Modules)
          hU.fromSpec :=
  ((tilde.adjunction (R := Γ(X, W))).homEquiv
      (ModuleCat.of Γ(X, W) (sections F (op W)))
      (Scheme.Modules.restrict ((algebra F).toModule : X.Modules)
        hU.fromSpec)).symm
    (ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj
      (Scheme.Modules.restrict ((algebra F).toModule : X.Modules)
        hU.fromSpec))
      ((sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).symm.toLinearMap.comp
      (sectionLinearMap F (op W))))

set_option backward.isDefEq.respectTransparency false in
/-- The affine comparison recovers the sheafification unit on global sections. -/
theorem affineComparison_top (F : X.Modules) {W : X.Opens} (hU : IsAffineOpen W)
    (a : sections F (op W)) :
    sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU
      ((affineComparison F hU).app ⊤
        (tilde.toOpen (ModuleCat.of Γ(X, W) (sections F (op W))) ⊤ a)) =
          sectionMap F (op W) a := by
  have h := ((tilde.adjunction (R := Γ(X, W))).homEquiv
      (ModuleCat.of Γ(X, W) (sections F (op W)))
      (Scheme.Modules.restrict ((algebra F).toModule : X.Modules)
        hU.fromSpec)).apply_symm_apply
    (ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj
      (Scheme.Modules.restrict ((algebra F).toModule : X.Modules)
        hU.fromSpec))
      ((sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).symm.toLinearMap.comp
      (sectionLinearMap F (op W))))
  have ha := congrArg (fun f ↦ f a) h
  change (affineComparison F hU).app ⊤
      (tilde.toOpen (ModuleCat.of Γ(X, W) (sections F (op W))) ⊤ a) =
    (sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).symm
    (sectionMap F (op W) a) at ha
  rw [ha]
  exact (sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).apply_symm_apply _

/-- The comparison on every open agrees with restriction of the global section unit. -/
theorem affineComparison_toOpen (F : X.Modules) {W : X.Opens} (hU : IsAffineOpen W)
    (V : (Spec Γ(X, W)).Opens) (a : sections F (op W)) :
    (affineComparison F hU).app V
      (tilde.toOpen (ModuleCat.of Γ(X, W) (sections F (op W))) V a) =
        (Scheme.Modules.restrict ((algebra F).toModule : X.Modules) hU.fromSpec).presheaf.map
          V.leTop.op ((sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).symm
            (sectionMap F (op W) a)) := by
  let A := ModuleCat.of Γ(X, W) (sections F (op W))
  let S := Scheme.Modules.restrict ((algebra F).toModule : X.Modules) hU.fromSpec
  have htop : (affineComparison F hU).app ⊤ (tilde.toOpen A ⊤ a) =
      (sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).symm (sectionMap F (op W) a) := by
    apply (sectionsTopRestrictFromSpecEquiv (algebra F).toModule hU).injective
    rw [LinearEquiv.apply_symm_apply]
    exact affineComparison_top F hU a
  have ht := congrArg (fun k ↦ k a) (tilde.toOpen_res A ⊤ V V.leTop)
  change (tilde A).presheaf.map V.leTop.op (tilde.toOpen A ⊤ a) =
    tilde.toOpen A V a at ht
  have hv := congrArg (fun k ↦ k (tilde.toOpen A ⊤ a))
    (((Scheme.Modules.toPresheaf _).map (affineComparison F hU)).naturality V.leTop.op)
  change (affineComparison F hU).app V
    ((tilde A).presheaf.map V.leTop.op (tilde.toOpen A ⊤ a)) =
      S.presheaf.map V.leTop.op ((affineComparison F hU).app ⊤ (tilde.toOpen A ⊤ a)) at hv
  rw [ht, htop] at hv
  exact hv

end AlgebraicGeometry.SymmetricAlgebraSheaf
