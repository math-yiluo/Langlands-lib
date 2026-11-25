/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineComparisonStalks
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine comparison for the symmetric algebra sheaf

## References

* Stacks Project, Schemes, Lemma 01I8 and Modules, Lemma 01CG
* Stacks Project, Modules, Lemmas 01CG, 01CH, 01CL and Schemes, Lemma 01I8
* Algebra, Lemma 0C6F
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

private theorem affineComparison_isIso (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W) :
    IsIso (SymmetricAlgebraSheaf.affineComparison F hW) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  let T := tilde (ModuleCat.of Γ(X, W) (SymmetricAlgebraSheaf.sections F (op W)))
  let S := Scheme.Modules.restrict
    ((SymmetricAlgebraSheaf.algebra F).toModule : X.Modules) hW.fromSpec
  let f : (⟨T.presheaf, T.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat (Spec Γ(X, W))) ⟶
      ⟨S.presheaf, S.isSheaf⟩ :=
    ⟨(Scheme.Modules.toPresheaf _).map (SymmetricAlgebraSheaf.affineComparison F hW)⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f V
    (fun x _ ↦ SymmetricAlgebraSheaf.affineComparison_stalk_bijective F hW x)

/-- The ring sheafification of the sectionwise symmetric algebra is quasi-coherent and its
unit is bijective on affine sections. -/
theorem quasiCoherentSymmetricAlgebra_affine_comparison
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    (SymmetricAlgebraSheaf.algebra F).toModule.IsQuasicoherent ∧
      ∀ U : X.affineOpens,
        Function.Bijective (SymmetricAlgebraSheaf.sectionMap F (op U.1)) := by
  have hIso (U : X.affineOpens) :
      IsIso (SymmetricAlgebraSheaf.affineComparison F (show IsAffineOpen U.1 from U.2)) :=
    affineComparison_isIso X F _
  constructor
  · refine Scheme.Modules.isQuasicoherent_of_iSup_opensRange_eq_top
      (SymmetricAlgebraSheaf.algebra F).toModule
      (fun U : X.affineOpens ↦ (show IsAffineOpen U.1 from U.2).fromSpec)
      Scheme.Modules.iSup_opensRange_fromSpec_eq_top (fun U ↦ ?_)
    exact (presentationTilde (ModuleCat.of Γ(X, U.1) (SymmetricAlgebraSheaf.sections F (op U.1)))
      .univ (by simp) _ (Submodule.span_eq _)).ofIsIso
        (SymmetricAlgebraSheaf.affineComparison F (show IsAffineOpen U.1 from U.2))
  · intro U
    let hU : IsAffineOpen U.1 := U.2
    have : IsIso (SymmetricAlgebraSheaf.affineComparison F hU) := hIso U
    let α := SymmetricAlgebraSheaf.affineComparison F hU
    let e := Scheme.Modules.sectionsTopRestrictFromSpecEquiv
      (SymmetricAlgebraSheaf.algebra F).toModule hU
    let A := ModuleCat.of Γ(X, U.1) (SymmetricAlgebraSheaf.sections F (op U.1))
    have hb := e.bijective.comp
      ((ConcreteCategory.bijective_of_isIso (α.app ⊤)).comp
        (ConcreteCategory.bijective_of_isIso (tilde.toOpen A ⊤)))
    have he : (fun a ↦ e (α.app ⊤ (tilde.toOpen A ⊤ a))) =
        SymmetricAlgebraSheaf.sectionMap F (op U.1) :=
      funext (SymmetricAlgebraSheaf.affineComparison_top F hU)
    exact he ▸ hb

end AlgebraicGeometry
