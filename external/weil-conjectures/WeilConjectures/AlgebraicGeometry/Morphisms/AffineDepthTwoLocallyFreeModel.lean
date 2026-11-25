/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineLocallyFreeModelCore
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDepthTwoBoundaryProperty
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDoubleDualRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # A coherent depth-two model of a finite locally free module on an affine open

## References

* Stacks Project, Tags 0G41(2), 0EY6 proof of (1), and the kernel calculation for double duals
  underlying Tags 0EBI and 0EBJ
* Stacks Project, Tag 0G41(2), Tag 0EY6 proof of (1), steps 2--3
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Construct a coherent depth-two module before making any Hartogs comparison. -/
theorem exists_affine_depth_two_locally_free_model
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (hboundary : ∀ x : Spec A, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x))
    (P : W.toScheme.Modules) [P.IsFiniteLocallyFree] :
    ∃ H : (Spec A).Modules,
      H.IsQuasicoherent ∧
      (∀ V : (Spec A).Opens, IsAffineOpen V →
        Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V))) ∧
      (∀ x : Spec A, x ∉ W →
        ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Spec A).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x)) ∧
      Nonempty (Modules.restrict H W.ι ≅ P) := by
  obtain ⟨H₀, hHqc, hHfin, ⟨e₀⟩⟩ :=
    exists_affine_locally_free_model_core A W P
  have : H₀.IsQuasicoherent := hHqc
  have : Module.Finite Γ(Spec A, ⊤) Γ(H₀, ⊤) :=
    hHfin ⊤ (isAffineOpen_top (Spec A))
  let M := (moduleSpecΓFunctor (R := A)).obj H₀
  have : Module.Finite A M := Modules.finite_sections_top_of_finite H₀
  let D := ModuleCat.of A (Module.Dual A (Module.Dual A M))
  have : Module.Finite A D := inferInstance
  let H := tilde D
  have hqc : H.IsQuasicoherent := inferInstance
  have : Module.Finite A Γ(H, ⊤) :=
    Module.Finite.equiv (tilde.isoTop D).toLinearEquiv
  have : H.IsFinitePresentation := Modules.isFinitePresentation_of_finite H
  have hfin (V : (Spec A).Opens) (hV : IsAffineOpen V) :
      Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V)) :=
    Modules.finite_sections_of_isFinitePresentation H hV
  have : IsIso H₀.fromTildeΓ := Modules.isIso_fromTildeΓ_of_isQuasicoherent H₀
  let e : Modules.restrict (tilde M) W.ι ≅ P :=
    (Modules.restrictFunctor W.ι).mapIso (asIso H₀.fromTildeΓ) ≪≫ e₀
  have hres : Nonempty (Modules.restrict H W.ι ≅ P) :=
    affine_double_dual_restriction A W M P e
  refine ⟨H, hqc, hfin, ?_, hres⟩
  exact affine_depth_two_boundary_property A W hboundary M

end AlgebraicGeometry.Scheme
