/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryMaps
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteRootNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra

/-! # Constructing the normalized coefficient and root frame -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] diagonalFiniteToPadic
  SpTowerClasses.lineModule cartierProRootMap

/-- Construct normalized finite coordinates from a normalized root coordinate.
Source: blueprint latest, diagonal trace proof (2), finite coefficient and root
identifications (blueprint: lem-sfb-diagonal-trace-supported-finite-frame-construction).

Proof: compose coefficientForget with the canonical constant finite-ring additive
comparison. Lift its inverse to a Z_l-linear map by the finite-exponent scalar
identity, and reflect invertibility through scalar forgetting. The constant-sheaf
unit comparison and coefficient_one prove that the coefficient coordinate preserves
one. The same explicit comparison also preserves one measured through
coefficientForget, independently of the source object's presentation.
The line coordinate is e_n inverse followed by t. Forgetting this composite,
the relation he cancels e_n against roots, and ht identifies the remaining t with
the prescribed root map. These constructions apply also at n=0 and on the empty
scheme. -/
theorem diagonalTrace_supportedFiniteBoundary_frame
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (he : Functor.whiskerRight e.hom (diagonalForget l (diagonalSurface Y)) =
      roots.hom ≫ k.lineForget.inv) (n : ℕ)
    (t : H.obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    (ht : FiniteRootNormalization l Y hY H roots n t) :
    ∃ a : SupportedFiniteBoundaryFrame l Y hY c r k n,
      a.line = e.symm.app (op n) ≪≫ t ∧
      ∀ (U : (diagonalSurface Y).ProEtᵒᵖ)
        (x : ((r.F.obj (SpTowerClasses.coefficient (diagonalSurface Y)
          (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))).obj
            (op n)).obj.obj U),
        (k.coefficientForget.hom.app (op n)).hom.app U x =
          (1 : (Scheme.purTwistFiniteRing (diagonalSurface Y) l n).obj.obj U) →
        HEq (a.coefficient.hom.hom.app U x)
          ((toSheafify (Scheme.ProEt.topology (diagonalSurface Y))
            ((Functor.const (diagonalSurface Y).ProEtᵒᵖ).obj
              (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).app U
                (1 : diagonalResidue.{u} l n)) := by
  have he' := NatTrans.congr_app he (op n)
  have her : (diagonalForget l (diagonalSurface Y)).map (e.inv.app (op n)) ≫
      roots.hom.app (op n) = k.lineForget.hom.app (op n) := by
    have hforward :
        (diagonalForget l (diagonalSurface Y)).map (e.hom.app (op n)) ≫
          k.lineForget.hom.app (op n) = roots.hom.app (op n) := by
      rw [show (diagonalForget l (diagonalSurface Y)).map (e.hom.app (op n)) =
        roots.hom.app (op n) ≫ k.lineForget.inv.app (op n) from he']
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← hforward, ← Functor.map_comp_assoc, e.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  let a : SupportedFiniteBoundaryFrame l Y hY c r k n :=
    { coefficient := finiteCoefficientIso l (diagonalSurface Y) c r k n
      line := e.symm.app (op n) ≪≫ t
      coefficient_one := finiteCoefficientIso_one l (diagonalSurface Y) c r k n
      line_roots := by
        dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
        rw [Functor.map_comp]
        have ht' := ht
        unfold FiniteRootNormalization at ht'
        have her' := her
        unfold diagonalForget at her'
        unfold diagonalForget diagonalFiniteToPadic at ht' ⊢
        rw [eq_of_heq ht', ← Category.assoc, her'] }
  exact ⟨a, rfl, finiteCoefficientIso_one_of_forget l (diagonalSurface Y) c r k n⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
