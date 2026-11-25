/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients

/-! # The ordinary root cone under its normalized linear isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The normalized root-limit comparison has exactly the coefficient root cone.
Source: diagonal trace proof (1), the root-limit projections.
(blueprint: lem-sfb-diagonal-trace-normalized-root-cone).
Proof: forget the scalar action and postcompose with the root-system isomorphism.
The inverse preserved-limit comparison followed by its n-th projection is the
root-limit projection. The normalization of e cancels the target root isomorphism,
and line_projection gives this same map for the coefficient cone. Faithfulness
of scalar forgetting proves the original equation. -/
theorem diagonalTrace_normalizedRootCone (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (roots : H ⋙ diagonalForget l T ≅
      Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime))
    (t : (diagonalCompletedRestriction l T).obj (Scheme.purTwistZlModule T l) ≅ limit H)
    (ht : HEq ((diagonalForget l T).map t.hom)
      (diagonalRootLimitComparison l T H roots).inv)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (he : Functor.whiskerRight e.hom (diagonalForget l T) =
      roots.hom ≫ k.lineForget.inv) (n : ℕ) :
    t.hom ≫ limit.π H (op n) ≫ e.hom.app (op n) = k.lineProjection.app (op n) := by
  let F := diagonalForget l T
  have : F.Faithful := by
    dsimp only [F, diagonalForget]
    infer_instance
  apply F.map_injective
  apply (cancel_mono (k.lineForget.hom.app (op n))).1
  have he' := congrArg (fun z ↦ z.app (op n)) he
  change F.map (e.hom.app (op n)) = roots.hom.app (op n) ≫
    k.lineForget.inv.app (op n) at he'
  have hk : F.map (k.lineProjection.app (op n)) ≫ k.lineForget.hom.app (op n) =
      limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op n) := by
    ext U x
    exact k.line_projection n U x
  rw [hk, F.map_comp, F.map_comp, he']
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [eq_of_heq ht]
  simp [diagonalRootLimitComparison, F, Category.assoc,
    preservesLimitIso_inv_π_assoc]

end AlgebraicGeometry.ProEtale.DiagonalTrace
