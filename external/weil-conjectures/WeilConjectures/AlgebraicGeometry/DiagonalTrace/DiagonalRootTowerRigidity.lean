/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRlimForgetUnit
import WeilConjectures.AlgebraicGeometry.DiagonalFiniteRootRigidity
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso

/-! # Detection of ordinary root-tower maps on the diagonal -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- Pullback to the diagonal detects maps between ordinary p-adic root towers.
Source: diagonal coefficient changes (3), connected-fibre root-map rigidity.
(blueprint: lem-diagonal-root-tower-rigidity).

Proof: at each level forget the p-adic action and conjugate the two maps by
the prescribed identifications with the ordinary roots sheaf. The canonical
forgetting/inverse-image comparison carries equality after module inverse
image to equality after abelian inverse image. Restriction to the diagonal
detects the resulting root maps. Cancel the root identifications, use
faithfulness of forgetting scalars, and apply natural-transformation
extensionality. This argument concerns ordinary maps, not arbitrary derived
morphisms of systems. -/
private theorem diagonalRootTower_restriction_injective (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    (H K : DiagonalSystems l (diagonalSurface Y))
    (rH : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (rK : K ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime)) :
    Function.Injective (fun f : H ⟶ K ↦ Functor.whiskerRight f
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (diagonalImmersion Y))) := by
  let W := diagonalSurface Y
  let P := ProjectiveLine Y
  let d := diagonalImmersion Y
  let F := diagonalForget l W
  let F' := diagonalForget l P
  let B := upperStar Ab.{u + 1} d
  let M := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) d
  let e := forgetPullbackIso l d
  let : F.Faithful := by dsimp [F, diagonalForget]; infer_instance
  intro f g heq
  apply NatTrans.ext
  funext n
  apply F.map_injective
  apply (cancel_epi (rH.inv.app n)).1
  apply (cancel_mono (rK.hom.app n)).1
  have hN : 0 < l ^ (n.unop + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hunit : IsUnit ((l ^ (n.unop + 1) : ℕ) : Γ(Y, ⊤)) := by
    simpa only [Nat.cast_pow] using hY.pow (n.unop + 1)
  apply diagonalFiniteRoot_restriction_injective Y _ hN hunit
  have hn : M.map (f.app n) = M.map (g.app n) := NatTrans.congr_app heq n
  have hb : B.map (F.map (f.app n)) = B.map (F.map (g.app n)) := by
    apply (cancel_epi (e.hom.app (H.obj n))).1
    calc
      e.hom.app (H.obj n) ≫ B.map (F.map (f.app n)) =
          F'.map (M.map (f.app n)) ≫ e.hom.app (K.obj n) :=
        (e.hom.naturality (f.app n)).symm
      _ = F'.map (M.map (g.app n)) ≫ e.hom.app (K.obj n) := by rw [hn]
      _ = e.hom.app (H.obj n) ≫ B.map (F.map (g.app n)) :=
        e.hom.naturality (g.app n)
  simp only [Functor.map_comp]
  rw [hb]

private theorem root_pullback_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    (N : ℕ) (hN : 0 < N) (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (Scheme.proEtaleRootsOfUnityInverseImageMap f N) := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let A := ULift.{u + 1} (ZMod N)
  have hA : (N : A) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self N
  have hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  have h := (Scheme.finiteRootSiteComparison A).choose_spec.choose_spec.2.2.2.2.2.2.1
    N hN hA f hS hX
  have : IsIso ((Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).map
      (cartierRootsIso S N hN hS).hom ≫
        Scheme.proEtaleRootsOfUnityInverseImageMap f N) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).map
      (cartierRootsIso S N hN hS).hom) _

private def pulledRoots (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (hS : IsUnit (l : Γ(S, ⊤)))
    (H : DiagonalSystems l S)
    (r : H ⋙ diagonalForget l S ≅
      Scheme.proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) :
    (H ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime) := by
  let M := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let B := upperStar Ab.{u + 1} f
  let c := ((Scheme.proEtaleRootsOfUnityInverseImageIso f).2.1 l
    (Fact.out : l.Prime)).choose
  have hc (n : ℕᵒᵖ) : IsIso (c.app n) := by
    have hn := ((Scheme.proEtaleRootsOfUnityInverseImageIso f).2.1 l
      (Fact.out : l.Prime)).choose_spec n.unop
    change c.app n = Scheme.proEtaleRootsOfUnityInverseImageMap f
      (l ^ (n.unop + 1)) at hn
    rw [hn]
    apply root_pullback_isIso f _ (pow_pos (Fact.out : l.Prime).pos _)
    simpa only [Nat.cast_pow] using hS.pow (n.unop + 1)
  let : ∀ n : ℕᵒᵖ, IsIso (c.app n) := hc
  let : IsIso c := NatIso.isIso_of_isIso_app c
  exact Functor.associator H M (diagonalForget l X) ≪≫
    Functor.isoWhiskerLeft H (forgetPullbackIso l f) ≪≫
    (Functor.associator H (diagonalForget l S) B).symm ≪≫
    Functor.isoWhiskerRight r B ≪≫ asIso c

/-- Pullback to the diagonal detects maps from a geometrically pulled-back root
tower to a root tower on the new base.
Source: diagonal coefficient changes (3), cartesian root sheaves and
connected-fibre scalar rigidity.
(blueprint: lem-diagonal-root-tower-rigidity).

Proof: ordinary roots commute with arbitrary inverse image when the exponent
is invertible. This follows from the finite-root site comparison square: its
other three maps are isomorphisms. The canonical fixed-scalar forgetting
comparison therefore gives the pulled-back tower a roots presentation. Apply
the ordinary root-tower restriction theorem on the new base. -/
theorem diagonalPulledRootTower_restriction_injective (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (f : diagonalSurface Y' ⟶ diagonalSurface Y)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (K : DiagonalSystems l (diagonalSurface Y'))
    (rH : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (rK : K ⋙ diagonalForget l (diagonalSurface Y') ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y') l (Fact.out : l.Prime)) :
    Function.Injective (fun h :
      H ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ⟶ K ↦
      Functor.whiskerRight h
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (diagonalImmersion Y'))) := by
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using hY.map
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≫
        (ProjectiveLine Y ↘ Y)).appTop.hom
  exact diagonalRootTower_restriction_injective l Y' hY' _ K
    (pulledRoots l f hW H rH) rK

end AlgebraicGeometry.ProEtale.DiagonalTrace
