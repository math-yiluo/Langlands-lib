import Langlands.GroupScheme.Reductive.PinningBaseChange
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-! # Numberings of scalar-extended split pinnings -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

local instance pinningNumberingAffine {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd _ _ inferInstance

namespace SplitPinning

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Algebra.IsAlgebraic F L]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

/-- Transport a numbering along the supplied pinning's actual scalar extension. -/
def baseChangeNumbering {n : ℕ} (e : p.base.support ≃ Fin n) :
    (p.baseChange (F := L)).base.support ≃ Fin n :=
  (p.baseChangeSimpleEquiv (F := L)).symm.trans e

@[simp]
theorem baseChangeNumbering_apply {n : ℕ} (e : p.base.support ≃ Fin n)
    (a : p.base.support) :
    p.baseChangeNumbering (L := L) e (p.baseChangeSimpleEquiv (F := L) a) = e a :=
  congrArg e ((p.baseChangeSimpleEquiv (F := L)).symm_apply_apply a)

theorem baseChangeNumbering_cartan {n : ℕ} (e : p.base.support ≃ Fin n)
    (h : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.D n (e a) (e b)) :
    ∀ a b, (p.baseChange (F := L)).rootDatum.pairing a.val b.val =
      CartanMatrix.D n (p.baseChangeNumbering (L := L) e a)
        (p.baseChangeNumbering (L := L) e b) := by
  intro a b
  obtain ⟨a, rfl⟩ := (p.baseChangeSimpleEquiv (F := L)).surjective a
  obtain ⟨b, rfl⟩ := (p.baseChangeSimpleEquiv (F := L)).surjective b
  rw [baseChangeNumbering_apply, baseChangeNumbering_apply]
  change (p.baseChangeRootDatum (F := L)).pairing a.val b.val = _
  rw [← RootPairing.root_coroot_eq_pairing]
  change (SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
    p.rootDatum).toLinearMap
      ((SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
        p.rootDatum).root a.val)
      ((SplitRootDatum.baseChange (algebraBaseMap F L) p.torus p.isSplitTorus
        p.rootDatum).coroot b.val) = _
  rw [SplitRootDatum.baseChange_root, SplitRootDatum.baseChange_coroot,
    SplitRootDatum.baseChange_pairing, RootPairing.root_coroot_eq_pairing]
  exact h a b

end SplitPinning

end Langlands.GroupScheme
