/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.FiniteEtaleCoverReducedCompactification
import WeilConjectures.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps
import WeilConjectures.AlgebraicGeometry.Curve.PrimeModuleFiniteOpenAssertionsTransfer

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve
/-- The compactification and filtration part of the filtered-cover transfer.

The proof is the first part of Stacks Project 03SD, using 05K0 to factor the finite
etale cover through an open immersion into a finite scheme over `X`.  Replace the
finite scheme by the reduced closure of the open image.  The open image is then a
dense open of a reduced curve, and over `U` it is also closed: its map to the
preimage of `U` is finite, while a finite dense open immersion is surjective.
Thus the resulting square is the cartesian square needed for base change.

Apply `hconstant` to this new reduced curve.  Exactness of extension by zero and
the short exact sequences supplied by `hquot` allow induction along `W`, starting
from `hzero`; the induction uses the cokernel identifications and the standard
short-exact devissage assertion.  Transport the result across `hend`.  Finite
pushforward and the exchange isomorphism for lower shriek transfer the resulting
assertions to the lower-star of the upper-star of `G`.  This is precisely the
conclusion below. No unit retraction is needed for this step; descent along the
retraction is performed only in the separate retract theorem.
(blueprint: k1-filtered-finite-cover-lower-shriek-transfer-core) -/
theorem filteredFiniteCoverLowerShriekTransfer_core {k : Type u} [Field k] [IsAlgClosed k]
    {X U V : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    (n : ℕ)
    (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (ι : ∀ i, W i ⟶ W (i + 1)) (hzero : IsZero (W 0))
    (hend : Nonempty (W n ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))
    (hquot : ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
      (constantSheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))
    (hconstant : ∀ {Y T : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsReduced Y]
      (a : T ⟶ Y) [IsOpenImmersion a],
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) g
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
          ((constantSheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))) :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))) :=
  by
  classical
  obtain ⟨Y, p, a, hp, hg, hY, ha, sq⟩ :=
    exists_reduced_cartesian_finite_cover_compactification f j v
  let : IsFinite p := hp
  let : IsCurve (p ≫ f) := hg
  let : IsReduced Y := hY
  let : IsOpenImmersion a := ha
  obtain ⟨hbase, hstep⟩ := open_lowerShriek_constant_filtration_steps
    (p ≫ f) a r n W ι hzero hquot (hconstant (p ≫ f) a)
  have hW : ∀ i ≤ n, Assertions (ULift.{u + 1} (ZMod r)) (p ≫ f)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
        (W i)) := by
    intro i
    induction i with
    | zero => intro _; exact hbase
    | succ i ih =>
      intro hi
      exact hstep i (Nat.lt_of_succ_le hi) (ih (Nat.le_of_succ_le hi))
  obtain ⟨e⟩ := hend
  exact prime_module_finite_open_assertions_transfer f p j a v sq r (W n) _ e
    (hW n le_rfl)

end AlgebraicGeometry.IsCurve
