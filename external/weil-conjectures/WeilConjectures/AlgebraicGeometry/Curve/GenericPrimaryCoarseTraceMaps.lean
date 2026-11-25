/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegreeTrace
import Mathlib.Data.Int.GCD

/-! # Rescaled trace transported through a commuting generic-point square

Source: blueprint `theorem-cohomology-curves--2`, proof paragraph 2.
(blueprint: lem-sc-generic-primary-coarse-trace-retraction-maps)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.IsConnectedCurve

/-- A finite etale generic cover of degree coprime to an annihilator gives a
retraction after generic direct image and terminal-sheaf identification.

Source: blueprint `theorem-cohomology-curves--2`, proof paragraph 2.
Proof: Bezout rescales trace to invert degree multiplication on M. Apply generic
pushforward and identify both composites of pushforwards using the commuting
square. Conjugate by the terminal-sheaf isomorphism.
(blueprint: lem-sc-generic-primary-coarse-trace-retraction-maps) -/
theorem exists_generic_primary_coarse_trace_maps
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D] (π : D ⟶ C)
    (q : Spec D.functionField ⟶ Spec C.functionField) [Etale q]
    (hsquare : q ≫ C.fromSpecFunctionField = D.fromSpecFunctionField ≫ π)
    (d m : ℕ) [q.IsFiniteLocallyFreeOfDegree d] (hcop : d.Coprime m)
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hkill : m • 𝟙 M = 0)
    (N : Sheaf (Spec D.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (Etale.upperStar AddCommGrpCat.{u + 1} q).obj M ≅ N) :
    ∃ (a : (Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} π).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj N))
      (b : (Etale.lowerStar AddCommGrpCat.{u + 1} π).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj N) ⟶
        (Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M),
      a ≫ b = 𝟙 _ := by
  let r := Etale.finiteEtaleRestriction q M
  let t := Etale.finiteEtaleTrace q M
  have hdegree : r ≫ t = d • 𝟙 M :=
    Etale.finiteEtaleTrace_comp_restriction q d M
  have hab : (d : ℤ) * Nat.gcdA d m + (m : ℤ) * Nat.gcdB d m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have hsplit : r ≫ (Nat.gcdA d m • t) = 𝟙 M := by
    rw [Preadditive.comp_zsmul, hdegree]
    have hk : (m : ℤ) • 𝟙 M = 0 := by simpa using hkill
    have hi := congrArg (fun z : ℤ ↦ z • 𝟙 M) hab
    simpa [add_zsmul, mul_zsmul, hk, mul_comm] using hi
  let G := Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField
  let Q := Etale.lowerStar AddCommGrpCat.{u + 1} q
  let P := Etale.lowerStar AddCommGrpCat.{u + 1} π
  let H := Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField
  let c : G.obj (Q.obj ((Etale.upperStar AddCommGrpCat.{u + 1} q).obj M)) ≅
      P.obj (H.obj N) :=
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} q C.fromSpecFunctionField).app _ ≪≫
      ((Etale.lowerStarComp AddCommGrpCat.{u + 1} D.fromSpecFunctionField π
        (q ≫ C.fromSpecFunctionField) hsquare).app _).symm ≪≫
      P.mapIso (H.mapIso e)
  refine ⟨G.map r ≫ c.hom, c.inv ≫ G.map (Nat.gcdA d m • t), ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, hsplit, G.map_id]
  rfl

end AlgebraicGeometry.IsConnectedCurve
