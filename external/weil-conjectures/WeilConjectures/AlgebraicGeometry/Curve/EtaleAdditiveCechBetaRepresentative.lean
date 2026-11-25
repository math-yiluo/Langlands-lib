/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaQuasiIso
import Mathlib.Algebra.Homology.ConcreteCategory

/-! # Coefficient representatives of arbitrary total homology classes

Source: Stacks Project, Tags 03P2 and 01EQ. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient augmentation represents every total homology class.
Source: Stacks Project, Tags 03P2 and 01EQ, the affine column comparison.
(blueprint: new-w2-additive-cech-beta-representative)

Proof: Choose a preimage of the given class under the beta homology isomorphism,
then a cycle representing that class using the surjection homologyPi. Its
cochain is an ULift of an ordinary cochain x; the lifted differential equation
implies that x is a cycle. Construct the ordinary cycle using cyclesMk. Apply
the chain map to the lifted cycle. Naturality of iCycles gives its beta inclusion,
and naturality of homologyPi gives the desired class. No global cycle, covering
condition, compactness or choice of an edge equivalence is used. -/
theorem additiveCech_beta_representative
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (h : (additiveCechTotal U I).homology n) :
    ∃ (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
      (tβ : (additiveCechTotal U I).cycles n),
      (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) ∧
      (additiveCechTotal U I).homologyπ n tβ = h := by
  classical
  let C := cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)
  let F := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let L := (F.mapHomologicalComplex (.up ℕ)).obj C
  obtain ⟨b, hb, hq⟩ := exists_additiveCech_beta_quasiIso X U hU I
  let : QuasiIso b := hq
  obtain ⟨w, hw⟩ := (AddCommGrpCat.epi_iff_surjective (L.homologyπ n)).mp
    inferInstance ((inv (HomologicalComplex.homologyMap b n)) h)
  let x : C.X n := (L.iCycles n w).down
  have hx : C.d n (n + 1) x = 0 := by
    have hd := ConcreteCategory.congr_hom (L.iCycles_d n (n + 1)) w
    exact congrArg ULift.down hd
  let z : C.cycles n := C.cyclesMk x (n + 1) (by simp) hx
  have hz : C.iCycles n z = x := C.i_cyclesMk x (n + 1) (by simp) hx
  let tβ := HomologicalComplex.cyclesMap b n w
  refine ⟨z, tβ, ?_, ?_⟩
  · have he := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i b n) w
    change (additiveCechTotal U I).iCycles n tβ = _ at he
    rw [hz]
    exact he.trans (hb n x)
  · have he :=
      (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality b n) w).symm
    change (additiveCechTotal U I).homologyπ n tβ =
      HomologicalComplex.homologyMap b n (L.homologyπ n w) at he
    rw [hw] at he
    exact he.trans (ConcreteCategory.congr_hom (IsIso.inv_hom_id
      (HomologicalComplex.homologyMap b n)) h)

end AlgebraicGeometry.Scheme.Modules
