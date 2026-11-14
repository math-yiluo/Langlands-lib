import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientStatement
import Langlands.Geometry.Building.UnramifiedTwistedGeneratorChamberStatement

/-! # From finite-field quotient data to a generator-stable chamber -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The geometric quotient construction suffices for the generator chamber input. -/
def UnramifiedTwistedChamberQuotientReductionStatement : Prop :=
  UnramifiedTwistedChamberQuotientStatement.{u} →
    UnramifiedTwistedGeneratorChamberStatement.{u}

private instance unramifiedTwistedQuotientReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

set_option maxHeartbeats 1600000 in
/-- The actual-residue quotient witnesses and Lang correction give a chamber
stable under the chosen dense generator, retaining the exact closure witnesses. -/
theorem unramifiedTwistedGeneratorChamber_of_quotient
    (hquot : UnramifiedTwistedChamberQuotientStatement.{u}) :
    UnramifiedTwistedGeneratorChamberStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let := mono_of_isMaximalSplitTorus hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hfin y hy
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let B := UnramifiedBuildingDescent.buildingData iT
    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
    hiT D C h6
  let A := UnramifiedBuildingDescent.semilinearData iT
    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
    hiT C h6 hD
  obtain ⟨φ, hdense, hred⟩ := hquot F G hG T iT hiT D C h6 hD c hc hfin y hy
  have hsemi : ∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
      (z : B.ReducedBuilding),
      c φ • A.action φ (g • z) =
        (c φ * rationalConjugate F (inertiaFixedField F) G φ g * (c φ)⁻¹) •
          (c φ • A.action φ z) := by
    intro g z
    rw [A.action_smul]
    simp only [mul_smul, inv_smul_smul]
  obtain ⟨Y, _, hstable, hpres⟩ := hred.exists_stable_chamber hsemi
  exact ⟨φ, hdense, Y, hstable, hpres⟩

/-- The conditional reduction is proved at every universe. -/
theorem unramifiedTwistedChamberQuotientReduction :
    UnramifiedTwistedChamberQuotientReductionStatement.{u} :=
  unramifiedTwistedGeneratorChamber_of_quotient

end Langlands.Geometry.Building
