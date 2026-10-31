import Langlands.Algebra.RenardStableIdealFiniteLocalizationStatements
import Langlands.Algebra.RenardCompatibleLocalizationNoetherianProof
import Langlands.Algebra.RenardCompatibleStableImageProof
import Langlands.Algebra.UnitizationIdealNoetherianProof
import Langlands.Algebra.UnitizationStableGenerationProof

/-!
# Actual localization under explicit stable-ideal finiteness: proof

Proof of the internal derived target motivated by Renard 2026, C.II,
printed p. 279 / PDF p. 285. The three explicit stable-generation
hypotheses become Noetherianity of the actual unitization and finiteness
of the two actual unitized modules; the published Noetherian localization
and stable-image results then give both conclusions.
-/

set_option autoImplicit false

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

/-- Finite stable generation of every complex-linear left ideal, of the source and of its
actual localization gives stabilization and the canonical compatible identification with
every positive stable image. -/
theorem stableIdealFiniteLocalization : StableIdealFiniteLocalizationStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f hB hV hL
  let σ := localizedAction f.toLinearMap ρ fun b v => f.map_action' b v
  let _ := CompatibleUnitization.module (NonUnitalAlgHom.lmul ℂ B)
  let _ := CompatibleUnitization.isScalarTower (NonUnitalAlgHom.lmul ℂ B)
  let _ := CompatibleUnitization.module ρ
  let _ := CompatibleUnitization.isScalarTower ρ
  let _ := CompatibleUnitization.module σ
  let _ := CompatibleUnitization.isScalarTower σ
  have hR : IsNoetherianRing (Unitization ℂ B) :=
    (UnitizationIdealNoetherian.scalarIdealCriterion ℂ B
      (CompatibleUnitization.smul_eq (NonUnitalAlgHom.lmul ℂ B))).2 hB
  have hVf : Module.Finite (Unitization ℂ B) V :=
    (UnitizationStableGeneration.moduleGeneration ℂ B V ρ
      (CompatibleUnitization.smul_eq ρ)).2 hV
  have hLf : Module.Finite (Unitization ℂ B) (Localized f.toLinearMap) :=
    (UnitizationStableGeneration.moduleGeneration ℂ B (Localized f.toLinearMap) σ
      (CompatibleUnitization.smul_eq σ)).2 hL
  exact ⟨stabilizationAt_of_finite ρ f hR hVf hLf, fun n hn hs =>
    CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable ρ f n hn hs⟩

end Langlands.Renard.AlgebraActionLocalization
