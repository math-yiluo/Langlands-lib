import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIwahoriModelStatement
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.Geometry.Building.KPZeroDatumExistence
import Langlands.Geometry.Building.IntegerValuationChamberBounded
import Langlands.GroupScheme.IntegralModel.UnramifiedStableParahoricModel

/-! # Conditional construction of the model of a stable chamber -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building
open Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme

private instance localIwahoriAssemblyExtendedAffineHom
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

section Chamber

variable
  (hparahoric : UnramifiedParahoricModelStatement.{u})
  (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
  {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (hG : IsSimplyConnected G)
  {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (D : MaximalUnramified.SemilinearApartmentData C)
  {Y : Set C.ReducedBuilding} (hY : C.IsChamber Y)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    D.action σ '' Y = Y)
  (hfix : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
    (g • ·) '' Y = Y → g ∈ C.pointwiseFixer Y)

include hparahoric hdescent hG D hY hstable hfix in
/-- The model of the specified stable chamber, conditional on the two general
model statements and pointwise fixation by its setwise stabilizer. -/
theorem exists_localUnramifiedIwahoriModel_of_inputs :
    ∃ M : IntegralModel 𝒪[F] F G,
      M.IsSmooth ∧ M.HasConnectedSpecialFibre ∧
      ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
        g ∈ M.baseChangeUnramified.integralPoints ↔ (g • ·) '' Y = Y := by
  have hGK : IsSimplyConnected (baseChanged F (inertiaFixedField F) G) :=
    isSimplyConnectedFieldExtension F (inertiaFixedField F) G hG
  let E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G) :=
    UnramifiedZeroDatum.ofConnectedReductive _ hGK.isSemisimple.isConnectedReductive
  obtain ⟨a, Ωa, hne, hbounded, himage⟩ :=
    MaximalUnramified.isChamber_exists_bounded C hY
  exact IntegralModel.exists_descendedStableParahoricModel hparahoric hdescent
    hGK D E a Ωa hne hbounded himage hstable hfix

/-- Choose the actual integral model of the supplied stable chamber under
the explicit model-existence, descent and fixation premises. -/
def localUnramifiedIwahoriModelOfInputs : IntegralModel 𝒪[F] F G :=
  (exists_localUnramifiedIwahoriModel_of_inputs
    hparahoric hdescent hG D hY hstable hfix).choose

theorem localUnramifiedIwahoriModelOfInputs_smooth :
    (localUnramifiedIwahoriModelOfInputs
      hparahoric hdescent hG D hY hstable hfix).IsSmooth :=
  (exists_localUnramifiedIwahoriModel_of_inputs
    hparahoric hdescent hG D hY hstable hfix).choose_spec.1

theorem localUnramifiedIwahoriModelOfInputs_connectedSpecialFibre :
    (localUnramifiedIwahoriModelOfInputs
      hparahoric hdescent hG D hY hstable hfix).HasConnectedSpecialFibre :=
  (exists_localUnramifiedIwahoriModel_of_inputs
    hparahoric hdescent hG D hY hstable hfix).choose_spec.2.1

theorem localUnramifiedIwahoriModelOfInputs_mem_integralPoints_iff
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    g ∈ (localUnramifiedIwahoriModelOfInputs
      hparahoric hdescent hG D hY hstable hfix).baseChangeUnramified.integralPoints
      ↔ (g • ·) '' Y = Y :=
  (exists_localUnramifiedIwahoriModel_of_inputs
    hparahoric hdescent hG D hY hstable hfix).choose_spec.2.2 g

end Chamber

/-- Reduce the exact Iwahori-model target to the two general model statements
and the assertion that full chamber stabilizers fix chambers pointwise. -/
theorem localSimplyConnectedUnramifiedIwahoriModel_of_inputs
    (hparahoric : UnramifiedParahoricModelStatement.{u})
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hfix : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
      IsSimplyConnected G →
      ∀ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
        (Y : Set C.ReducedBuilding), C.IsChamber Y →
        ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
          (g • ·) '' Y = Y → g ∈ C.pointwiseFixer Y) :
    LocalSimplyConnectedUnramifiedIwahoriModelStatement.{u} := by
  intro F _ _ _ _ G _ hG C D Y hY hstable
  exact exists_localUnramifiedIwahoriModel_of_inputs hparahoric hdescent
    hG D hY hstable (hfix F G hG C Y hY)

end Langlands.GroupScheme
