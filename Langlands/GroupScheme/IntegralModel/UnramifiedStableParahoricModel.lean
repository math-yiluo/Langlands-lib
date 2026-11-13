import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelStatement
import Langlands.Geometry.Building.UnramifiedSimplyConnectedZero
import Langlands.GroupScheme.IntegralModel.UnramifiedStableSetModelDescent
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent

/-! # Conditional descent of a simply connected stable parahoric model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building
open Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme.IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance stableParahoricExtendedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (hparahoric : UnramifiedParahoricModelStatement.{u})
  (hdescent : UnramifiedSmoothModelDescentStatement.{u})
  (hG : IsSimplyConnected (baseChanged F (inertiaFixedField F) G))
  {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (D : MaximalUnramified.SemilinearApartmentData C)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  {Y : Set C.ReducedBuilding}
  (a : rationalPoints (baseChanged F (inertiaFixedField F) G))
  (Ωa : Set C.Apartment)
  (hne : Ωa.Nonempty)
  (hbounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa))
  (himage : Y = (fun x => a • C.apartmentMap x) '' Ωa)
  (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    D.action σ '' Y = Y)
  (hfix : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
    (g • ·) '' Y = Y → g ∈ C.pointwiseFixer Y)

set_option maxHeartbeats 1200000 in
include hparahoric hdescent hG D E a Ωa hne hbounded himage hstable hfix in
/-- The neutral parahoric model has the full stabilizer as its point image
under the supplied pointwise-fixation premise, and descends with connected
special fibre under the supplied model-existence and descent statements. -/
theorem exists_descendedStableParahoricModel :
    ∃ M : IntegralModel ↥𝒪[F] F G,
      M.IsSmooth ∧ M.HasConnectedSpecialFibre ∧
      ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
        g ∈ M.baseChangeUnramified.integralPoints ↔ (g • ·) '' Y = Y := by
  obtain ⟨P, _, hneutral⟩ := hparahoric F G C E a Ωa hne hbounded
  have hneutral' : P.neutral.integralPoints = C.pointwiseFixer Y := by
    calc
      _ = E.zeroPoints ⊓ C.pointwiseFixer ((fun x => a • C.apartmentMap x) '' Ωa) :=
        hneutral
      _ = ⊤ ⊓ C.pointwiseFixer ((fun x => a • C.apartmentMap x) '' Ωa) :=
        congrArg (fun H => H ⊓ C.pointwiseFixer ((fun x => a • C.apartmentMap x) '' Ωa))
          (E.zeroPoints_eq_top_of_isSimplyConnected hG)
      _ = C.pointwiseFixer ((fun x => a • C.apartmentMap x) '' Ωa) := top_inf_eq _
      _ = C.pointwiseFixer Y := congrArg C.pointwiseFixer himage.symm
  have hpoints (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
      g ∈ P.neutral.integralPoints ↔ (g • ·) '' Y = Y := by
    rw [hneutral']
    constructor
    · intro hg
      have hfixed := C.apartment.mem_pointwiseFixer.mp hg
      apply Set.Subset.antisymm
      · rintro z ⟨y, hy, rfl⟩
        change g • y ∈ Y
        rwa [hfixed y hy]
      · intro z hz
        exact ⟨z, hz, hfixed z hz⟩
    · exact hfix g
  let M := descendedStableSetModel hdescent D hstable P.neutral
    P.neutral_smooth hpoints
  obtain ⟨e⟩ := descendedStableSetModel_iso hdescent D hstable P.neutral
    P.neutral_smooth hpoints
  exact ⟨M, descendedStableSetModel_smooth hdescent D hstable P.neutral
      P.neutral_smooth hpoints,
    M.hasConnectedSpecialFibre_of_unramified_iso e P.neutral_connectedFibres,
    descendedStableSetModel_mem_integralPoints_iff hdescent D hstable P.neutral
      P.neutral_smooth hpoints⟩

/-- Choose the smooth descent of the neutral model of a supplied stable,
nonempty, affine-bounded apartment subset under explicit existence, descent,
simple-connectedness and pointwise-fixation premises. -/
def descendedStableParahoricModel : IntegralModel ↥𝒪[F] F G :=
  (exists_descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
    hne hbounded himage hstable hfix).choose

theorem descendedStableParahoricModel_smooth :
    (descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
      hne hbounded himage hstable hfix).IsSmooth :=
  (exists_descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
    hne hbounded himage hstable hfix).choose_spec.1

theorem descendedStableParahoricModel_connectedSpecialFibre :
    (descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
      hne hbounded himage hstable hfix).HasConnectedSpecialFibre :=
  (exists_descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
    hne hbounded himage hstable hfix).choose_spec.2.1

theorem descendedStableParahoricModel_mem_integralPoints_iff
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) :
    g ∈ (descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
      hne hbounded himage hstable hfix).baseChangeUnramified.integralPoints
      ↔ (g • ·) '' Y = Y :=
  (exists_descendedStableParahoricModel hparahoric hdescent hG D E a Ωa
    hne hbounded himage hstable hfix).choose_spec.2.2 g

end Langlands.GroupScheme.IntegralModel
