import Langlands.BruhatTits.IntegralModels.UnramifiedFixedSubsetRecovery
import Langlands.BruhatTits.IntegralModels.UnramifiedFixerModelComparison

/-! # Recovered models along fixed descended translation lines -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped ValuativeRel CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (f : S ⟶ T) (hS : IsSplitTorus S.toGrp)

private instance nearbyExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- Recovered models of the singleton and every translated two-point set,
with actual compatible full and neutral comparison maps. -/
structure RecoveredFixedNearbyModels (x : D.Apartment) where
  target : RecoveredApartmentFixerModels D {x}
  source : ∀ v : V S,
    RecoveredApartmentFixerModels D {x, D.descentTranslate f hS x v}
  comparison : ∀ v : V S,
    RelativeComponentModelHom (source v).lower target.lower

/-- Choose the singleton and two-point models using the four retained model
inputs. Hom extension supplies the actual comparison over the generic identity. -/
def recoveredFixedNearbyModelsOfVertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hext : IntegralModel.UnramifiedSmoothHomExtensionStatement.{u})
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (x : D.Apartment)
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredFixedNearbyModels D f hS x := by
  let target := recoveredFixedPointModelsOfVertexInputs D hvertex hmaximal
    hintersection hdescent hG hiT C hDC x hx
  let source := fun v : V S =>
    recoveredFixedPairModelsOfVertexInputs D hvertex hmaximal hintersection
      hdescent hG hiT C hDC x (D.descentTranslate f hS x v) hx
      (D.galois_fixed_descentTranslate f hS x hx v)
  refine ⟨target, source, fun v => ?_⟩
  exact comparisonOfRecoveredFixerModels D hext (source v).recovery target.recovery
    (by
      intro z hz
      have : z = x := Set.mem_singleton_iff.mp hz
      exact this ▸ Set.mem_insert x {D.descentTranslate f hS x v})
    (source v).full_integralPoints target.full_integralPoints

namespace RecoveredFixedNearbyModels

variable {D f hS} {x : D.Apartment} (M : RecoveredFixedNearbyModels D f hS x)

/-- Every upper full source integral point fixes the translated endpoint,
including when that endpoint coincides with the original point. -/
theorem source_full_integralPoints_le_translatedFixer (v : V S) :
    (M.source v).upper.full.integralPoints ≤
      D.reducedFixer (D.apartmentMap (D.descentTranslate f hS x v)) := by
  intro g hg
  rw [(M.source v).full_integralPoints] at hg
  apply D.mem_reducedFixer.mpr
  exact D.mem_pointwiseFixer.mp hg.2 _
    ⟨D.descentTranslate f hS x v, Set.mem_insert_of_mem x (Set.mem_singleton _), rfl⟩

/-- The remaining geometric conditions on these actual comparison maps.
Both conditions are required on one common neighbourhood of zero in each line. -/
def HasParabolicComparisonsNear : Prop :=
  ∀ v : V S, ∀ᶠ t : ℝ in 𝓝 0,
    (M.comparison (t • v)).HasParabolicSpecialFibreImage ∧
      (M.comparison (t • v)).HasParabolicReductionPreimage

variable [Smooth G.X.hom]
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hopp : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

include hGK hf

/-- Exact two-point fixer recovery supplies all integral-root depth bounds;
only parabolic images and exact reduction preimages remain to be established. -/
theorem parabolicRootComparisonsNear
    (hpar : M.HasParabolicComparisonsNear) :
    D.ParabolicRootComparisonsNearDescentTranslations f hS hiT.isSplitSubtorus.1
      hopp iS M.target.lower x := by
  apply parabolicRootComparisonsNear_of_recoveredFixerModels
    D hGK hiT f hf hS hopp M.target.lower x
  intro v
  filter_upwards [hpar v] with t ht
  exact ⟨(M.source (t • v)).lower, (M.source (t • v)).upper,
    (M.source (t • v)).recovery, M.comparison (t • v), ht.1, ht.2,
    M.source_full_integralPoints_le_translatedFixer (t • v)⟩

end RecoveredFixedNearbyModels

end Langlands.BruhatTits.IntegralModels
