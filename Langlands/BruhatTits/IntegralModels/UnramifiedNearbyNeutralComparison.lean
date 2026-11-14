import Langlands.BruhatTits.IntegralModels.UnramifiedFixedNearbyModels
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralCentralizerComparison
import Langlands.Geometry.Building.UnramifiedNearbyRootFixer

/-! # Nearby neutral groups of recovered apartment fixer models -/

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
  {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

private instance nearbyNeutralExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

include hG hiT hDC

namespace RecoveredApartmentFixerModels

variable {D} {Ω₁ Ω₂ : Set D.Apartment}
  (M : RecoveredApartmentFixerModels D Ω₁)
  (N : RecoveredApartmentFixerModels D Ω₂)

/-- Equal sharp fixers identify the actual upper neutral integral subgroups
of any two supplied recovered models of nonempty subsets. -/
theorem upper_neutral_integralPoints_eq_of_sharpFixer_eq
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : D.sharpFixer Ω₁ = D.sharpFixer Ω₂) :
    M.upper.neutral.integralPoints = N.upper.neutral.integralPoints := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  exact unramifiedNeutral_integralPoints_eq_of_sharpFixer_eq
    B M.upper N.upper Ω₁ Ω₂ M.full_integralPoints N.full_integralPoints
    hne₁ hne₂ hsharp

/-- Exact unramified recovery transfers the upper equality to the original
lower neutral integral subgroups. -/
theorem lower_neutral_integralPoints_eq_of_sharpFixer_eq
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : D.sharpFixer Ω₁ = D.sharpFixer Ω₂) :
    M.lower.neutral.integralPoints = N.lower.neutral.integralPoints := by
  rw [M.recovery.neutral_integralPoints_eq_comap,
    N.recovery.neutral_integralPoints_eq_comap,
    M.upper_neutral_integralPoints_eq_of_sharpFixer_eq hG hiT C hDC N
      hne₁ hne₂ hsharp]

/-- The lower comparison retains every ambient rational point. -/
def lowerNeutralSharpFixerEquiv
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : D.sharpFixer Ω₁ = D.sharpFixer Ω₂) :
    M.lower.neutral.integralPoints ≃* N.lower.neutral.integralPoints :=
  MulEquiv.subgroupCongr
    (M.lower_neutral_integralPoints_eq_of_sharpFixer_eq hG hiT C hDC N
      hne₁ hne₂ hsharp)

@[simp] theorem lowerNeutralSharpFixerEquiv_coe
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : D.sharpFixer Ω₁ = D.sharpFixer Ω₂)
    (g : M.lower.neutral.integralPoints) :
    (M.lowerNeutralSharpFixerEquiv hG hiT C hDC N hne₁ hne₂ hsharp g :
      rationalPoints G) = g := by
  exact MulEquiv.subgroupCongr_apply
    (M.lower_neutral_integralPoints_eq_of_sharpFixer_eq hG hiT C hDC N
      hne₁ hne₂ hsharp) g

variable {x y : D.Apartment}

/-- If the first endpoint lies in the second endpoint's closed facet,
the pair and second singleton have equal upper and lower neutral groups. -/
theorem neutral_integralPoints_pair_eq_singleton_of_mem_facetClosure
    (M : RecoveredApartmentFixerModels D {x, y})
    (N : RecoveredApartmentFixerModels D {y})
    (hxy : x ∈ AffineRootSystem.facetClosure D.affineRoots y) :
    M.upper.neutral.integralPoints = N.upper.neutral.integralPoints ∧
      M.lower.neutral.integralPoints = N.lower.neutral.integralPoints := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  have hsharp := D.sharpFixer_pair_eq_singleton_of_mem_facetClosure
    B.affineRoot_mem_or_two_smul_mem hxy
  exact ⟨M.upper_neutral_integralPoints_eq_of_sharpFixer_eq hG hiT C hDC N
      (Set.insert_nonempty x {y}) (Set.singleton_nonempty y) hsharp,
    M.lower_neutral_integralPoints_eq_of_sharpFixer_eq hG hiT C hDC N
      (Set.insert_nonempty x {y}) (Set.singleton_nonempty y) hsharp⟩

end RecoveredApartmentFixerModels

/-- Along each actual descended line, any recovered pair models and endpoint
singleton models have equal upper and lower neutral groups near zero. -/
theorem eventually_recovered_neutral_integralPoints_pair_eq_singleton
    (f : S ⟶ T) (hS : IsSplitTorus S.toGrp)
    (x : D.Apartment) (v : V S)
    (M : ∀ t : ℝ, RecoveredApartmentFixerModels D
      {x, D.descentTranslate f hS x (t • v)})
    (N : ∀ t : ℝ, RecoveredApartmentFixerModels D
      {D.descentTranslate f hS x (t • v)}) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (M t).upper.neutral.integralPoints = (N t).upper.neutral.integralPoints ∧
        (M t).lower.neutral.integralPoints = (N t).lower.neutral.integralPoints := by
  filter_upwards [D.eventually_mem_facetClosure_descentTranslate
    f hS hG hiT C hDC x v] with t ht
  exact RecoveredApartmentFixerModels.neutral_integralPoints_pair_eq_singleton_of_mem_facetClosure
    hG hiT C hDC (M t) (N t) ht

namespace RecoveredFixedNearbyModels

variable {D} {f : S ⟶ T} {hS : IsSplitTorus S.toGrp} {x : D.Apartment}
  (M : RecoveredFixedNearbyModels D f hS x)

/-- Specialization to the actual pair sources in a recovered nearby-model
package, with any supplied recovered models of the translated endpoints. -/
theorem eventually_source_neutral_integralPoints_eq_endpoint
    (v : V S)
    (N : ∀ t : ℝ, RecoveredApartmentFixerModels D
      {D.descentTranslate f hS x (t • v)}) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (M.source (t • v)).upper.neutral.integralPoints =
          (N t).upper.neutral.integralPoints ∧
        (M.source (t • v)).lower.neutral.integralPoints =
          (N t).lower.neutral.integralPoints :=
  eventually_recovered_neutral_integralPoints_pair_eq_singleton
    D hG hiT C hDC f hS x v (fun t => M.source (t • v)) N

end RecoveredFixedNearbyModels

end Langlands.BruhatTits.IntegralModels
