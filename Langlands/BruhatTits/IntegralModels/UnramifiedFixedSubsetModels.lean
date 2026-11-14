import Langlands.BruhatTits.IntegralModels.UnramifiedFixedSubsetRecovery
import Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof
import Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction
import Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof

/-! # Recovered fixed-subset models from published construction proofs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
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

include hG hiT C hDC in
/-- Published vertex, bounded-model, intersection and descent proofs supply
actual compatible full and neutral models for a bounded fixed subset. -/
theorem exists_recoveredFixedSubsetModels
    (Ω : Set D.Apartment) (hne : Ω.Nonempty)
    (hbounded : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    Nonempty (RecoveredApartmentFixerModels D Ω) :=
  exists_recoveredFixedSubsetModels_of_vertexInputs D
    MaximalUnramified.vertexOneStabilizerMaximalBounded maximalBoundedIntegralModel
    IntegralModel.smoothIntersection IntegralModel.unramifiedSmoothModelDescent
    hG hiT C hDC Ω hne hbounded hΩ

/-- Choose the recovered models without retaining any of the four global
construction statements as a premise. -/
def recoveredFixedSubsetModels
    (Ω : Set D.Apartment) (hne : Ω.Nonempty)
    (hbounded : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredApartmentFixerModels D Ω :=
  Classical.choice
    (exists_recoveredFixedSubsetModels D hG hiT C hDC Ω hne hbounded hΩ)

/-- A nonempty finite fixed subset is automatically bounded under every
real affine function. -/
def recoveredFixedFiniteSubsetModels
    (Ω : Set D.Apartment) (hfinite : Ω.Finite) (hne : Ω.Nonempty)
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredApartmentFixerModels D Ω :=
  recoveredFixedSubsetModels D hG hiT C hDC Ω hne
    (fun f => (hfinite.image f).bddAbove) hΩ

/-- Every coefficient-fixed point has actual compatible lower and upper
component models with the exact upper full norm-one point fixer. -/
def recoveredFixedPointModels (x : D.Apartment)
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredApartmentFixerModels D {x} :=
  recoveredFixedFiniteSubsetModels D hG hiT C hDC {x}
    (Set.finite_singleton x) (Set.singleton_nonempty x)
    (by simpa only [Set.forall_mem_singleton] using hx)

/-- Two individually coefficient-fixed endpoints have recovered models,
including when the endpoints coincide. -/
def recoveredFixedPairModels (x y : D.Apartment)
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)
    (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) :
    RecoveredApartmentFixerModels D {x, y} :=
  recoveredFixedFiniteSubsetModels D hG hiT C hDC {x, y}
    ((Set.finite_singleton y).insert x) (Set.insert_nonempty x {y}) (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact hx
      · exact Set.mem_singleton_iff.mp hz ▸ hy)

end Langlands.BruhatTits.IntegralModels
