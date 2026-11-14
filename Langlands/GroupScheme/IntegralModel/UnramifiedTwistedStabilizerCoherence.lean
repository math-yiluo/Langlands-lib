import Langlands.GroupScheme.IntegralModel.InnerSemilinearCoherence
import Langlands.GroupScheme.IntegralModel.UnramifiedTwistedStabilizer

/-! # Coherence for actual unramified twisted stabilizer models -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois.Separable
open Langlands.Geometry.Building
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The actual integer spectrum automorphisms obey the same diagrammatic
composition law as the coefficient field automorphisms. -/
theorem fixedIntegerBaseAut_mul
    (σ τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    fixedIntegerBaseAut F (σ * τ) = fixedIntegerBaseAut F σ ≫ fixedIntegerBaseAut F τ := by
  change Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change (σ * τ) (x : inertiaFixedField F) = σ (τ (x : inertiaFixedField F))
  rfl

end Descent.FiniteUnramified

namespace IntegralModel

open GaloisPointComparison Descent Descent.FiniteUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : MaximalUnramified.SemilinearApartmentData B)
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
  (y : B.ReducedBuilding) (hy : ∀ σ, A.twistedAction c hc σ y = y)
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (hpoints : P.integralPoints = B.oneStabilizer y) (hP : P.IsSmooth)

/-- The actual stabilizer-model maps form a coherent semilinear family for
all coefficient automorphisms. -/
theorem twistedStabilizerModelIso_tower
    (σ τ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    pullbackComparison (fixedIntegerBaseAut F τ) (fixedIntegerBaseAut F σ)
        (fixedIntegerBaseAut F (σ * τ)) (fixedIntegerBaseAut_mul F σ τ).symm P.group ≪≫
          (twistedStabilizerModelIso A c hc y hy P hpoints hP (σ * τ)).iso =
      (GroupScheme.baseChange (fixedIntegerBaseAut F σ)).mapIso
        (twistedStabilizerModelIso A c hc y hy P hpoints hP τ).iso ≪≫
          (twistedStabilizerModelIso A c hc y hy P hpoints hP σ).iso :=
  semilinear_tower_of_generic P
    (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut F τ) (fixedIntegerBaseAut F (σ * τ))
    (fixedIntegerBaseAut_mul F σ τ).symm
    (galoisBaseMap F (inertiaFixedField F) σ) (galoisBaseMap F (inertiaFixedField F) τ)
    (galoisBaseMap F (inertiaFixedField F) (σ * τ))
    (galoisBaseMap_mul F (inertiaFixedField F) σ τ).symm
    (fixedIntegerBaseAut_generic F σ) (fixedIntegerBaseAut_generic F τ)
    (fixedIntegerBaseAut_generic F (σ * τ)) _ _ _ _ _ _
    (twistedStabilizerModelIso_generic_comm A c hc y hy P hpoints hP σ)
    (twistedStabilizerModelIso_generic_comm A c hc y hy P hpoints hP τ)
    (twistedStabilizerModelIso_generic_comm A c hc y hy P hpoints hP (σ * τ))
    (innerGaloisDescentIso_tower F (inertiaFixedField F) G σ τ (σ * τ)
      (galoisBaseMap_mul F (inertiaFixedField F) σ τ).symm
      (c σ) (c τ) (c (σ * τ)) (hc σ τ))

/-- Reindex the actual tower law along a specified product identity. -/
theorem twistedStabilizerModelIso_tower_of_eq
    (σ τ ρ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hρ : ρ = σ * τ)
    (ha : fixedIntegerBaseAut F σ ≫ fixedIntegerBaseAut F τ =
      fixedIntegerBaseAut F ρ) :
    pullbackComparison (fixedIntegerBaseAut F τ) (fixedIntegerBaseAut F σ)
        (fixedIntegerBaseAut F ρ) ha P.group ≪≫
          (twistedStabilizerModelIso A c hc y hy P hpoints hP ρ).iso =
      (GroupScheme.baseChange (fixedIntegerBaseAut F σ)).mapIso
        (twistedStabilizerModelIso A c hc y hy P hpoints hP τ).iso ≪≫
          (twistedStabilizerModelIso A c hc y hy P hpoints hP σ).iso := by
  subst ρ
  exact twistedStabilizerModelIso_tower A c hc y hy P hpoints hP σ τ

variable {S : Scheme.{u}} (p : Spec (CommRingCat.of (fixedFieldIntegers F)) ⟶ S)
  {I : Type} (σ : I → (inertiaFixedField F ≃ₐ[F] inertiaFixedField F))
  (q : I → (Spec (CommRingCat.of (fixedFieldIntegers F)) ⟶ Overlap p))
  [∀ i, IsIso (q i ≫ fst p)] [Finite I] [IsIso (Sigma.desc q)]
  (hf : ∀ i, q i ≫ fst p = 𝟙 _)
  (hg : ∀ i, q i ≫ snd p = fixedIntegerBaseAut F (σ i))
  (m : I → I → I) (hσ : ∀ i j, σ (m i j) = σ i * σ j)

/-- A supplied finite normalized component cover turns the actual coherent
stabilizer-model maps into integral Čech descent data. -/
def datumOfTwistedStabilizerModel : Datum p P.group :=
  SemilinearComponents.datumOfSemilinear p q (fun i => fixedIntegerBaseAut F (σ i))
    hf hg m (fun i j => by rw [hσ i j]; exact (fixedIntegerBaseAut_mul F _ _).symm)
    P.group (fun i => (twistedStabilizerModelIso A c hc y hy P hpoints hP (σ i)).iso)
    (fun i j => twistedStabilizerModelIso_tower_of_eq A c hc y hy P hpoints hP
      (σ i) (σ j) (σ (m i j)) (hσ i j) _)

/-- Every normalized component is the specified integral twisted stabilizer
isomorphism, with its canonical orientation as an overlap map. -/
theorem pullIso_datumOfTwistedStabilizerModel (i : I) :
    pullIso (q i) (hf i) (hg i)
        (datumOfTwistedStabilizerModel A c hc y hy P hpoints hP p σ q hf hg m hσ).overlap =
      semilinearComponent P.group
        (twistedStabilizerModelIso A c hc y hy P hpoints hP (σ i)).iso :=
  SemilinearComponents.pullIso_datumOfSemilinear p q
    (fun i => fixedIntegerBaseAut F (σ i)) hf hg m
    (fun i j => by rw [hσ i j]; exact (fixedIntegerBaseAut_mul F _ _).symm)
    P.group (fun i => (twistedStabilizerModelIso A c hc y hy P hpoints hP (σ i)).iso) _ i

end IntegralModel
end Langlands.GroupScheme
