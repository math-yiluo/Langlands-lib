import Langlands.LocalFactor.BrauerKernel.StandaloneEpsilon
import Langlands.LocalFactor.BrauerKernel.PlaceRamification
import Langlands.LocalFactor.BrauerKernel.PlaceNorm
import Langlands.Global.Factors.RelativeWeilLocalHecke

/-! # Local epsilon products of a global relation at the finite places other than `v` -/

noncomputable section

set_option autoImplicit false

universe u w

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open VirtualRepresentation CommonClosure Correspondence
open scoped NumberField

variable {k E' : Type u} [Field k] [NumberField k] [Field E'] [NumberField E'] [Algebra k E']
  {J : Type*} [Fintype J] (r : J → ℤ) (K : J → IntermediateField k E')
  (Λ₁ Λ₂ : ∀ j, HeckeCharacter (K j)) (z : Langlands.Global.FinitePlace k)
  (eC : ReciprocityFamily (padicField z)) (heC : NormalizedReciprocity (padicField z) eC)

/-- The relation among induced characters of `W_{k_z}` obtained by restricting a global
relation to the place `z` (the form of `sum_induce_weilCharacter_eq_zero`). -/
def LocalPlaceRelation : Prop :=
  ∑ j : (Σ j, FinitePlacesAbove (K j) z), r j.1 •
      ExactGrothendieckGroup.continuousInduceAlong
        (Weil.Local.extensionWeilMap (padicField z) (towerPadicField z j.2.1)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1))
        (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
        (ExactGrothendieckGroup.characterClass.{u, w}
            (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
              (LocalClassField.extensionReciprocityCandidate (padicField z)
                (towerPadicField z j.2.1)
                (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) eC)
              (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                ((Λ₁ j.1).finiteComponent j.2.1))) -
          ExactGrothendieckGroup.characterClass.{u, w}
            (LocalFactor.RankOne.weilCharacter (towerPadicField z j.2.1)
              (LocalClassField.extensionReciprocityCandidate (padicField z)
                (towerPadicField z j.2.1)
                (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) eC)
              (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1)
                ((Λ₂ j.1).finiteComponent j.2.1)))) = 0

/-- The Tate epsilon product of the place `z`, for the standalone trace character of `ψz` and
Haar measures `μ`. -/
def placeEpsilonRatioProduct (ψz : NontrivialAdditiveCharacter (padicField z))
    (μ : ∀ j : (Σ j, FinitePlacesAbove (K j) z),
      LocalAdditiveHaarMeasure (towerPadicField z j.2.1)) : ℂ :=
  ∏ j : (Σ j, FinitePlacesAbove (K j) z),
    (PadicAbelian.epsilon (towerPadicField z j.2.1).canonicalTopologicalData
        (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₁ j.1).finiteComponent j.2.1))
        (Weil.Local.SystemEpsilon.standaloneTraceCharacter (padicField z) (towerPadicField z j.2.1)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) ψz)
        (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
          (towerPadicField z j.2.1).canonicalTopologicalData.topology
          (@borel _ (towerPadicField z j.2.1).canonicalTopologicalData.topology) (μ j)) 0 /
      PadicAbelian.epsilon (towerPadicField z j.2.1).canonicalTopologicalData
        (quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₂ j.1).finiteComponent j.2.1))
        (Weil.Local.SystemEpsilon.standaloneTraceCharacter (padicField z) (towerPadicField z j.2.1)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) ψz)
        (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
          (towerPadicField z j.2.1).canonicalTopologicalData.topology
          (@borel _ (towerPadicField z j.2.1).canonicalTopologicalData.topology) (μ j)) 0) ^ r j.1

/-- The component of `(α ∘ N) · Φ` at a place `u` above `z` is the component of `Φ` times `α_z`
composed with the local norm. -/
theorem quasicharacterAt_normComp_mul (α : HeckeCharacter k) {M : IntermediateField k E'}
    (Φ : HeckeCharacter M) (u : FinitePlacesAbove M z)
    (x : (towerPadicField z u.1).Carrierˣ) :
    quasicharacterAt u.1 (residuePrime_eq z u.1)
        ((HeckeCharacter.normComp α * Φ).finiteComponent u.1) x =
      quasicharacterAt u.1 (residuePrime_eq z u.1) (Φ.finiteComponent u.1) x *
        quasicharacterBase z (α.finiteComponent z) (Units.map
          (@Algebra.norm (padicField z).Carrier (towerPadicField z u.1).Carrier _ _
            (Weil.Local.extensionAlgebra (padicField z) (towerPadicField z u.1)
              (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z u.1))) x) := by
  have : u.1.asIdeal.LiesOver z.asIdeal := u.2
  change ((HeckeCharacter.normComp α * Φ).finiteComponent u.1) x =
    (Φ.finiteComponent u.1) x * (α.finiteComponent z) (Units.map
      (@Algebra.norm (padicField z).Carrier (towerPadicField z u.1).Carrier _ _
        (Weil.Local.extensionAlgebra (padicField z) (towerPadicField z u.1)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z u.1))) x)
  rw [HeckeCharacter.finiteComponent_mul, ContinuousMonoidHom.mul_apply,
    HeckeCharacter.normComp_finiteComponent α z u x, localUnitNorm_eq_units_map_norm, mul_comm]


include heC in
/-- **Unramified places.** At a place `z` where every place of every `K j` above `z` has
ramification index one, and the characters are `(α ∘ N) · Φ` with `Φ` unramified there, the
epsilon product of the local relation is `1`, for every `α`. -/
theorem placeEpsilonRatioProduct_eq_one_of_unramified
    (hrel : LocalPlaceRelation.{u, w} r K Λ₁ Λ₂ z eC) (α : HeckeCharacter k)
    (Φ₁ Φ₂ : ∀ j, HeckeCharacter (K j))
    (hΛ₁ : ∀ j, Λ₁ j = HeckeCharacter.normComp α * Φ₁ j)
    (hΛ₂ : ∀ j, Λ₂ j = HeckeCharacter.normComp α * Φ₂ j)
    (hram : ∀ j (u : FinitePlacesAbove (K j) z), u.1.asIdeal.ramificationIdx (𝓞 k) = 1)
    (hunr : ∀ j (u : FinitePlacesAbove (K j) z),
      (Φ₁ j).IsUnramifiedAt u.1 ∧ (Φ₂ j).IsUnramifiedAt u.1)
    (ψz : NontrivialAdditiveCharacter (padicField z))
    (μ : ∀ j : (Σ j, FinitePlacesAbove (K j) z),
      LocalAdditiveHaarMeasure (towerPadicField z j.2.1)) :
    placeEpsilonRatioProduct r K Λ₁ Λ₂ z ψz μ = 1 := by
  let E : (Σ j, FinitePlacesAbove (K j) z) → PadicField (residuePrime z) :=
    fun j => towerPadicField z j.2.1
  let η₁ : ∀ j, Correspondence.QuasiCharacter (E j) := fun j =>
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₁ j.1).finiteComponent j.2.1)
  let η₂ : ∀ j, Correspondence.QuasiCharacter (E j) := fun j =>
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₂ j.1).finiteComponent j.2.1)
  refine prod_epsilon_ratio_eq_one_of_unramified (padicField z) eC heC E
    (fun j => ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1)
    η₁ η₂ (fun j => r j.1) hrel (quasicharacterBase z (α.finiteComponent z)) (fun j => ?_) ψz μ
  have : j.2.1.asIdeal.LiesOver z.asIdeal := j.2.2
  refine ⟨ramificationIndex_towerPadicField_eq z j.2.1 (hram j.1 j.2),
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Φ₁ j.1).finiteComponent j.2.1),
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Φ₂ j.1).finiteComponent j.2.1),
    isUnramifiedQuasicharacter_quasicharacterAt j.2.1 _ (hunr j.1 j.2).1 _,
    isUnramifiedQuasicharacter_quasicharacterAt j.2.1 _ (hunr j.1 j.2).2 _, fun x => ?_,
    fun x => ?_⟩
  · change quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₁ j.1).finiteComponent j.2.1) x = _
    rw [hΛ₁]
    exact quasicharacterAt_normComp_mul z α (Φ₁ j.1) j.2 x
  · change quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₂ j.1).finiteComponent j.2.1) x = _
    rw [hΛ₂]
    exact quasicharacterAt_normComp_mul z α (Φ₂ j.1) j.2 x

/-- A character nontrivial on the principal units of level `r'` has conductor exponent larger than
`r'` in the canonical package of `k_z`. -/
theorem lt_multiplicativeConductor_quasicharacterBase
    (η : (FiniteCompletion k z)ˣ →ₜ* ℂˣ) (r' : ℕ) (hη : NontrivialOnPrincipalUnits z η r') :
    r' < (padicField z).canonicalTopologicalData.multiplicativeConductor
      (quasicharacterBase z η) :=
  lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits z η r' hη (p := residuePrime z) rfl

include heC in
/-- **Ramified places.** For a place `z`, a nontrivial additive character `ψz` and a conductor
bound `Kb`, there is `B` such that for every `α` with conductor exponent at least `B` at `z`, if
the characters are `(α ∘ N) · Φ` with conductor exponents of `Φ` at most `Kb` above `z`, the
epsilon product of the local relation is `1`. -/
theorem exists_bound_placeEpsilonRatioProduct_eq_one
    (ψz : NontrivialAdditiveCharacter (padicField z)) (Kb : ℕ) :
    ∃ B : ℕ, ∀ α : HeckeCharacter k,
      B ≤ (padicField z).canonicalTopologicalData.multiplicativeConductor
        (quasicharacterBase z (α.finiteComponent z)) →
      ∀ (Λ₁ Λ₂ Φ₁ Φ₂ : ∀ j, HeckeCharacter (K j)),
        LocalPlaceRelation.{u, w} r K Λ₁ Λ₂ z eC →
        (∀ j, Λ₁ j = HeckeCharacter.normComp α * Φ₁ j) →
        (∀ j, Λ₂ j = HeckeCharacter.normComp α * Φ₂ j) →
        (∀ j (u : FinitePlacesAbove (K j) z),
          (towerPadicField z u.1).canonicalTopologicalData.multiplicativeConductor
              (quasicharacterAt u.1 (residuePrime_eq z u.1) ((Φ₁ j).finiteComponent u.1)) ≤ Kb ∧
          (towerPadicField z u.1).canonicalTopologicalData.multiplicativeConductor
              (quasicharacterAt u.1 (residuePrime_eq z u.1) ((Φ₂ j).finiteComponent u.1)) ≤ Kb) →
        ∀ μ : ∀ j : (Σ j, FinitePlacesAbove (K j) z),
          LocalAdditiveHaarMeasure (towerPadicField z j.2.1),
          placeEpsilonRatioProduct r K Λ₁ Λ₂ z ψz μ = 1 := by
  obtain ⟨B, hB⟩ := exists_bound_prod_epsilon_ratio_eq_one_of_ramified (padicField z) eC heC
    (fun j : (Σ j, FinitePlacesAbove (K j) z) => towerPadicField z j.2.1)
    (fun j => ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) ψz Kb
  refine ⟨B, fun α hα Λ₁ Λ₂ Φ₁ Φ₂ hrel hΛ₁ hΛ₂ hcond μ => ?_⟩
  refine hB (quasicharacterBase z (α.finiteComponent z)) hα
    (fun j => quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₁ j.1).finiteComponent j.2.1))
    (fun j => quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₂ j.1).finiteComponent j.2.1))
    (fun j => r j.1) hrel (fun j => ?_) μ
  refine ⟨quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Φ₁ j.1).finiteComponent j.2.1),
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Φ₂ j.1).finiteComponent j.2.1),
    (hcond j.1 j.2).1, (hcond j.1 j.2).2, fun x => ?_, fun x => ?_⟩
  · change quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₁ j.1).finiteComponent j.2.1) x = _
    rw [hΛ₁]
    exact quasicharacterAt_normComp_mul z α (Φ₁ j.1) j.2 x
  · change quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₂ j.1).finiteComponent j.2.1) x = _
    rw [hΛ₂]
    exact quasicharacterAt_normComp_mul z α (Φ₂ j.1) j.2 x

end Langlands.LocalFactor.NonabelianBrauer
