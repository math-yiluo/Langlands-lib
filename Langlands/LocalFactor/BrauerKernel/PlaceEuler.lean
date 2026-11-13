import Langlands.LocalFactor.BrauerKernel.PlaceEpsilon
import Langlands.LocalFactor.BrauerKernel.LocalEuler
import Langlands.Global.Factors.RelativeWeilAssemblyGlobal
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof
import Langlands.VirtualRepresentation.ExactDual
import Langlands.Weil.Representation.CharacterLineDual

/-! # Local L-factors of a global relation at a finite place -/

noncomputable section

set_option autoImplicit false

universe u w

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open VirtualRepresentation CommonClosure Correspondence
open scoped NumberField

variable {k E' : Type u} [Field k] [NumberField k] [Field E'] [NumberField E'] [Algebra k E']
  {J : Type*} [Fintype J] (r : J → ℤ) (K : J → IntermediateField k E')
  (Λ₁ Λ₂ : ∀ j, HeckeCharacter (K j)) (z : Langlands.Global.FinitePlace k)

/-- The product of the quotients of the Hecke L-factors at the places above `z`, regrouped over
the pairs `(j, u)`. -/
def placeLFactorProduct (s : ℂ) : ℂ :=
  ∏ j : (Σ j, FinitePlacesAbove (K j) z),
    (heckeL (Λ₁ j.1) j.2.1 s / heckeL (Λ₂ j.1) j.2.1 s) ^ r j.1

/-- The local factor of the Brauer product package at `z` is the regrouped product. -/
theorem prod_heckeL_eq_placeLFactorProduct (s : ℂ) :
    (∏ i ∈ Finset.univ, ((∏ u ∈ placesAbove (K i) z, heckeL (Λ₁ i) u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (Λ₂ i) u s)⁻¹) ^ r i) =
      placeLFactorProduct r K Λ₁ Λ₂ z s := by
  unfold placeLFactorProduct
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [placesAbove, Finset.prod_map, Finset.prod_map, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun u _ => ?_
  rfl

/-- **Local L-factors.** If the local relation at `z` holds for a normalized family of `k_z`,
the regrouped product of quotients of Hecke L-factors is `1` wherever all the L-factors are
nonzero. -/
theorem placeLFactorProduct_eq_one (eC : ReciprocityFamily (padicField z))
    (heC : NormalizedReciprocity (padicField z) eC)
    (hrel : LocalPlaceRelation.{u, w} r K Λ₁ Λ₂ z eC) (s : ℂ)
    (hs : ∀ j : (Σ j, FinitePlacesAbove (K j) z),
      heckeL (Λ₁ j.1) j.2.1 s ≠ 0 ∧ heckeL (Λ₂ j.1) j.2.1 s ≠ 0) :
    placeLFactorProduct r K Λ₁ Λ₂ z s = 1 := by
  let E : (Σ j, FinitePlacesAbove (K j) z) → PadicField (residuePrime z) :=
    fun j => towerPadicField z j.2.1
  let η₁ : ∀ j, Correspondence.QuasiCharacter (E j) := fun j =>
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₁ j.1).finiteComponent j.2.1)
  let η₂ : ∀ j, Correspondence.QuasiCharacter (E j) := fun j =>
    quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) ((Λ₂ j.1).finiteComponent j.2.1)
  have hgeo : ∀ j, IsGeometricReciprocity (E j)
      (LocalClassField.extensionReciprocityCandidate (padicField z) (E j)
        (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) eC) := fun j =>
    (LocalClassField.commonClosureGeometricProof (residuePrime z) (padicField z) eC heC).2 (E j)
      (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1)
  have hL₁ : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η₁ j) s =
      heckeL (Λ₁ j.1) j.2.1 s := fun j =>
    lFactor_quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) _ s
  have hL₂ : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η₂ j) s =
      heckeL (Λ₂ j.1) j.2.1 s := fun j =>
    lFactor_quasicharacterAt j.2.1 (residuePrime_eq z j.2.1) _ s
  have h := Weil.Local.InertiaEuler.prod_lFactor_eq_one_of_relation (padicField z) E
    (fun j => ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z j.2.1) hgeo η₁ η₂
    (fun j => r j.1) hrel s (fun j => by rw [hL₁]; exact (hs j).1)
    (fun j => by rw [hL₂]; exact (hs j).2)
  unfold placeLFactorProduct
  rw [← h]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hL₁, hL₂]

/-- **Local factors of the Brauer package.** If the local relation at `z` holds, the weights are
nonzero and the local factor of the Brauer product at `z` is nonzero, it is `1`. -/
theorem prod_heckeL_eq_one_of_ne_zero (eC : ReciprocityFamily (padicField z))
    (heC : NormalizedReciprocity (padicField z) eC)
    (hrel : LocalPlaceRelation.{u, w} r K Λ₁ Λ₂ z eC) (hr : ∀ j, r j ≠ 0) (s : ℂ)
    (hne : (∏ i ∈ Finset.univ, ((∏ u ∈ placesAbove (K i) z, heckeL (Λ₁ i) u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (Λ₂ i) u s)⁻¹) ^ r i) ≠ 0) :
    (∏ i ∈ Finset.univ, ((∏ u ∈ placesAbove (K i) z, heckeL (Λ₁ i) u s) *
        (∏ u ∈ placesAbove (K i) z, heckeL (Λ₂ i) u s)⁻¹) ^ r i) = 1 := by
  rw [prod_heckeL_eq_placeLFactorProduct] at hne ⊢
  refine placeLFactorProduct_eq_one r K Λ₁ Λ₂ z eC heC hrel s fun j => ?_
  have hj := Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ _)
  have hq : heckeL (Λ₁ j.1) j.2.1 s / heckeL (Λ₂ j.1) j.2.1 s ≠ 0 := by
    intro h0
    rw [h0, zero_zpow _ (hr j.1)] at hj
    exact hj rfl
  refine ⟨left_ne_zero_of_mul hq, fun h0 => right_ne_zero_of_mul hq ?_⟩
  rw [h0, inv_zero]

/-- The Weil character of the component of `Λ⁻¹` is the inverse of that of `Λ`. -/
theorem weilCharacter_quasicharacterAt_inv {M : IntermediateField k E'} (Λ : HeckeCharacter M)
    (eC : ReciprocityFamily (padicField z)) (u : FinitePlacesAbove M z) :
    LocalFactor.RankOne.weilCharacter (towerPadicField z u.1)
        (LocalClassField.extensionReciprocityCandidate (padicField z) (towerPadicField z u.1)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z u.1) eC)
        (quasicharacterAt u.1 (residuePrime_eq z u.1) (Λ⁻¹.finiteComponent u.1)) =
      (LocalFactor.RankOne.weilCharacter (towerPadicField z u.1)
        (LocalClassField.extensionReciprocityCandidate (padicField z) (towerPadicField z u.1)
          (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom z u.1) eC)
        (quasicharacterAt u.1 (residuePrime_eq z u.1) (Λ.finiteComponent u.1)))⁻¹ :=
  DFunLike.ext _ _ fun _ => rfl

set_option maxHeartbeats 1000000 in
/-- **The dual local relation.** Applying the contragredient to the local relation gives the
local relation for the inverse characters. -/
theorem localPlaceRelation_inv (eC : ReciprocityFamily (padicField z))
    (hrel : LocalPlaceRelation.{u, w} r K Λ₁ Λ₂ z eC) :
    LocalPlaceRelation.{u, w} r K (fun j => (Λ₁ j)⁻¹) (fun j => (Λ₂ j)⁻¹) z eC := by
  unfold LocalPlaceRelation at hrel ⊢
  have h := congrArg ExactGrothendieckGroup.continuousDual hrel
  rw [map_zero] at h
  refine Eq.trans ?_ h
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Eq.trans ?_ (map_zsmul _ _ _).symm
  congr 1
  rw [ExactGrothendieckGroup.continuousDual_continuousInduceAlong,
    map_sub ExactGrothendieckGroup.continuousDual,
    ExactGrothendieckGroup.continuousDual_characterClass,
    ExactGrothendieckGroup.continuousDual_characterClass,
    ← weilCharacter_quasicharacterAt_inv z (Λ₁ j.1) eC j.2,
    ← weilCharacter_quasicharacterAt_inv z (Λ₂ j.1) eC j.2]

/-- The epsilon factor of the Brauer product package at `z`, at `s = 0`, is the epsilon product of
the place `z` for the standalone trace character of `ψz` and the transported self-dual measures. -/
theorem prod_finiteEpsilon_eq_placeEpsilonRatioProduct
    (ψf : ∀ v : Langlands.Global.FinitePlace k,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
        (topologicalData v).topology)
    (ψz : NontrivialAdditiveCharacter (padicField z))
    (hψf : ψf z = ofCanonicalCharacter z ψz)
    (μK : ∀ i (u : Langlands.Global.FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (topologicalData u) (traceComponents ψf u)) :
    (∏ i ∈ Finset.univ,
        ((∏ u ∈ placesAbove (K i) z, HeckeFunctionalEquation.finiteEpsilon (Λ₁ i)
            (traceComponents ψf) (μK i) u 0) *
          (∏ u ∈ placesAbove (K i) z, HeckeFunctionalEquation.finiteEpsilon (Λ₂ i)
            (traceComponents ψf) (μK i) u 0)⁻¹) ^ r i) =
      placeEpsilonRatioProduct r K Λ₁ Λ₂ z ψz
        (fun j => haarMeasureAt j.2.1 (residuePrime_eq z j.2.1) (μK j.1 j.2.1).val) := by
  unfold placeEpsilonRatioProduct
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← ClassField.Global.RelativeWeilGroup.prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon
      (K i) (Λ₁ i) ψf z ψz hψf (μK i) 0,
    ← ClassField.Global.RelativeWeilGroup.prod_epsilon_quasicharacterAt_eq_prod_finiteEpsilon
      (K i) (Λ₂ i) ψf z ψz hψf (μK i) 0,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_zpow]
  rfl

end Langlands.LocalFactor.NonabelianBrauer
