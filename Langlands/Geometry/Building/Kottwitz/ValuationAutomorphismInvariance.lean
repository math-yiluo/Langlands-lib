import Langlands.FieldTheory.HenselianAutomorphismValuation
import Langlands.Geometry.Building.Kottwitz.NormalizedValuationStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction

/-! # Invariance of the normalized valuation under compatible automorphisms

Let `K` be the maximal unramified extension of a nonarchimedean local field `F` inside its
separable closure, and let `L/K` be a finite Galois subextension. A ring automorphism `τ` of
`L` that restricts to a ring automorphism `σ` of `K` preserves the spectral valuation of `L`
up to equivalence and preserves its integer normalization exactly. Neither `σ` nor `τ` has to
be linear over `K`.
-/

noncomputable section

universe u

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))

/-- The spectral valuation of `L` restricts to the spectral valuation of `K`. -/
theorem intermediateValuation_comap_algebraMap :
    (intermediateValuation F L).comap (algebraMap (UnramifiedClosure F) L) =
      fixedFieldValuation F := by
  ext a
  rfl

/-- Every ring automorphism of `K` preserves the spectral valuation of `K` up to equivalence. -/
theorem fixedFieldValuation_comap_ringEquiv_isEquiv
    (σ : UnramifiedClosure F ≃+* UnramifiedClosure F) :
    ((fixedFieldValuation F).comap (σ : UnramifiedClosure F →+* UnramifiedClosure F)).IsEquiv
      (fixedFieldValuation F) := by
  have := MaximalUnramified.valuationSubring_isHenselian F
  have := MaximalUnramified.residueField_isAlgClosed F
  have hK := MaximalUnramified.valuation_isEquiv F
  exact ((hK.comap (σ : UnramifiedClosure F →+* UnramifiedClosure F)).symm.trans
    (Langlands.FieldTheory.isEquiv_comap_ringEquiv (MaximalUnramified.valuation F) σ)).trans hK

/-- The spectral valuation of `K` is nontrivial. -/
theorem fixedFieldValuation_isNontrivial : (fixedFieldValuation F).IsNontrivial := by
  refine Valuation.isNontrivial_of_isEquiv (MaximalUnramified.valuation_isEquiv F) ?_
  obtain ⟨π, hπ⟩ := MaximalUnramified.valuation_surjective F
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  refine ⟨⟨π, ?_, ?_⟩⟩
  · rw [hπ]
    exact WithZero.coe_ne_zero
  · rw [hπ, ← WithZero.coe_one, Ne, WithZero.coe_inj, ← ofAdd_zero,
      Multiplicative.ofAdd.injective.eq_iff]
    omega

/-- The spectral valuation ring of `K` is Henselian. -/
theorem fixedFieldValuation_valuationSubring_isHenselian :
    HenselianLocalRing (fixedFieldValuation F).valuationSubring := by
  rw [← (Valuation.isEquiv_iff_valuationSubring _ _).mp (MaximalUnramified.valuation_isEquiv F)]
  exact MaximalUnramified.valuationSubring_isHenselian F

/-- On a finite Galois extension `L/K`, a ring automorphism of `L` compatible with a ring
automorphism of `K` preserves the spectral valuation up to equivalence. -/
theorem intermediateValuation_comap_ringEquiv_isEquiv
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (σ : UnramifiedClosure F ≃+* UnramifiedClosure F) (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap (UnramifiedClosure F) L a) =
      algebraMap (UnramifiedClosure F) L (σ a)) :
    ((intermediateValuation F L).comap (τ : L →+* L)).IsEquiv (intermediateValuation F L) := by
  have h₁ := intermediateValuation_comap_algebraMap F L
  have h₂ : ((intermediateValuation F L).comap (τ : L →+* L)).comap
      (algebraMap (UnramifiedClosure F) L) =
      (fixedFieldValuation F).comap (σ : UnramifiedClosure F →+* UnramifiedClosure F) := by
    ext a
    simp only [Valuation.comap_apply, RingEquiv.coe_toRingHom, hτ]
    rw [← h₁, Valuation.comap_apply]
  have : HenselianLocalRing ((intermediateValuation F L).comap
      (algebraMap (UnramifiedClosure F) L)).valuationSubring := by
    rw [h₁]
    exact fixedFieldValuation_valuationSubring_isHenselian F
  refine (Langlands.FieldTheory.realValuation_isEquiv_of_comap_isEquiv
    (K := UnramifiedClosure F) (intermediateValuation F L)
    ((intermediateValuation F L).comap (τ : L →+* L)) ?_ ?_).symm
  · rw [h₁]
    exact fixedFieldValuation_isNontrivial F
  · rw [h₁, h₂]
    exact (fixedFieldValuation_comap_ringEquiv_isEquiv F σ).symm

/-- On a finite Galois extension `L/K`, a ring automorphism of `L` compatible with a ring
automorphism of `K` preserves the integer normalization of the spectral valuation. -/
theorem normalizedIntermediateValuation_ringEquiv_of_comm
    (hnorm : NormalizedIntermediateValuationStatement.{u})
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (σ : UnramifiedClosure F ≃+* UnramifiedClosure F) (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap (UnramifiedClosure F) L a) =
      algebraMap (UnramifiedClosure F) L (σ a))
    (x : L) :
    normalizedIntermediateValuation F L (τ x) = normalizedIntermediateValuation F L x := by
  obtain ⟨v, hv, huniq⟩ := hnorm F L
  have hspec := normalizedIntermediateValuation_spec F L ⟨v, hv⟩
  have hτv : IsNormalizedIntermediateValuation F L
      ((normalizedIntermediateValuation F L).comap (τ : L →+* L)) := by
    refine ⟨(hspec.1.comap (τ : L →+* L)).trans
      (intermediateValuation_comap_ringEquiv_isEquiv F L σ τ hτ), fun a => ?_⟩
    obtain ⟨y, hy⟩ := hspec.2 a
    exact ⟨τ.symm y, by
      rw [Valuation.comap_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, hy]⟩
  have h := (huniq _ hτv).trans (huniq _ hspec).symm
  exact DFunLike.congr_fun h x

/-- The unit order of the integer normalization is invariant under a ring automorphism of `L`
compatible with a ring automorphism of `K`. -/
theorem orderUnits_ringEquiv_of_comm
    (hnorm : NormalizedIntermediateValuationStatement.{u})
    [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L]
    (σ : UnramifiedClosure F ≃+* UnramifiedClosure F) (τ : L ≃+* L)
    (hτ : ∀ a, τ (algebraMap (UnramifiedClosure F) L a) =
      algebraMap (UnramifiedClosure F) L (σ a))
    (a : Lˣ) :
    IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map (τ : L →* L) a) =
      IntegerValuation.orderUnits (normalizedIntermediateValuation F L) a := by
  apply Multiplicative.toAdd.injective
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd]
  exact congrArg (fun z => -WithZero.log z)
    (normalizedIntermediateValuation_ringEquiv_of_comm F L hnorm σ τ hτ (a : L))

end Langlands.Geometry.Building.Kottwitz
