import Langlands.Global.AdelicFunctoriality.Norm
import Mathlib.RingTheory.RamificationInertia.Basic

/-! # Surjectivity and the finite local-degree reduction -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct FiniteExtension Valued

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

theorem finiteAdicAbv_isNontrivial (q : HeightOneSpectrum (𝓞 L)) :
    (NumberField.HeightOneSpectrum.adicAbv L q).IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp q.ne_bot
  refine ⟨algebraMap (𝓞 L) L x,
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 L) L).not.mpr hx0, ?_⟩
  have hlt := (FinitePlace.norm_lt_one_iff_mem L q x).mpr hx
  rw [FinitePlace.norm_embedding] at hlt
  exact hlt.ne

theorem finiteAdicAbv_isEquiv_iff (q r : HeightOneSpectrum (𝓞 L)) :
    (NumberField.HeightOneSpectrum.adicAbv L q).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv L r) ↔ q = r := by
  refine ⟨fun h => ?_, fun h => h ▸ AbsoluteValue.IsEquiv.rfl⟩
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro x
  have hx := h.lt_one_iff (x := algebraMap (𝓞 L) L x)
  simpa only [← FinitePlace.norm_embedding,
    FinitePlace.norm_lt_one_iff_mem] using hx

def finiteWithAbsEmbedding (q : HeightOneSpectrum (𝓞 L)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv L q) →+* q.adicCompletion L :=
  (algebraMap L (q.adicCompletion L)).comp
    (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv L q)).toRingHom

theorem finiteWithAbsEmbedding_isometry (q : HeightOneSpectrum (𝓞 L)) :
    Isometry (finiteWithAbsEmbedding q) :=
  AddMonoidHomClass.isometry_of_norm _ fun x => by
    change ‖FinitePlace.embedding q
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv L q) x)‖ = ‖x‖
    rw [FinitePlace.norm_embedding]
    rfl

theorem finiteWithAbsEmbedding_denseRange (q : HeightOneSpectrum (𝓞 L)) :
    DenseRange (finiteWithAbsEmbedding q) := by
  apply (q.denseRange_algebraMap L).mono
  rintro _ ⟨y, rfl⟩
  exact ⟨(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv L q)).symm y, rfl⟩

theorem denseRange_finiteAbove (p : HeightOneSpectrum (𝓞 K)) :
    DenseRange (fun y : L => fun q : FinitePlacesAbove L p =>
      algebraMap L (q.1.adicCompletion L) y) := by
  have h := AbsoluteValue.denseRange_algebraMap_pi
    (v := fun q : FinitePlacesAbove L p => NumberField.HeightOneSpectrum.adicAbv L q.1)
    (fun q => finiteAdicAbv_isNontrivial q.1)
    (fun q r hqr h => hqr (Subtype.ext ((finiteAdicAbv_isEquiv_iff q.1 r.1).mp h)))
  have hd := DenseRange.piMap (fun q : FinitePlacesAbove L p =>
    finiteWithAbsEmbedding_denseRange q.1)
  exact hd.comp h (.piMap fun q => (finiteWithAbsEmbedding_isometry q.1).continuous)

theorem finiteTensorMap_surjective (p : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (finiteTensorMap (L := L) p) := by
  let f := (finiteTensorMap (L := L) p).toLinearMap
  have hd : DenseRange f := by
    apply (denseRange_finiteAbove (L := L) p).mono
    rintro _ ⟨y, rfl⟩
    exact ⟨1 ⊗ₜ[K] y, funext (finiteTensorMap_one_tmul p y)⟩
  change Function.Surjective f
  rw [← Set.range_eq_univ, ← f.coe_range, ← f.range.closed_of_finiteDimensional.closure_eq]
  exact hd.closure_range

theorem finiteLocalDegree_sum_le (p : HeightOneSpectrum (𝓞 K)) :
    (∑ q : FinitePlacesAbove L p,
      Module.finrank (p.adicCompletion K) (q.1.adicCompletion L)) ≤
        Module.finrank K L := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (finiteTensorMap (L := L) p).toLinearMap)
    (finiteTensorMap_surjective p)
  simpa only [Module.finrank_baseChange, Module.finrank_pi_fintype] using h

theorem finiteTensorMap_bijective_iff_degree_sum (p : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (finiteTensorMap (L := L) p) ↔
      (∑ q : FinitePlacesAbove L p,
        Module.finrank (p.adicCompletion K) (q.1.adicCompletion L)) =
          Module.finrank K L := by
  constructor
  · intro h
    have heq := (AlgEquiv.ofBijective (finiteTensorMap (L := L) p) h).toLinearEquiv.finrank_eq
    simpa only [Module.finrank_baseChange, Module.finrank_pi_fintype] using heq.symm
  · intro h
    apply OrzechProperty.bijective_of_surjective_of_finrank_le
      (finiteTensorMap (L := L) p).toLinearMap (finiteTensorMap_surjective p)
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype, h]

theorem finiteTensorMap_bijective_of_degree_lower_bound
    (p : HeightOneSpectrum (𝓞 K))
    (h : Module.finrank K L ≤ ∑ q : FinitePlacesAbove L p,
      Module.finrank (p.adicCompletion K) (q.1.adicCompletion L)) :
    Function.Bijective (finiteTensorMap (L := L) p) :=
  (finiteTensorMap_bijective_iff_degree_sum p).mpr
    (Nat.le_antisymm (finiteLocalDegree_sum_le p) h)

/-- Actual height-one primes above `p` are exactly the prime ideals above `p`. -/
def finitePlacesAboveEquivPrimesOver (p : HeightOneSpectrum (𝓞 K)) :
    FinitePlacesAbove L p ≃ p.asIdeal.primesOver (𝓞 L) where
  toFun q := ⟨q.1.asIdeal, q.1.isPrime, q.2⟩
  invFun q := ⟨⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q.2⟩, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The global fundamental identity, indexed by the actual finite places. -/
theorem finitePlacesAbove_sum_ramification_inertia (p : HeightOneSpectrum (𝓞 K)) :
    (∑ q : FinitePlacesAbove L p,
      q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K)) =
        Module.finrank K L := by
  let := Fintype.ofFinite (p.asIdeal.primesOver (𝓞 L))
  calc
    _ = ∑ q : p.asIdeal.primesOver (𝓞 L),
        q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) :=
      (finitePlacesAboveEquivPrimesOver (L := L) p).sum_comp _
    _ = Module.finrank (𝓞 K) (𝓞 L) :=
      Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 L)
    _ = Module.finrank K L := (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm

/-- Per-place lower bounds give bijectivity of the actual finite tensor map. -/
theorem finiteTensorMap_bijective_of_local_degree_bounds
    (p : HeightOneSpectrum (𝓞 K))
    (h : ∀ q : FinitePlacesAbove L p,
      q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K) ≤
        Module.finrank (p.adicCompletion K) (q.1.adicCompletion L)) :
    Function.Bijective (finiteTensorMap (L := L) p) := by
  apply finiteTensorMap_bijective_of_degree_lower_bound p
  rw [← finitePlacesAbove_sum_ramification_inertia (L := L) p]
  exact Finset.sum_le_sum fun q _ => h q

end Langlands.Global.AdelicFunctoriality
