import Langlands.Global.PrimitiveAdelicMinimum
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Langlands.Global.AdelicFunctoriality.IdeleNormLift

/-! # Normalized adelic heights under the inclusion of adeles along a field extension -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField NNReal WithZero

universe u v

namespace Langlands.Global.AdelicFunctoriality

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

namespace FiniteExtension

/-- Raising the base of `WithZeroMulInt.toNNReal` to a positive power raises its values to
that power. -/
theorem toNNReal_pow_base {e : ℝ≥0} (he : e ≠ 0) {f : ℕ} (hf : f ≠ 0) (hef : e ^ f ≠ 0)
    (x : ℤᵐ⁰) : WithZeroMulInt.toNNReal hef x = WithZeroMulInt.toNNReal he x ^ f := by
  by_cases hx : x = 0
  · rw [WithZeroMulInt.toNNReal_pos_apply _ hx, WithZeroMulInt.toNNReal_pos_apply _ hx,
      zero_pow hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply _ hx, WithZeroMulInt.toNNReal_neg_apply _ hx,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem toNNReal_congr {e e' : ℝ≥0} (he : e ≠ 0) (he' : e' ≠ 0) (h : e = e') (x : ℤᵐ⁰) :
    WithZeroMulInt.toNNReal he x = WithZeroMulInt.toNNReal he' x := by
  subst h
  rfl

variable (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver p.asIdeal]

/-- The normalized absolute value of a completed embedding is the `e f`-th power of the
normalized absolute value below. -/
theorem norm_completionMap (x : p.adicCompletion K) :
    ‖completionMap p q x‖ =
      ‖x‖ ^ (q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K)) := by
  have hf : q.asIdeal.inertiaDeg (𝓞 K) ≠ 0 := (q.asIdeal.inertiaDeg_pos (𝓞 K)).ne'
  have hnorm : (Ideal.absNorm q.asIdeal : ℝ≥0) =
      (Ideal.absNorm p.asIdeal : ℝ≥0) ^ q.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← Ideal.absNorm_pow_inertiaDeg p.asIdeal q.asIdeal, Nat.cast_pow]
  have hpow : (Ideal.absNorm p.asIdeal : ℝ≥0) ^ q.asIdeal.inertiaDeg (𝓞 K) ≠ 0 :=
    pow_ne_zero _ (NumberField.HeightOneSpectrum.absNorm_ne_zero p)
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def,
    valuation_completionMap, map_pow,
    toNNReal_congr _ hpow hnorm,
    toNNReal_pow_base (NumberField.HeightOneSpectrum.absNorm_ne_zero p) hf hpow,
    ← pow_mul, mul_comm (q.asIdeal.inertiaDeg (𝓞 K)), NNReal.coe_pow]

end FiniteExtension

omit [NumberField K] [NumberField L] in
/-- The completed embedding at an infinite place is an isometry. -/
theorem norm_infiniteCompletionMap (q : InfinitePlace L)
    (x : (q.comap (algebraMap K L)).Completion) :
    ‖infiniteCompletionMap (algebraMap K L) q x‖ = ‖x‖ := by
  have hiso : Isometry (WithAbs.map (q.comap (algebraMap K L)).1 q.1 (algebraMap K L)) := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    rfl
  exact hiso.completion_map.norm_map_of_map_zero
    (map_zero (UniformSpace.Completion.mapRingHom _ hiso.continuous)) _

/-- A coordinatewise power law for maximum norms on finite coordinate vectors. -/
theorem pi_norm_eq_pow_of_forall {n : ℕ} {E E' : Fin n → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, SeminormedAddCommGroup (E' i)]
    (a : ∀ i, E i) (b : ∀ i, E' i) {d : ℕ} (hd : d ≠ 0)
    (h : ∀ i, ‖b i‖ = ‖a i‖ ^ d) : ‖b‖ = ‖a‖ ^ d := by
  have hnn : ∀ i, ‖b i‖₊ = ‖a i‖₊ ^ d := fun i => NNReal.eq (by simpa using h i)
  have hmono : Monotone (fun t : ℝ≥0 => t ^ d) := fun s t hst => pow_le_pow_left₀ s.2 hst d
  have hsup : Finset.univ.sup (fun i => ‖b i‖₊) = (Finset.univ.sup fun i => ‖a i‖₊) ^ d := by
    simp only [hnn]
    exact (Finset.apply_sup_eq_sup_comp_of_linearOrder (fun t : ℝ≥0 => t ^ d) hmono
      (by simp [zero_pow hd])).symm
  rw [← coe_nnnorm b, ← coe_nnnorm a, Pi.nnnorm_def, Pi.nnnorm_def, hsup, NNReal.coe_pow]

/-- The finite places above a finite place of `K` are finitely many, so the preimage of a
finite set of places of `K` is finite. -/
theorem finite_preimage_under {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (HeightOneSpectrum.under (𝓞 K) ⁻¹' S : Set (HeightOneSpectrum (𝓞 L))).Finite := by
  refine hS.preimage' fun p _ => ?_
  refine (Set.finite_range (fun q : FinitePlacesAbove L p => q.1)).subset ?_
  intro q hq
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
  subst hq
  exact ⟨⟨q, liesOver_under q⟩, rfl⟩

/-- A finitely supported product over finite places of `K`, pulled back to `L` and weighted
by `e f`, is the `[L : K]`-th power of the original product. -/
theorem finprod_under_pow (f : HeightOneSpectrum (𝓞 K) → ℝ)
    (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ q : HeightOneSpectrum (𝓞 L), f (q.under (𝓞 K)) ^
        (q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K)) =
      (∏ᶠ p, f p) ^ Module.finrank K L := by
  classical
  set d : HeightOneSpectrum (𝓞 L) → ℕ := fun q =>
    q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K) with hd
  set S := hf.toFinset with hS
  have hT := finite_preimage_under (K := K) (L := L) S.finite_toSet
  set T := hT.toFinset with hTdef
  have hsuppL : Function.mulSupport (fun q : HeightOneSpectrum (𝓞 L) =>
      f (q.under (𝓞 K)) ^ d q) ⊆ (T : Set _) := by
    intro q hq
    simp only [Function.mem_mulSupport] at hq
    simp only [hTdef, Set.Finite.coe_toFinset, Set.mem_preimage, hS, Set.Finite.coe_toFinset,
      Function.mem_mulSupport]
    intro h1
    exact hq (by rw [h1, one_pow])
  have hsuppK : Function.mulSupport f ⊆ (S : Set _) := by simp [hS]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsuppL,
    finprod_eq_prod_of_mulSupport_subset _ hsuppK, ← Finset.prod_pow]
  rw [← Finset.prod_fiberwise_of_maps_to (g := HeightOneSpectrum.under (𝓞 K)) (t := S)
    (fun q hq => by simpa [hTdef] using hq)]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Finset.prod_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2]),
    Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← finitePlacesAbove_sum_ramification_inertia (L := L) p]
  refine Finset.sum_subtype _ (fun q => ?_) d
  constructor
  · intro hq
    have h := (Finset.mem_filter.mp hq).2
    subst h
    exact liesOver_under q
  · intro hq
    have h : q.under (𝓞 K) = p := finitePlacesAbove_under p ⟨q, hq⟩
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    simp only [hTdef, Set.Finite.mem_toFinset, Set.mem_preimage, h]
    exact hp

open scoped NumberField.LiesOver in
/-- A product over infinite places of `L` of a function pulled back from `K`, weighted by
multiplicities, is the `[L : K]`-th power of the weighted product over `K`. -/
theorem prod_comap_pow_mult (f : InfinitePlace K → ℝ) :
    ∏ w : InfinitePlace L, f (w.comap (algebraMap K L)) ^ w.mult =
      (∏ v : InfinitePlace K, f v ^ v.mult) ^ Module.finrank K L := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L => w.comap (algebraMap K L)),
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hfib : ∀ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v},
      f (w.1.comap (algebraMap K L)) ^ w.1.mult = f v ^ w.1.mult := fun w => by rw [w.2]
  rw [Finset.prod_congr rfl (fun w _ => hfib w), Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 1
  have hiff : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v ↔ w.LiesOver v := by
    intro w
    constructor
    · intro h
      subst h
      exact ⟨rfl⟩
    · intro h
      exact InfinitePlace.LiesOver.comap_eq w v
  calc ∑ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v}, w.1.mult
      = ∑ w : InfinitePlacesAbove L v, w.1.mult :=
        Fintype.sum_equiv (Equiv.subtypeEquivRight hiff) _ _ (fun _ => rfl)
    _ = ∑ w : InfinitePlacesAbove L v,
          v.mult * Module.finrank v.Completion w.1.Completion := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact (InfinitePlace.mult_mul_finrank v w.1).symm
    _ = v.mult * Module.finrank K L := by
        rw [← Finset.mul_sum, infiniteLocalDegree_sum]

open PrimitiveAdelicHeight in
/-- **Height comparison.** For an adelic vector over `K` whose finite local norms are `1`
at almost all places, the normalized height of its image over `L` is the `[L : K]`-th power
of its normalized height over `K`. -/
theorem height_adeleInclusion {n : ℕ} (x : Fin n → Adeles K)
    (hx : (Function.mulSupport (finiteNorm K n x)).Finite) :
    height L n (fun i => adeleInclusion (x i)) = height K n x ^ Module.finrank K L := by
  have hfin : ∀ q : HeightOneSpectrum (𝓞 L),
      finiteNorm L n (fun i => adeleInclusion (x i)) q =
        finiteNorm K n x (q.under (𝓞 K)) ^
          (q.asIdeal.ramificationIdx (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 K)) := by
    intro q
    refine pi_norm_eq_pow_of_forall _ _
      (mul_ne_zero (q.asIdeal.ramificationIdx_pos (𝓞 K)).ne'
        (q.asIdeal.inertiaDeg_pos (𝓞 K)).ne') fun i => ?_
    exact FiniteExtension.norm_completionMap (q.under (𝓞 K)) q _
  have hinf : ∀ w : InfinitePlace L,
      infiniteNorm L n (fun i => adeleInclusion (x i)) w =
        infiniteNorm K n x (w.comap (algebraMap K L)) := by
    intro w
    have h := pi_norm_eq_pow_of_forall
      (fun i : Fin n => infiniteProjection K (w.comap (algebraMap K L)) (x i))
      (fun i : Fin n => infiniteProjection L w (adeleInclusion (x i))) one_ne_zero
      (fun i => by rw [pow_one]; exact norm_infiniteCompletionMap w _)
    simpa only [pow_one, infiniteNorm] using h
  simp only [height]
  rw [mul_pow, finprod_congr hfin, finprod_under_pow _ hx, Finset.prod_congr rfl
    (fun w _ => by rw [hinf w]), prod_comap_pow_mult]

end Langlands.Global.AdelicFunctoriality
