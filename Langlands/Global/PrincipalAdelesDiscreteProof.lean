import Langlands.Global.AdeleQuotientStatement

/-!
# Discreteness and closedness of the principal adeles

Proof of `Langlands.Global.PrincipalAdelesDiscreteStatement`. See
`PrincipalAdelesDiscreteProof.md`.
-/

noncomputable section

open scoped RestrictedProduct

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- An element of `K` that is integral at every finite place and has absolute value `< 1` at
every infinite place is zero. -/
theorem eq_zero_of_forall_mem_adicCompletionIntegers_of_forall_lt_one {x : K}
    (hfin : ∀ v : FinitePlace K, (x : FiniteCompletion K v) ∈ v.adicCompletionIntegers K)
    (hinf : ∀ w : InfinitePlace K, w x < 1) : x = 0 := by
  obtain ⟨a, rfl⟩ : x ∈ (algebraMap (NumberField.RingOfIntegers K) K).range := by
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x fun v ↦ ?_
    have := hfin v
    rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_contra ha
  have ha' : a ≠ 0 := fun h ↦ ha (by simp [h])
  exact (NumberField.InfinitePlace.one_le_of_lt_one ha' fun z _ ↦ hinf z).not_gt (hinf w)

/-- The open neighbourhood of `0` in `𝔸_K` of adeles whose archimedean components have norm
`< 1` and whose finite components are integral. -/
def principalAdelesIsolatingSet : Set (Adeles K) :=
  {a | (∀ w : InfinitePlace K, ‖a.1 w‖ < 1) ∧
    ∀ v : FinitePlace K, a.2 v ∈ v.adicCompletionIntegers K}

/-- `principalAdelesIsolatingSet K` is open in the product of the archimedean and finite
restricted-product topologies. -/
theorem isOpen_principalAdelesIsolatingSet : IsOpen (principalAdelesIsolatingSet K) := by
  have h₁ : IsOpen {b : InfiniteAdeles K | ∀ w : InfinitePlace K, ‖b w‖ < 1} := by
    have : {b : InfiniteAdeles K | ∀ w : InfinitePlace K, ‖b w‖ < 1} =
        Set.pi Set.univ (fun w : InfinitePlace K ↦ Metric.ball (0 : w.Completion) 1) := by
      ext b
      exact ⟨fun h w _ ↦ mem_ball_zero_iff.mpr (h w),
        fun h w ↦ mem_ball_zero_iff.mp (h w (Set.mem_univ w))⟩
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun w _ ↦ Metric.isOpen_ball
  have h₂ : IsOpen {f : FiniteAdeles K | ∀ v : FinitePlace K,
      f v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem (fun v : FinitePlace K ↦ Valued.isOpen_valuationSubring _)
  exact h₁.prod h₂

/-- `principalAdelesIsolatingSet K` is a neighbourhood of `0`. -/
theorem zero_mem_principalAdelesIsolatingSet : (0 : Adeles K) ∈ principalAdelesIsolatingSet K :=
  ⟨fun w ↦ by
    change ‖(0 : w.Completion)‖ < 1
    simp, fun v ↦ (v.adicCompletionIntegers K).zero_mem⟩

/-- The only principal adele in `principalAdelesIsolatingSet K` is `0`. -/
theorem principalAdelesIsolatingSet_inter_principalAdeles :
    principalAdelesIsolatingSet K ∩ (principalAdeles K : Set (Adeles K)) = {0} := by
  ext a
  constructor
  · rintro ⟨⟨hinf, hfin⟩, x, rfl⟩
    have hx : x = 0 := by
      refine eq_zero_of_forall_mem_adicCompletionIntegers_of_forall_lt_one K
        (fun v ↦ hfin v) (fun w ↦ ?_)
      have h : w.1 x < 1 := by simpa [WithAbs.norm_toAbs_eq] using hinf w
      exact h
    simp [hx]
  · rintro rfl
    exact ⟨zero_mem_principalAdelesIsolatingSet K, (principalAdeles K).zero_mem⟩

/-- The principal adeles are a discrete subgroup of `𝔸_K`. -/
theorem principalAdeles_discreteTopology : DiscreteTopology (principalAdeles K) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_induced_iff.mpr
    ⟨principalAdelesIsolatingSet K, isOpen_principalAdelesIsolatingSet K, ?_⟩
  ext ⟨a, ha⟩
  have := Set.ext_iff.mp (principalAdelesIsolatingSet_inter_principalAdeles K) a
  simp only [Set.mem_inter_iff, SetLike.mem_coe, ha, and_true, Set.mem_singleton_iff] at this
  simp only [Set.mem_preimage, Set.mem_singleton_iff, this]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact congrArg Subtype.val h

/-- The adele ring of a number field is Hausdorff. -/
theorem adeles_t2Space : T2Space (Adeles K) := by
  have : T2Space (InfiniteAdeles K) :=
    inferInstanceAs (T2Space ((w : InfinitePlace K) → w.Completion))
  have : T2Space (FiniteAdeles K) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace K,
      [FiniteCompletion K v, v.adicCompletionIntegers K]))
  exact inferInstanceAs (T2Space (InfiniteAdeles K × FiniteAdeles K))

/-- The principal adeles are a closed subgroup of `𝔸_K`. -/
theorem principalAdeles_isClosed : IsClosed (principalAdeles K : Set (Adeles K)) := by
  have := adeles_t2Space K
  have := principalAdeles_discreteTopology K
  exact AddSubgroup.isClosed_of_discreteTopology

/-- Proof of the published statement that the principal adeles are discrete and closed. -/
theorem principalAdelesDiscrete : PrincipalAdelesDiscreteStatement K :=
  ⟨principalAdeles_discreteTopology K, principalAdeles_isClosed K⟩

end Langlands.Global
