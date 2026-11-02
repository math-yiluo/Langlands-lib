import Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.UniformRing

/-! # Transport of actual curve-place completions -/

noncomputable section

universe u

open IsDedekindDomain Topology WithZero

namespace Langlands.Global

private theorem uniformContinuous_of_valuation_preserving
    {A B Γ : Type*} [Field A] [Field B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (f : A ≃+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f.toAddMonoidHom ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ :=
    Valuation.exists_div_eq_of_unit (Valued.v : Valuation B Γ) γ
  have hvr : Valued.v (f.symm r) = (Valued.v r : Γ) := by
    simpa using (hf (f.symm r)).symm
  have hvs : Valued.v (f.symm s) = (Valued.v s : Γ) := by
    simpa using (hf (f.symm s)).symm
  have hr' : Valued.v.restrict (f.symm r) ≠ 0 := by
    apply ne_of_gt
    apply (Valuation.restrict_pos_iff _ _).mpr
    rwa [hvr]
  have hs' : Valued.v.restrict (f.symm s) ≠ 0 := by
    apply ne_of_gt
    apply (Valuation.restrict_pos_iff _ _).mpr
    rwa [hvs]
  refine ⟨Units.mk0 (Valued.v.restrict (f.symm r) /
    Valued.v.restrict (f.symm s)) (div_ne_zero hr' hs'), ?_⟩
  intro x hx
  change Valued.v.restrict (f x) < γ.1
  rw [← hr, lt_div_iff₀ ((Valuation.restrict_pos_iff _ _).mpr hs₀),
    ← map_mul, Valuation.restrict_lt_iff]
  change Valued.v.restrict x <
    Valued.v.restrict (f.symm r) / Valued.v.restrict (f.symm s) at hx
  rw [lt_div_iff₀ ((Valuation.restrict_pos_iff _ _).mpr (hvs ▸ hs₀)),
    ← map_mul, Valuation.restrict_lt_iff] at hx
  have hfx := hf (x * f.symm s)
  simpa only [map_mul, RingEquiv.apply_symm_apply, hvr, ← hfx] using hx

variable {k F F' : Type u} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F']

/-- An algebra equivalence transports each actual discrete curve place. -/
abbrev curvePlaceEquiv (e : F ≃ₐ[k] F') :
    AlgebraicCurve.Place k F ≃ AlgebraicCurve.Place k F' :=
  AlgebraicCurve.Place.congrEquiv e.toRingEquiv e.commutes

theorem curvePlaceEquiv_valuation (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) (x : F) :
    (curvePlaceEquiv e v).adicValuation (e x) = v.adicValuation x := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' := (map_ne_zero e).mpr hx
  have h :=
    AlgebraicCurve.Place.ord_congrRingEquiv e.toRingEquiv e.commutes v x
  unfold AlgebraicCurve.Place.ord at h
  have hl := neg_injective h
  rw [← exp_log ((curvePlaceEquiv e v).adicValuation_ne_zero hx'),
    ← exp_log (v.adicValuation_ne_zero hx)]
  exact congrArg exp hl

/-- The original field equivalence, with the two corresponding valuation topologies. -/
def curvePlaceWithValEquiv (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    WithVal v.adicValuation ≃+* WithVal (curvePlaceEquiv e v).adicValuation :=
  WithVal.congr _ _ e.toRingEquiv

theorem uniformContinuous_curvePlaceWithValEquiv
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    UniformContinuous (curvePlaceWithValEquiv e v) :=
  uniformContinuous_of_valuation_preserving _ (fun x =>
    curvePlaceEquiv_valuation e v x.ofVal)

theorem uniformContinuous_curvePlaceWithValEquiv_symm
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    UniformContinuous (curvePlaceWithValEquiv e v).symm :=
  uniformContinuous_of_valuation_preserving _ (fun x => by
    have h := curvePlaceEquiv_valuation e v (e.symm x.ofVal)
    change v.adicValuation (e.symm x.ofVal) =
      (curvePlaceEquiv e v).adicValuation x.ofVal
    simpa using h.symm)

/-- The induced equivalence on the underlying valued-field completions. -/
def curvePlaceValuedCompletionEquiv (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.adicValuation.Completion ≃+* (curvePlaceEquiv e v).adicValuation.Completion :=
  UniformSpace.Completion.mapRingEquiv (curvePlaceWithValEquiv e v)
    (uniformContinuous_curvePlaceWithValEquiv e v).continuous
    (uniformContinuous_curvePlaceWithValEquiv_symm e v).continuous

theorem continuous_curvePlaceValuedCompletionEquiv
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    Continuous (curvePlaceValuedCompletionEquiv e v) := by
  change Continuous (UniformSpace.Completion.map (curvePlaceWithValEquiv e v))
  exact UniformSpace.Completion.continuous_map

theorem continuous_curvePlaceValuedCompletionEquiv_symm
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    Continuous (curvePlaceValuedCompletionEquiv e v).symm := by
  change Continuous (UniformSpace.Completion.map (curvePlaceWithValEquiv e v).symm)
  exact UniformSpace.Completion.continuous_map

/-- The completion equivalence retains the actual completion topologies. -/
def curvePlaceValuedCompletionHomeomorph (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.adicValuation.Completion ≃ₜ (curvePlaceEquiv e v).adicValuation.Completion where
  toEquiv := (curvePlaceValuedCompletionEquiv e v).toEquiv
  continuous_toFun := continuous_curvePlaceValuedCompletionEquiv e v
  continuous_invFun := continuous_curvePlaceValuedCompletionEquiv_symm e v

theorem curvePlaceValuedCompletionEquiv_le_one_iff
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) (x : v.adicValuation.Completion) :
    Valued.v (curvePlaceValuedCompletionEquiv e v x) ≤ 1 ↔ Valued.v x ≤ 1 := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · have h := (curvePlaceValuedCompletionHomeomorph e v).isClosed_setOfPred_iff
      (Valued.isClopen_valuationSubring _) (Valued.isClopen_valuationSubring _)
    change IsClosed {a : v.adicValuation.Completion |
      Valued.v a ≤ 1 ↔ Valued.v (curvePlaceValuedCompletionEquiv e v a) ≤ 1} at h
    simpa only [iff_comm] using h
  · intro a
    change Valued.v (UniformSpace.Completion.map (curvePlaceWithValEquiv e v)
      (a : v.adicValuation.Completion)) ≤ 1 ↔ Valued.v (a : v.adicValuation.Completion) ≤ 1
    rw [UniformSpace.Completion.map_coe (uniformContinuous_curvePlaceWithValEquiv e v),
      Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
    change (curvePlaceEquiv e v).adicValuation (e a.ofVal) ≤ 1 ↔
      v.adicValuation a.ofVal ≤ 1
    rw [curvePlaceEquiv_valuation]

/-- The actual adic completions are canonically ring equivalent after changing presentation. -/
def curvePlaceCompletionCongr (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.heightOneSpectrum.adicCompletion F ≃+*
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletion F' :=
  (HeightOneSpectrum.adicCompletion.equiv F v.heightOneSpectrum).trans
    ((curvePlaceValuedCompletionEquiv e v).trans
      (HeightOneSpectrum.adicCompletion.equiv F' (curvePlaceEquiv e v).heightOneSpectrum).symm)

theorem continuous_curvePlaceCompletionCongr
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    Continuous (curvePlaceCompletionCongr e v) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _).comp
    ((continuous_curvePlaceValuedCompletionEquiv e v).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion _ _))

theorem continuous_curvePlaceCompletionCongr_symm
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    Continuous (curvePlaceCompletionCongr e v).symm :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion _ _).comp
    ((continuous_curvePlaceValuedCompletionEquiv_symm e v).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion _ _))

/-- The canonical local comparison is a homeomorphism for the existing topologies. -/
def curvePlaceCompletionHomeomorph (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.heightOneSpectrum.adicCompletion F ≃ₜ
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletion F' where
  toEquiv := (curvePlaceCompletionCongr e v).toEquiv
  continuous_toFun := continuous_curvePlaceCompletionCongr e v
  continuous_invFun := continuous_curvePlaceCompletionCongr_symm e v

theorem curvePlaceCompletionCongr_algebraMap
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) (x : F) :
    curvePlaceCompletionCongr e v (algebraMap F (v.heightOneSpectrum.adicCompletion F) x) =
      algebraMap F' ((curvePlaceEquiv e v).heightOneSpectrum.adicCompletion F') (e x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map (curvePlaceWithValEquiv e v)
    ((WithVal.toVal v.adicValuation x : WithVal v.adicValuation) :
      v.adicValuation.Completion) =
    ((WithVal.toVal (curvePlaceEquiv e v).adicValuation (e x) :
      WithVal (curvePlaceEquiv e v).adicValuation) :
        (curvePlaceEquiv e v).adicValuation.Completion)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_curvePlaceWithValEquiv e v)]
  rfl

theorem curvePlaceCompletionCongr_mem_integers_iff
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F)
    (x : v.heightOneSpectrum.adicCompletion F) :
    curvePlaceCompletionCongr e v x ∈
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletionIntegers F' ↔
        x ∈ v.heightOneSpectrum.adicCompletionIntegers F :=
  curvePlaceValuedCompletionEquiv_le_one_iff e v x.toCompletion

/-- The completion comparison respects the original constant-field structure. -/
def curvePlaceCompletionAlgEquiv (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.heightOneSpectrum.adicCompletion F ≃ₐ[k]
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletion F' where
  __ := curvePlaceCompletionCongr e v
  commutes' a := by
    change curvePlaceCompletionCongr e v
      (algebraMap k (v.heightOneSpectrum.adicCompletion F) a) = _
    rw [IsScalarTower.algebraMap_apply k F (v.heightOneSpectrum.adicCompletion F)]
    rw [curvePlaceCompletionCongr_algebraMap, e.commutes]
    exact (IsScalarTower.algebraMap_apply k F'
      ((curvePlaceEquiv e v).heightOneSpectrum.adicCompletion F') a).symm

/-- The canonical comparison restricts to the completed valuation rings. -/
def curvePlaceCompletionIntegersCongr (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.heightOneSpectrum.adicCompletionIntegers F ≃+*
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletionIntegers F' where
  toFun x := ⟨curvePlaceCompletionCongr e v x,
    (curvePlaceCompletionCongr_mem_integers_iff e v x).mpr x.property⟩
  invFun y := ⟨(curvePlaceCompletionCongr e v).symm y,
    (curvePlaceCompletionCongr_mem_integers_iff e v _).mp
      (((curvePlaceCompletionCongr e v).apply_symm_apply y).symm ▸ y.property)⟩
  left_inv x := Subtype.ext ((curvePlaceCompletionCongr e v).symm_apply_apply x)
  right_inv y := Subtype.ext ((curvePlaceCompletionCongr e v).apply_symm_apply y)
  map_mul' x y := Subtype.ext ((curvePlaceCompletionCongr e v).map_mul x y)
  map_add' x y := Subtype.ext ((curvePlaceCompletionCongr e v).map_add x y)

theorem coe_curvePlaceCompletionIntegersCongr
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F)
    (x : v.heightOneSpectrum.adicCompletionIntegers F) :
    (curvePlaceCompletionIntegersCongr e v x :
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletion F') =
        curvePlaceCompletionCongr e v x := rfl

/-- The restricted comparison respects the existing subspace topologies. -/
def curvePlaceCompletionIntegersHomeomorph
    (e : F ≃ₐ[k] F') (v : AlgebraicCurve.Place k F) :
    v.heightOneSpectrum.adicCompletionIntegers F ≃ₜ
      (curvePlaceEquiv e v).heightOneSpectrum.adicCompletionIntegers F' where
  toEquiv := (curvePlaceCompletionIntegersCongr e v).toEquiv
  continuous_toFun :=
    ((continuous_curvePlaceCompletionCongr e v).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_curvePlaceCompletionCongr_symm e v).comp continuous_subtype_val).subtype_mk _

end Langlands.Global
