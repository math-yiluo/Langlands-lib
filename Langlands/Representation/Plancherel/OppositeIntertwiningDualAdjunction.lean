import Langlands.Representation.Plancherel.OppositeIntertwiningHermitianAdjunction
import Langlands.Representation.Plancherel.DynamicOppositeContragredientScalar
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Representation.Smooth.Contragredient.LawsProof

/-! # Duality adjunction of two opposite standard intertwining integrals

Let `P = M U` and `P' = M U'` be two semidirect decompositions with the same Levi `M` and
`U ∩ U' = 1`, and let `K` be a compact open subgroup with `G = P K = P' K` whose
intersections with `P` and `P'` are stable under the Levi projections. Let `A` be a smooth
representation of `M` with smooth contragredient `Ǎ`, and let `χ₁`, `χ₂` be characters of `M`
with `χ₁ χ₂ = 1`. Suppose `J f` represents the standard integral `∫_{U'} f(u' g) du'` of `f`
induced from `A ⊗ χ₁` on `P`, and `J' f'` represents `∫_U f'(u g) du` of `f'` induced from
`Ǎ ⊗ χ₂` on `P'`, in the weak sense of `StandardIntertwining.HasIntegral`. This module proves
`∫_K f'(k)(J f(k)) dk = ∫_K (J' f'(k))(f(k)) dk`, and its compact-picture form for the pairing
`compactPictureDualPairing`.

Both sides equal Iwasawa integrals of the function `Θ(x) = f'(x)(f(x))`: the left side is
`∫_K ∫_{U'} Θ(u' k)` and the right side `∫_K ∫_U Θ(u k)`. The function `Θ` is invariant under
left translation by `M` because the Haar half-moduli of `U` and `U'` on `M` multiply to one,
`χ₁ χ₂ = 1`, and the contragredient pairing is `M`-invariant. The two integrals then agree by
`LeviInvariantIwasawaExchange.integral_exchange`, which needs `M` unimodular.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.Plancherel.OppositeIntertwiningDualAdjunction

open Aubert.General Induction StandardIntertwining Haar
open OppositeIntertwiningHermitianAdjunction

universe uG uV uJ

/-! ### Smooth functionals on twists -/

section Functional

variable {M : Type uG} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]

omit [IsTopologicalGroup M] in
/-- A smooth functional of a representation `ρ` is smooth for every twist of `ρ` by a
character with open kernel. -/
theorem mem_smoothVectors_dual_twist {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ M V} (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    {ℓ : Module.Dual ℂ V} (hℓ : ℓ ∈ smoothVectors ρ.dual) :
    ℓ ∈ smoothVectors (Langlands.twist χ ρ).dual := by
  change IsSmoothVector (Langlands.twist χ ρ).dual ℓ
  rw [dual_twist]
  exact (isSmoothVector_twist_iff χ⁻¹ ρ.dual (isOpen_ker_inv hχ) ℓ).mpr hℓ

variable {A : SmoothRep.{0, uG, uV} ℂ M}

/-- A smooth functional `ℓ` of `A`, viewed as a smooth functional of the twist `A ⊗ χ`. -/
def twistDualFunctional (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (ℓ : SmoothDual A.representation) : SmoothDual (A.twist χ hχ).representation :=
  ⟨ℓ.val, mem_smoothVectors_dual_twist χ hχ ℓ.property⟩

omit [IsTopologicalGroup M] in
@[simp]
theorem twistDualFunctional_apply (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (ℓ : SmoothDual A.representation) (v : A) :
    (twistDualFunctional χ hχ ℓ).val v = smoothDualPairing A.representation ℓ v :=
  rfl

/-- Evaluation `λ ↦ λ(v)` at a vector `v` of `A`, a smooth functional of the twist `Ǎ ⊗ χ` of
the smooth contragredient. -/
def twistEvaluationFunctional (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) (v : A) :
    SmoothDual (A.contragredient.twist χ hχ).representation :=
  ⟨(smoothBidual A.isSmooth v).val,
    mem_smoothVectors_dual_twist χ hχ (smoothBidual A.isSmooth v).property⟩

@[simp]
theorem twistEvaluationFunctional_apply (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) (v : A)
    (ℓ : SmoothDual A.representation) :
    (twistEvaluationFunctional χ hχ v).val ℓ = smoothDualPairing A.representation ℓ v :=
  rfl

/-- Under simultaneous action of `m`, the evaluation pairing of `Ǎ ⊗ χ₂` with `A ⊗ χ₁` picks
up the factor `χ₁(m) χ₂(m)`: the contragredient pairing itself is invariant. -/
theorem twistEvaluationFunctional_twist_apply (χ₁ χ₂ : M →* ℂˣ)
    (hχ₁ : IsOpen (χ₁.ker : Set M)) (hχ₂ : IsOpen (χ₂.ker : Set M)) (m : M) (a b : ℂ) (v : A)
    (ℓ : A.contragredient.twist χ₂ hχ₂) :
    (twistEvaluationFunctional (A := A) χ₂ hχ₂ (a • (A.twist χ₁ hχ₁).representation m v)).val
        (b • (A.contragredient.twist χ₂ hχ₂).representation m ℓ) =
      (a * (χ₁ m : ℂ)) * (b * (χ₂ m : ℂ)) * (twistEvaluationFunctional χ₂ hχ₂ v).val ℓ := by
  change smoothDualPairing A.representation
      (b • ((χ₂ m : ℂ) • smoothContragredient A.representation m ℓ))
      (a • ((χ₁ m : ℂ) • A.representation m v)) =
    (a * (χ₁ m : ℂ)) * (b * (χ₂ m : ℂ)) * smoothDualPairing A.representation ℓ v
  have hinv : smoothDualPairing A.representation
      (smoothContragredient A.representation m (ℓ : SmoothDual A.representation))
      (A.representation m v) = smoothDualPairing A.representation ℓ v :=
    smoothDualPairing_invariant (ρ := A.representation) m ℓ v
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hinv]
  ring

end Functional

/-! ### The function `Θ = f'(f)` -/

section Integrand

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U P' U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  {A : SmoothRep.{0, uG, uV} ℂ M}
  {χ₁ χ₂ : M →* ℂˣ} {hχ₁ : IsOpen (χ₁.ker : Set M)} {hχ₂ : IsOpen (χ₂.ker : Set M)}

/-- The function `Θ(x) = f'(x)(f(x))` of a Levi-normalized section `f` for `P`, inducing
`A ⊗ χ₁`, and a Levi-normalized section `f'` for `P'`, inducing `Ǎ ⊗ χ₂`. -/
def dualIntegrand
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂))
    (x : G) : ℂ :=
  (twistEvaluationFunctional (A := A) χ₂ hχ₂
    (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f x)).val
    (eval P' (leviInflatedInducingRepresentation h' hU' (A.contragredient.twist χ₂ hχ₂)) f' x)

/-- `Θ` is invariant under left translation by `M` when the Haar moduli of `U` and `U'` on `M`
multiply to one and `χ₁ χ₂ = 1`. -/
theorem dualIntegrand_levi_mul
    (hrec : ∀ m : M, HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m *
      HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m = 1)
    (hχ : ∀ m : M, (χ₁ m : ℂ) * (χ₂ m : ℂ) = 1)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂))
    (m : M) (x : G) :
    dualIntegrand h hU h' hU' f f' ((m : G) * x) = dualIntegrand h hU h' hU' f f' x := by
  have hc := (leviInflated_covariant_iff h hU (A.twist χ₁ hχ₁)
    (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f)).mp f.1.2 m 1 x
  have hc' := (leviInflated_covariant_iff h' hU' (A.contragredient.twist χ₂ hχ₂)
    (eval P' (leviInflatedInducingRepresentation h' hU' (A.contragredient.twist χ₂ hχ₂)) f')).mp
      f'.1.2 m 1 x
  rw [OneMemClass.coe_one, mul_one] at hc hc'
  have hδ : NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m : ℝ≥0) *
      NNReal.sqrt (HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m : ℝ≥0) =
        1 := by
    rw [← NNReal.sqrt_mul, ← Units.val_mul, hrec m, Units.val_one, NNReal.sqrt_one]
  have e₁ : (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) =
      ((NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m : ℝ≥0) :
        ℝ) : ℂ) := rfl
  have e₂ : (HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer m : ℂ) =
      ((NNReal.sqrt (HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m :
        ℝ≥0) : ℝ) : ℂ) := rfl
  have hscalar :
      ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) * (χ₁ m : ℂ)) *
        ((HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer m : ℂ) *
          (χ₂ m : ℂ)) = 1 := by
    rw [e₁, e₂, mul_mul_mul_comm, ← Complex.ofReal_mul, ← NNReal.coe_mul, hδ, hχ m,
      NNReal.coe_one, Complex.ofReal_one, one_mul]
  unfold dualIntegrand
  rw [hc, hc', twistEvaluationFunctional_twist_apply, hscalar, one_mul]

/-- `Θ` is invariant under right translation by an open subgroup. -/
theorem exists_dualIntegrand_mul_right
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂)) :
    ∃ L : OpenSubgroup G, ∀ x : G, ∀ k ∈ (L : Subgroup G),
      dualIntegrand h hU h' hU' f f' (x * k) = dualIntegrand h hU h' hU' f f' x := by
  obtain ⟨L₁, hL₁⟩ :=
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁)).isSmooth f
  obtain ⟨L₂, hL₂⟩ :=
    ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂)).isSmooth f'
  refine ⟨L₁ ⊓ L₂, fun x k hk => ?_⟩
  obtain ⟨hk₁, hk₂⟩ := OpenSubgroup.mem_inf.mp hk
  have e₁ : ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj
      (A.twist χ₁ hχ₁)).representation k f = f := hL₁ ⟨k, hk₁⟩
  have e₂ : ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂)).representation k f' = f' := hL₂ ⟨k, hk₂⟩
  unfold dualIntegrand
  rw [← leviInflatedInduction_right_translation h hU _ k f x,
    ← leviInflatedInduction_right_translation h' hU' _ k f' x, e₁, e₂]

variable [T2Space G]

/-- **Forward pointwise identity.** If `J f` represents the integral of `f` over the trivial
quotient `(U ∩ U') \ U'`, then `f'(g)(J f(g)) = ∫_{U'} Θ(u' g) du'`, with integrability. -/
theorem forward_pairing_eq [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {ν : Measure (QuotientSpace (U := U) U')}
    (hbot : U ⊓ U' = ⊥) (hμI : μI Set.univ = 1)
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂))
    {Jf : G → A} (hJ : HasIntegral h hU U' (A.twist χ₁ hχ₁) ν f Jf) (g : G) :
    Integrable (fun u' : U' => dualIntegrand h hU h' hU' f f' ((u' : G) * g)) μU' ∧
      smoothDualPairing A.representation
        (eval P' (leviInflatedInducingRepresentation h' hU' (A.contragredient.twist χ₂ hχ₂))
          f' g) (Jf g) =
        ∫ u' : U', dualIntegrand h hU h' hU' f f' ((u' : G) * g) ∂μU' := by
  have : LocallyCompactSpace U' := hU'.locallyCompactSpace
  have : IsFiniteMeasure μI := ⟨by rw [hμI]; exact ENNReal.one_lt_top⟩
  have hbot' := subgroupOf_eq_one hbot
  have hH : IsClosed ((U.subgroupOf U' : Subgroup U') : Set U') :=
    hU.preimage continuous_subtype_val
  set ℓ := twistDualFunctional χ₁ hχ₁
    (eval P' (leviInflatedInducingRepresentation h' hU' (A.contragredient.twist χ₂ hχ₂)) f' g)
  obtain ⟨hint, heq⟩ := hJ g ℓ
  have hint' := (integrable_trivialQuotient_iff (U.subgroupOf U') hbot' hH hμI hν _).mp hint
  have heq' := integral_trivialQuotient (U.subgroupOf U') hbot' hH hμI hν
    (fun q => ℓ.val (integrand h hU U' (A.twist χ₁ hχ₁) g f q))
  have hfun : (fun u' : U' => dualIntegrand h hU h' hU' f f' ((u' : G) * g)) =
      fun u' => ℓ.val (integrand h hU U' (A.twist χ₁ hχ₁) g f (Quotient.mk _ u')) := by
    funext u'
    rw [integrand_mk]
    unfold dualIntegrand
    rw [source_unipotent_invariant h' hU' (A.contragredient.twist χ₂ hχ₂) f' u' g]
    rfl
  rw [hfun]
  exact ⟨hint', heq.symm.trans heq'⟩

/-- **Reverse pointwise identity.** If `J' f'` represents the integral of `f'` over the trivial
quotient `(U' ∩ U) \ U`, then `(J' f'(g))(f(g)) = ∫_U Θ(u g) du`, with integrability. -/
theorem reverse_pairing_eq [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace (U'.subgroupOf U)] [BorelSpace (U'.subgroupOf U)]
    [MeasurableSpace (QuotientSpace (U := U') U)] [BorelSpace (QuotientSpace (U := U') U)]
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU]
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    {ν' : Measure (QuotientSpace (U := U') U)}
    (hbot : U ⊓ U' = ⊥) (hμI' : μI' Set.univ = 1)
    (hν' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ν')
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂))
    {Jf' : G → A.contragredient}
    (hJ' : HasIntegral h' hU' U (A.contragredient.twist χ₂ hχ₂) ν' f' Jf') (g : G) :
    Integrable (fun u : U => dualIntegrand h hU h' hU' f f' ((u : G) * g)) μU ∧
      smoothDualPairing A.representation (Jf' g)
        (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f g) =
        ∫ u : U, dualIntegrand h hU h' hU' f f' ((u : G) * g) ∂μU := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : IsFiniteMeasure μI' := ⟨by rw [hμI']; exact ENNReal.one_lt_top⟩
  have hbot' := subgroupOf_eq_one ((inf_comm _ _).trans hbot)
  have hH : IsClosed ((U'.subgroupOf U : Subgroup U) : Set U) :=
    hU'.preimage continuous_subtype_val
  set ℓ := twistEvaluationFunctional (A := A) χ₂ hχ₂
    (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f g)
  obtain ⟨hint, heq⟩ := hJ' g ℓ
  have hint' := (integrable_trivialQuotient_iff (U'.subgroupOf U) hbot' hH hμI' hν' _).mp hint
  have heq' := integral_trivialQuotient (U'.subgroupOf U) hbot' hH hμI' hν'
    (fun q => ℓ.val (integrand h' hU' U (A.contragredient.twist χ₂ hχ₂) g f' q))
  have hfun : (fun u : U => dualIntegrand h hU h' hU' f f' ((u : G) * g)) =
      fun u => ℓ.val (integrand h' hU' U (A.contragredient.twist χ₂ hχ₂) g f' (Quotient.mk _ u)) := by
    funext u
    rw [integrand_mk]
    unfold dualIntegrand
    rw [source_unipotent_invariant h hU (A.twist χ₁ hχ₁) f u g]
  rw [hfun]
  exact ⟨hint', heq.symm.trans heq'⟩

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **The `K`-integral identity.** Let `K` be a compact open subgroup with `G = P K = P' K`
whose intersections with `P` and `P'` are stable under the Levi projections, let `μM` be a
left and right invariant measure on `M`, and let the Haar measures `μU`, `μU'` and the
left-invariant measure `μ` on `G` be arbitrary, with `M ∩ K`, `U ∩ K`, `U' ∩ K` of mass one.
If `J f` and `J' f'` represent the standard integrals of `f` (inducing `A ⊗ χ₁` on `P`) and `f'`
(inducing `Ǎ ⊗ χ₂` on `P'`) over the trivial quotients `(U ∩ U') \ U'` and `(U' ∩ U) \ U`, and
`χ₁ χ₂ = 1`, then `∫_K f'(k)(J f(k)) dk = ∫_K (J' f'(k))(f(k)) dk`. -/
theorem setIntegral_pairing_eq [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (U'.subgroupOf U)] [BorelSpace (U'.subgroupOf U)]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    [MeasurableSpace (QuotientSpace (U := U') U)] [BorelSpace (QuotientSpace (U := U') U)]
    (hbot : U ⊓ U' = ⊥) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
    (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
    (hKsplit : ∀ p : P, (p : G) ∈ K → (h.projection p : G) ∈ K)
    (hK'split : ∀ p : P', (p : G) ∈ K → (h'.projection p : G) ∈ K)
    (hrec : ∀ m : M, HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m *
      HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m = 1)
    (hχ : ∀ m : M, (χ₁ m : ℂ) * (χ₂ m : ℂ) = 1)
    {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant] [μM.IsMulRightInvariant]
    (hμM : μM {m : M | (m : G) ∈ K} = 1)
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU]
    (hμU : μU {u : U | (u : G) ∈ K} = 1)
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    (hμU' : μU' {u : U' | (u : G) ∈ K} = 1)
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hμI : μI Set.univ = 1)
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    (hμI' : μI' Set.univ = 1)
    {ν : Measure (QuotientSpace (U := U) U')}
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    {ν' : Measure (QuotientSpace (U := U') U)}
    (hν' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ν')
    {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.contragredient.twist χ₂ hχ₂))
    {Jf : G → A} {Jf' : G → A.contragredient}
    (hJ : HasIntegral h hU U' (A.twist χ₁ hχ₁) ν f Jf)
    (hJ' : HasIntegral h' hU' U (A.contragredient.twist χ₂ hχ₂) ν' f' Jf') :
    ∫ x in (K : Set G), smoothDualPairing A.representation
        (eval P' (leviInflatedInducingRepresentation h' hU' (A.contragredient.twist χ₂ hχ₂))
          f' x) (Jf x) ∂μ =
      ∫ x in (K : Set G), smoothDualPairing A.representation (Jf' x)
        (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f x) ∂μ := by
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology U' := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨L, hL⟩ := exists_dualIntegrand_mul_right h hU h' hU' f f'
  have hc := LeviInvariantIwasawaExchange.continuous_of_mul_right_invariant L.isOpen
    (dualIntegrand h hU h' hU' f f') hL
  have hfw := forward_pairing_eq h hU h' hU' hbot hμI hν f f' hJ
  have hrv := reverse_pairing_eq h hU h' hU' hbot hμI' hν' f f' hJ'
  have hint := LeviInvariantIwasawaExchange.integrable_iwasawaCoordinates (W := U')
    (K := (K : Subgroup G)) (μ := μ) (μW := μU') L.isOpen K.isOpen hK
    (dualIntegrand h hU h' hU' f f') hL (fun k _ => (hfw k).1)
  have hex := (LeviInvariantIwasawaExchange.integral_exchange (M := M) (U := U) (V := U')
    (K := (K : Subgroup G)) (μ := μ) (μM := μM) (μU := μU) (μV := μU') K.isOpen
    h.levi_le_normalizer (exists_levi_unipotent_compact h K hPK)
    ((semidirect_compact_split_iff h (K : Subgroup G)).mpr hKsplit) hμU
    h'.levi_le_normalizer (exists_levi_unipotent_compact h' K hP'K)
    ((semidirect_compact_split_iff h' (K : Subgroup G)).mpr hK'split) hμU' hμM
    (dualIntegrand h hU h' hU' f f') hc.measurable
    (dualIntegrand_levi_mul h hU h' hU' hrec hχ f f') hint).2
  calc _ = ∫ k in (K : Set G), ∫ v : U', dualIntegrand h hU h' hU' f f' ((v : G) * k)
          ∂μU' ∂μ :=
        setIntegral_congr_fun K.isOpen.measurableSet fun k _ => (hfw k).2
    _ = ∫ k in (K : Set G), ∫ u : U, dualIntegrand h hU h' hU' f f' ((u : G) * k)
          ∂μU ∂μ := hex
    _ = _ := (setIntegral_congr_fun K.isOpen.measurableSet fun k _ => (hrv k).2).symm

end Integrand

/-! ### The compact-picture form -/

section Compact

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U P' U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {J : Type uJ} (ν : J → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)
  {A : SmoothRep.{0, uG, uV} ℂ M}

/-- **Compact-picture duality adjunction.** In the setting of `setIntegral_pairing_eq`, let
`χa`, `χb` be unramified characters of `M` with `χa χb = 1`, let `Ja` be an intertwiner from the
induction of `A` along `P` to that along `P'` at `χa` whose values represent the standard
integrals over `(U ∩ U') \ U'`, and let `Jb` go back from the induction of `Ǎ` along `P'` to
that along `P` at `χb`, representing the integrals over `(U' ∩ U) \ U`. Then their
compact-picture forms are adjoint for the pairing `compactPictureDualPairing`, that is
`∫_K φ'(k)((Ja φ)(k)) dk = ∫_K (Jb φ')(k)(φ(k)) dk`. -/
theorem compactPicture_dualAdjunction [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (U'.subgroupOf U)] [BorelSpace (U'.subgroupOf U)]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    [MeasurableSpace (QuotientSpace (U := U') U)] [BorelSpace (QuotientSpace (U := U') U)]
    (hbot : U ⊓ U' = ⊥)
    (hKsplit : ∀ p : P, (p : G) ∈ K → (h.projection p : G) ∈ K)
    (hK'split : ∀ p : P', (p : G) ∈ K → (h'.projection p : G) ∈ K)
    (hrec : ∀ m : M, HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m *
      HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m = 1)
    {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant] [μM.IsMulRightInvariant]
    (hμM : μM {m : M | (m : G) ∈ K} = 1)
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU]
    (hμU : μU {u : U | (u : G) ∈ K} = 1)
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    (hμU' : μU' {u : U' | (u : G) ∈ K} = 1)
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hμI : μI Set.univ = 1)
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    (hμI' : μI' Set.univ = 1)
    {ρ : Measure (QuotientSpace (U := U) U')}
    (hρ : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ρ)
    {ρ' : Measure (QuotientSpace (U := U') U)}
    (hρ' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ρ')
    (χa χb : unramifiedCharacters ν)
    (hχ : ∀ m : M, (χa.val m : ℂ) * (χb.val m : ℂ) = 1)
    (Ja : (UnramifiedLeviInduction h hU ν χa A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χa A).representation)
    (Jb : (UnramifiedLeviInduction h' hU' ν χb A.contragredient).representation.IntertwiningMap
      (UnramifiedLeviInduction h hU ν χb A.contragredient).representation)
    (hJa : ∀ f, HasIntegral h hU U'
      (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa)) ρ f
      (eval P' (leviInflatedInducingRepresentation h' hU'
        (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f)))
    (hJb : ∀ f', HasIntegral h' hU' U
      (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)) ρ' f'
      (eval P (leviInflatedInducingRepresentation h hU
        (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
          (Jb f')))
    (φ : CompactInductionPicture h K A) (φ' : CompactInductionPicture h' K A.contragredient) :
    compactPictureDualPairing h' K hK A
        (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
          χa A Ja φ) φ' =
      compactPictureDualPairing h K hK A φ
        (compactIntertwiningOperator h' hU' hδ' K hP' hK hP'K ν hν hr' h hU hδ hP hPK hr
          χb A.contragredient Jb φ') := by
  set f := (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χa A).symm φ
  set f' := (unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χb
    A.contragredient).symm φ'
  have e₁ := eval_compactEquiv_symm h hU hδ K hP hK hPK ν hν hr χa φ
  have e₂ := eval_compactEquiv_symm h' hU' hδ' K hP' hK hP'K ν hν hr' χb φ'
  have hm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have key := setIntegral_pairing_eq h hU h' hU' (χ₁ := χa.val.toMonoidHom)
    (χ₂ := χb.val.toMonoidHom) (hχ₁ := unramifiedCharacter_isOpen_ker ν χa)
    (hχ₂ := unramifiedCharacter_isOpen_ker ν χb) hbot K hK hPK hP'K hKsplit hK'split hrec hχ
    hμM hμU hμU' hμI hμI' hρ hρ' (μ := RankinSelberg.normalizedCompactOpenHaar K hK)
    f f' (hJa f) (hJb f')
  unfold compactPictureDualPairing CompactInduction.measure
  calc _ = ∫ k : K, smoothDualPairing A.representation
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
              f' (k : G))
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f) (k : G))
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        exact congrArg₂ (fun a b => smoothDualPairing A.representation a b) (e₂ k) rfl
    _ = ∫ x in (K : Set G), smoothDualPairing A.representation
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
              f' x)
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f) x)
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK) :=
        integral_subtype_comap hm (fun x => smoothDualPairing A.representation
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
              f' x)
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f) x))
    _ = ∫ x in (K : Set G), smoothDualPairing A.representation
          (eval P (leviInflatedInducingRepresentation h hU
            (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
              (Jb f') x)
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f x)
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK) := key
    _ = ∫ k : K, smoothDualPairing A.representation
          (eval P (leviInflatedInducingRepresentation h hU
            (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
              (Jb f') (k : G))
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f (k : G))
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val :=
        (integral_subtype_comap hm (fun x => smoothDualPairing A.representation
          (eval P (leviInflatedInducingRepresentation h hU
            (A.contragredient.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)))
              (Jb f') x)
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f x))).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        exact congrArg₂ (fun a b => smoothDualPairing A.representation a b) rfl (e₁ k).symm

end Compact

end Langlands.Plancherel.OppositeIntertwiningDualAdjunction
