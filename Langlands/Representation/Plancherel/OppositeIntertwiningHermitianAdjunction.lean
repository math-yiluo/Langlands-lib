import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionStatement
import Langlands.Representation.Plancherel.CompactNormalizedInductionDuality
import Langlands.Representation.Plancherel.StandardIntertwiningSourceFactors
import Langlands.Representation.Plancherel.LeviInvariantIwasawaExchange
import Langlands.Representation.Plancherel.SemidirectSourceHaarNormalization
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Analysis.Local.QuotientFactorization

/-! # Hermitian adjunction of two opposite standard intertwining integrals

Let `P = M U` and `P' = M U'` be two semidirect decompositions with the same Levi `M` and
`U ∩ U' = 1`, and let `K` be a compact open subgroup with `G = P K = P' K` whose
intersections with `P` and `P'` are stable under the Levi projections. Let `A` carry an
invariant positive definite Hermitian form `b`, and let `χ₁`, `χ₂` be characters of `M`
with `χ₂ = χ̄₁⁻¹`. Suppose `J f` represents the standard integral `∫_{U'} f(u' g) du'` of `f`
induced from `A ⊗ χ₁` on `P`, and `J' f'` represents `∫_U f'(u g) du` of `f'` induced from
`A ⊗ χ₂` on `P'`, in the weak sense of `StandardIntertwining.HasIntegral`. This module proves
`∫_K b(J f(k), f'(k)) dk = ∫_K b(f(k), J' f'(k)) dk`, and its compact-picture form.

Both sides equal Iwasawa integrals of the function `Θ(x) = b(f(x), f'(x))`: the left side is
`∫_K ∫_{U'} Θ(u' k)` and the right side `∫_K ∫_U Θ(u k)`. The function `Θ` is invariant under
left translation by `M` because the Haar half-moduli of `U` and `U'` on `M` multiply to one
and `χ̄₁ χ₂ = 1`. The two integrals then agree by
`LeviInvariantIwasawaExchange.integral_exchange`, which needs `M` unimodular.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction

open Aubert.General Induction StandardIntertwining Haar

universe uG uI uV uJ

/-! ### Quotients by a trivial subgroup -/

section TrivialQuotient

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (H : Subgroup Γ) (hbot : ∀ a : H, a = 1)

/-- Multiplication `H × Γ → Γ`, a homeomorphism when `H` is trivial. -/
def trivialProductHomeomorph : H × Γ ≃ₜ Γ where
  toFun p := (p.1 : Γ) * p.2
  invFun x := (1, x)
  left_inv p := Prod.ext (by simp [hbot p.1]) (by simp [hbot p.1])
  right_inv x := by simp
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

/-- The quotient chart `Γ ≃ₜ H \ Γ`, `x ↦ H x`, for a trivial subgroup `H`. -/
abbrev trivialQuotientChart : Γ ≃ₜ QuotientIntegration.LeftQuotient H :=
  QuotientIntegration.factorQuotientHomeomorph H id (trivialProductHomeomorph H hbot)
    fun _ => rfl

variable [T2Space Γ] [LocallyCompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (hH : IsClosed (H : Set Γ)) [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)]
  {μΓ : Measure Γ} [IsHaarMeasure μΓ] [μΓ.Regular] [SFinite μΓ]
  {μH : Measure H} [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH] [SFinite μH]
  {ν : Measure (QuotientIntegration.LeftQuotient H)}

include hH in
/-- A quotient measure compatible with Haar measures `μΓ` and `μH`, where `μH` gives the
trivial group mass one, is the image of `μΓ` under the quotient chart. -/
theorem measurePreserving_trivialQuotientChart (hμH : μH Set.univ = 1)
    (hν : QuotientIntegration.IsCompatible H μΓ μH ν) :
    MeasurePreserving (trivialQuotientChart H hbot) μΓ ν := by
  have hdirac : μH = Measure.dirac 1 := by
    ext s hs
    by_cases h1 : (1 : H) ∈ s
    · have hs' : s = Set.univ := Set.eq_univ_of_forall fun a => by rw [hbot a]; exact h1
      rw [hs', hμH, dirac_apply_of_mem (Set.mem_univ _)]
    · have hs' : s = ∅ := Set.eq_empty_of_forall_notMem fun a ha => h1 (by rwa [hbot a] at ha)
      rw [hs', measure_empty, measure_empty]
  have he' : ⇑(trivialProductHomeomorph H hbot) = Prod.snd :=
    funext fun p => by simp [trivialProductHomeomorph, hbot p.1]
  have hm : Measurable (trivialProductHomeomorph H hbot) := by
    rw [he']
    exact measurable_snd
  have hprod : MeasurePreserving (trivialProductHomeomorph H hbot) (μH.prod μΓ) μΓ := by
    refine ⟨hm, ?_⟩
    rw [hdirac, dirac_prod, Measure.map_map hm measurable_prodMk_left]
    have he : (trivialProductHomeomorph H hbot) ∘ Prod.mk (1 : H) = id := by
      funext x
      simp [trivialProductHomeomorph]
    rw [he, Measure.map_id]
  exact QuotientIntegration.IsCompatible.measurePreserving_factorQuotientHomeomorph H id
    (trivialProductHomeomorph H hbot) (fun _ => rfl) hH hν hprod

include hbot hH in
/-- Integrals over the quotient by a trivial subgroup are integrals over the group. -/
theorem integral_trivialQuotient (hμH : μH Set.univ = 1)
    (hν : QuotientIntegration.IsCompatible H μΓ μH ν)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : QuotientIntegration.LeftQuotient H → E) :
    ∫ q, F q ∂ν = ∫ x, F (Quotient.mk _ x) ∂μΓ :=
  ((measurePreserving_trivialQuotientChart H hbot hH hμH hν).integral_comp
    (trivialQuotientChart H hbot).measurableEmbedding F).symm

include hbot hH in
/-- Integrability over the quotient by a trivial subgroup is integrability over the group. -/
theorem integrable_trivialQuotient_iff (hμH : μH Set.univ = 1)
    (hν : QuotientIntegration.IsCompatible H μΓ μH ν)
    {E : Type*} [NormedAddCommGroup E] (F : QuotientIntegration.LeftQuotient H → E) :
    Integrable F ν ↔ Integrable (fun x => F (Quotient.mk _ x)) μΓ :=
  ((measurePreserving_trivialQuotientChart H hbot hH hμH hν).integrable_comp_emb
    (trivialQuotientChart H hbot).measurableEmbedding).symm

end TrivialQuotient

/-- The source Haar measure of a trivial intersection gives it mass one. -/
theorem sourceIntersectionHaar_univ {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))
    (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G))
    [MeasurableSpace (A.subgroupOf B)] [BorelSpace (A.subgroupOf B)] (hbot : A ⊓ B = ⊥) :
    OrderedSubgroupFactorization.sourceIntersectionHaar Q hQ A B hA hB Set.univ = 1 := by
  have h1 := OrderedSubgroupFactorization.sourceIntersectionHaar_mass Q hQ A B hA hB
  have hset : {a : A.subgroupOf B | a.val.val ∈ Q} = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    have ha : a.val.val ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨a.2, a.val.2⟩
    rw [hbot, Subgroup.mem_bot] at ha
    change a.val.val ∈ Q
    rw [ha]
    exact Q.one_mem
  rwa [hset] at h1

/-- Every element of the intersection subgroup `A.subgroupOf B` is trivial when
`A ⊓ B = ⊥`. -/
theorem subgroupOf_eq_one {G : Type uG} [Group G] {A B : Subgroup G} (hbot : A ⊓ B = ⊥)
    (a : A.subgroupOf B) : a = 1 := by
  have ha : a.val.val ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨a.2, a.val.2⟩
  rw [hbot, Subgroup.mem_bot] at ha
  exact Subtype.ext (Subtype.ext ha)

/-! ### The smooth functionals `b(v, -)` on a twist -/

section Functional

variable {M : Type uG} [Group M] [TopologicalSpace M] {A : SmoothRep.{0, uG, uV} ℂ M}

theorem twist_representation_apply (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) (m : M)
    (v : A) : (A.twist χ hχ).representation m v = (χ m : ℂ) • A.representation m v :=
  rfl

/-- For an invariant positive form `b` and a character `χ` with open kernel, the functional
`b(v, -)` is smooth for the twist of the representation by `χ`. The form `b` itself need not be
invariant under the twist. -/
theorem rightFunctional_mem_smoothVectors_twist (b : InvariantPositiveForm A.representation)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M)) (v : A) :
    b.rightFunctional v ∈ smoothVectors (Langlands.twist χ A.representation).dual := by
  obtain ⟨L, hL⟩ := A.isSmooth v
  let Z : OpenSubgroup M :=
    { toSubgroup := L.toSubgroup ⊓ χ.ker, isOpen' := L.isOpen.inter hχ }
  refine ⟨Z, fun k => ?_⟩
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp k.2
  have hv : A.representation (k : M) v = v := hL ⟨(k : M), hk1⟩
  have hχk : χ (k : M) = 1 := hk2
  apply LinearMap.ext
  intro w
  change b.inner v (Langlands.twist χ A.representation (k : M)⁻¹ w) = b.inner v w
  have htw : Langlands.twist χ A.representation (k : M)⁻¹ w =
      A.representation (k : M)⁻¹ w := by
    change ((χ (k : M)⁻¹ : ℂˣ) : ℂ) • A.representation (k : M)⁻¹ w = _
    rw [map_inv, hχk, inv_one, Units.val_one, one_smul]
  rw [htw, ← b.invariant (k : M) v (A.representation (k : M)⁻¹ w),
    Representation.self_inv_apply, hv]

/-- The smooth functional `b(v, -)` on the twist by `χ`. -/
def twistFunctional (b : InvariantPositiveForm A.representation) (χ : M →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set M)) (v : A) : SmoothDual (A.twist χ hχ).representation :=
  ⟨b.rightFunctional v, rightFunctional_mem_smoothVectors_twist b χ hχ v⟩

@[simp]
theorem twistFunctional_apply (b : InvariantPositiveForm A.representation) (χ : M →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set M)) (v w : A) :
    (twistFunctional b χ hχ v).val w = b.inner v w :=
  rfl

theorem inner_smul_smul (b : InvariantPositiveForm A.representation) (a c : ℂ) (v w : A) :
    b.inner (a • v) (c • w) = starRingEnd ℂ a * c * b.inner v w := by
  let := b.toInnerProductCore
  rw [b.smul_left, show b.inner v (c • w) = c * b.inner v w from
    InnerProductSpace.Core.inner_smul_right _ _, mul_assoc]

theorem conj_inner (b : InvariantPositiveForm A.representation) (v w : A) :
    starRingEnd ℂ (b.inner v w) = b.inner w v :=
  b.conj_inner_symm w v

end Functional

/-- Complex conjugation preserves integrability. -/
theorem integrable_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : X → ℂ}
    (hF : Integrable F μ) : Integrable (fun x => starRingEnd ℂ (F x)) μ :=
  hF.mono (Complex.continuous_conj.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    (ae_of_all _ fun x => by rw [Complex.norm_conj])

/-! ### The function `Θ = b(f, f')` -/

section Integrand

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U P' U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  {A : SmoothRep.{0, uG, uV} ℂ M} (b : InvariantPositiveForm A.representation)
  {χ₁ χ₂ : M →* ℂˣ} {hχ₁ : IsOpen (χ₁.ker : Set M)} {hχ₂ : IsOpen (χ₂.ker : Set M)}

/-- The function `Θ(x) = b(f(x), f'(x))` of a Levi-normalized section `f` for `P`, inducing
`A ⊗ χ₁`, and a Levi-normalized section `f'` for `P'`, inducing `A ⊗ χ₂`. -/
def hermitianIntegrand
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂))
    (x : G) : ℂ :=
  b.inner (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f x)
    (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' x)

/-- `Θ` is invariant under left translation by `M` when the Haar moduli of `U` and `U'` on `M`
multiply to one and `χ̄₁ χ₂ = 1`. -/
theorem hermitianIntegrand_levi_mul
    (hrec : ∀ m : M, HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m *
      HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m = 1)
    (hχ : ∀ m : M, starRingEnd ℂ (χ₁ m : ℂ) * (χ₂ m : ℂ) = 1)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂))
    (m : M) (x : G) :
    hermitianIntegrand h hU h' hU' b f f' ((m : G) * x) =
      hermitianIntegrand h hU h' hU' b f f' x := by
  have hc := (leviInflated_covariant_iff h hU (A.twist χ₁ hχ₁)
    (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f)).mp f.1.2 m 1 x
  have hc' := (leviInflated_covariant_iff h' hU' (A.twist χ₂ hχ₂)
    (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f')).mp f'.1.2 m 1 x
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
      starRingEnd ℂ ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
          (χ₁ m : ℂ)) *
        ((HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer m : ℂ) * (χ₂ m : ℂ)) =
        1 := by
    rw [e₁, e₂, map_mul, Complex.conj_ofReal, mul_mul_mul_comm, ← Complex.ofReal_mul,
      ← NNReal.coe_mul, hδ, hχ m, NNReal.coe_one, Complex.ofReal_one, one_mul]
  unfold hermitianIntegrand
  rw [hc, hc', twist_representation_apply, twist_representation_apply, smul_smul, smul_smul,
    inner_smul_smul, b.invariant, hscalar, one_mul]

/-- `Θ` is invariant under right translation by an open subgroup. -/
theorem exists_hermitianIntegrand_mul_right
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂)) :
    ∃ L : OpenSubgroup G, ∀ x : G, ∀ k ∈ (L : Subgroup G),
      hermitianIntegrand h hU h' hU' b f f' (x * k) = hermitianIntegrand h hU h' hU' b f f' x := by
  obtain ⟨L₁, hL₁⟩ :=
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁)).isSmooth f
  obtain ⟨L₂, hL₂⟩ :=
    ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂)).isSmooth f'
  refine ⟨L₁ ⊓ L₂, fun x k hk => ?_⟩
  obtain ⟨hk₁, hk₂⟩ := OpenSubgroup.mem_inf.mp hk
  have e₁ : ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj
      (A.twist χ₁ hχ₁)).representation k f = f := hL₁ ⟨k, hk₁⟩
  have e₂ : ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
      (A.twist χ₂ hχ₂)).representation k f' = f' := hL₂ ⟨k, hk₂⟩
  unfold hermitianIntegrand
  rw [← leviInflatedInduction_right_translation h hU _ k f x,
    ← leviInflatedInduction_right_translation h' hU' _ k f' x, e₁, e₂]

variable [T2Space G]

/-- **Forward pointwise identity.** If `J f` represents the integral of `f` over the trivial
quotient `(U ∩ U') \ U'`, then `b(J f(g), f'(g)) = ∫_{U'} Θ(u' g) du'`, with integrability. -/
theorem forward_inner_eq [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
    {μI : Measure (U.subgroupOf U')} [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    {ν : Measure (QuotientSpace (U := U) U')}
    (hbot : U ⊓ U' = ⊥) (hμI : μI Set.univ = 1)
    (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂))
    {Jf : G → A} (hJ : HasIntegral h hU U' (A.twist χ₁ hχ₁) ν f Jf) (g : G) :
    Integrable (fun u' : U' => hermitianIntegrand h hU h' hU' b f f' ((u' : G) * g)) μU' ∧
      b.inner (Jf g) (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' g) =
        ∫ u' : U', hermitianIntegrand h hU h' hU' b f f' ((u' : G) * g) ∂μU' := by
  have : LocallyCompactSpace U' := hU'.locallyCompactSpace
  have : IsFiniteMeasure μI := ⟨by rw [hμI]; exact ENNReal.one_lt_top⟩
  have hbot' := subgroupOf_eq_one hbot
  have hH : IsClosed ((U.subgroupOf U' : Subgroup U') : Set U') :=
    hU.preimage continuous_subtype_val
  obtain ⟨hint, heq⟩ := hJ g (twistFunctional b χ₁ hχ₁
    (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' g))
  have hint' := (integrable_trivialQuotient_iff (U.subgroupOf U') hbot' hH hμI hν _).mp hint
  have heq' := integral_trivialQuotient (U.subgroupOf U') hbot' hH hμI hν
    (fun q => (twistFunctional b χ₁ hχ₁
      (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' g)).val
        (integrand h hU U' (A.twist χ₁ hχ₁) g f q))
  have hfun : (fun u' : U' => hermitianIntegrand h hU h' hU' b f f' ((u' : G) * g)) =
      fun u' => starRingEnd ℂ ((twistFunctional b χ₁ hχ₁
        (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' g)).val
          (integrand h hU U' (A.twist χ₁ hχ₁) g f (Quotient.mk _ u'))) := by
    funext u'
    rw [integrand_mk, twistFunctional_apply, conj_inner]
    unfold hermitianIntegrand
    rw [source_unipotent_invariant h' hU' (A.twist χ₂ hχ₂) f' u' g]
  rw [hfun]
  refine ⟨integrable_conj hint', ?_⟩
  rw [integral_conj, ← heq', heq, twistFunctional_apply, conj_inner]

/-- **Reverse pointwise identity.** If `J' f'` represents the integral of `f'` over the trivial
quotient `(U' ∩ U) \ U`, then `b(f(g), J' f'(g)) = ∫_U Θ(u g) du`, with integrability. -/
theorem reverse_inner_eq [MeasurableSpace U] [BorelSpace U]
    [MeasurableSpace (U'.subgroupOf U)] [BorelSpace (U'.subgroupOf U)]
    [MeasurableSpace (QuotientSpace (U := U') U)] [BorelSpace (QuotientSpace (U := U') U)]
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU]
    {μI' : Measure (U'.subgroupOf U)} [IsHaarMeasure μI'] [μI'.Regular] [IsMulRightInvariant μI']
    {ν' : Measure (QuotientSpace (U := U') U)}
    (hbot : U ⊓ U' = ⊥) (hμI' : μI' Set.univ = 1)
    (hν' : QuotientIntegration.IsCompatible (U'.subgroupOf U) μU μI' ν')
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (A.twist χ₁ hχ₁))
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂))
    {Jf' : G → A} (hJ' : HasIntegral h' hU' U (A.twist χ₂ hχ₂) ν' f' Jf') (g : G) :
    Integrable (fun u : U => hermitianIntegrand h hU h' hU' b f f' ((u : G) * g)) μU ∧
      b.inner (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f g) (Jf' g) =
        ∫ u : U, hermitianIntegrand h hU h' hU' b f f' ((u : G) * g) ∂μU := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : IsFiniteMeasure μI' := ⟨by rw [hμI']; exact ENNReal.one_lt_top⟩
  have hbot' := subgroupOf_eq_one ((inf_comm _ _).trans hbot)
  have hH : IsClosed ((U'.subgroupOf U : Subgroup U) : Set U) :=
    hU'.preimage continuous_subtype_val
  obtain ⟨hint, heq⟩ := hJ' g (twistFunctional b χ₂ hχ₂
    (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f g))
  have hint' := (integrable_trivialQuotient_iff (U'.subgroupOf U) hbot' hH hμI' hν' _).mp hint
  have heq' := integral_trivialQuotient (U'.subgroupOf U) hbot' hH hμI' hν'
    (fun q => (twistFunctional b χ₂ hχ₂
      (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f g)).val
        (integrand h' hU' U (A.twist χ₂ hχ₂) g f' q))
  have hfun : (fun u : U => hermitianIntegrand h hU h' hU' b f f' ((u : G) * g)) =
      fun u => (twistFunctional b χ₂ hχ₂
        (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f g)).val
          (integrand h' hU' U (A.twist χ₂ hχ₂) g f' (Quotient.mk _ u)) := by
    funext u
    rw [integrand_mk, twistFunctional_apply]
    unfold hermitianIntegrand
    rw [source_unipotent_invariant h hU (A.twist χ₁ hχ₁) f u g]
  rw [hfun]
  refine ⟨hint', ?_⟩
  rw [← heq', heq, twistFunctional_apply]

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G] in
include h in
/-- The Iwasawa factorization `g = m u k` obtained from `G = P K`. -/
theorem exists_levi_unipotent_compact (K : OpenSubgroup G)
    (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)) (g : G) :
    ∃ m : M, ∃ u : U, ∃ k ∈ (K : Subgroup G), g = (m : G) * u * k := by
  obtain ⟨p, k, rfl⟩ := hPK g
  refine ⟨h.projection p, ⟨_, h.projection_inv_mul_mem p⟩, k, k.2, ?_⟩
  show (p : G) * k = (h.projection p : G) * ((h.projection p : G)⁻¹ * p) * k
  rw [mul_inv_cancel_left]

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **The `K`-integral identity.** Let `K` be a compact open subgroup with `G = P K = P' K`
whose intersections with `P` and `P'` are stable under the Levi projections, let `μM` be a
left and right invariant measure on `M`, and let the Haar measures `μU`, `μU'` and the
left-invariant measure `μ` on `G` be arbitrary, with `M ∩ K`, `U ∩ K`, `U' ∩ K` of mass one.
If `J f` and `J' f'` represent the standard integrals of `f` and `f'` over the trivial
quotients `(U ∩ U') \ U'` and `(U' ∩ U) \ U`, then
`∫_K b(J f(k), f'(k)) dk = ∫_K b(f(k), J' f'(k)) dk`. -/
theorem setIntegral_inner_eq [MeasurableSpace M] [BorelSpace M]
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
    (hχ : ∀ m : M, starRingEnd ℂ (χ₁ m : ℂ) * (χ₂ m : ℂ) = 1)
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
    (f' : (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj (A.twist χ₂ hχ₂))
    {Jf Jf' : G → A} (hJ : HasIntegral h hU U' (A.twist χ₁ hχ₁) ν f Jf)
    (hJ' : HasIntegral h' hU' U (A.twist χ₂ hχ₂) ν' f' Jf') :
    ∫ x in (K : Set G), b.inner (Jf x)
        (eval P' (leviInflatedInducingRepresentation h' hU' (A.twist χ₂ hχ₂)) f' x) ∂μ =
      ∫ x in (K : Set G), b.inner
        (eval P (leviInflatedInducingRepresentation h hU (A.twist χ₁ hχ₁)) f x) (Jf' x) ∂μ := by
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology U' := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨L, hL⟩ := exists_hermitianIntegrand_mul_right h hU h' hU' b f f'
  have hc := LeviInvariantIwasawaExchange.continuous_of_mul_right_invariant L.isOpen
    (hermitianIntegrand h hU h' hU' b f f') hL
  have hfw := forward_inner_eq h hU h' hU' b hbot hμI hν f f' hJ
  have hrv := reverse_inner_eq h hU h' hU' b hbot hμI' hν' f f' hJ'
  have hint := LeviInvariantIwasawaExchange.integrable_iwasawaCoordinates (W := U')
    (K := (K : Subgroup G)) (μ := μ) (μW := μU') L.isOpen K.isOpen hK
    (hermitianIntegrand h hU h' hU' b f f') hL (fun k _ => (hfw k).1)
  have hex := (LeviInvariantIwasawaExchange.integral_exchange (M := M) (U := U) (V := U')
    (K := (K : Subgroup G)) (μ := μ) (μM := μM) (μU := μU) (μV := μU') K.isOpen
    h.levi_le_normalizer (exists_levi_unipotent_compact h K hPK)
    ((semidirect_compact_split_iff h (K : Subgroup G)).mpr hKsplit) hμU
    h'.levi_le_normalizer (exists_levi_unipotent_compact h' K hP'K)
    ((semidirect_compact_split_iff h' (K : Subgroup G)).mpr hK'split) hμU' hμM
    (hermitianIntegrand h hU h' hU' b f f') hc.measurable
    (hermitianIntegrand_levi_mul h hU h' hU' b hrec hχ f f') hint).2
  calc _ = ∫ k in (K : Set G), ∫ v : U', hermitianIntegrand h hU h' hU' b f f' ((v : G) * k)
          ∂μU' ∂μ :=
        setIntegral_congr_fun K.isOpen.measurableSet fun k _ => (hfw k).2
    _ = ∫ k in (K : Set G), ∫ u : U, hermitianIntegrand h hU h' hU' b f f' ((u : G) * k)
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
  {A : SmoothRep.{0, uG, uV} ℂ M} (b : InvariantPositiveForm A.representation)

omit [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- A compact-picture section is the restriction of its extension at any parameter. -/
theorem eval_compactEquiv_symm (χ : unramifiedCharacters ν)
    (φ : CompactInductionPicture h K A) (k : K) :
    eval _ _ φ k = eval _ _
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm φ) (k : G) := by
  conv_lhs =>
    rw [← (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).apply_symm_apply φ]
  rfl

/-- **Compact-picture Hermitian adjunction.** In the setting of `setIntegral_inner_eq`, let
`χa`, `χb` be unramified characters of `M` with `χ̄a χb = 1`, let `Ja` be an intertwiner from the
induction along `P` to the induction along `P'` at `χa` whose values represent the standard
integrals over `(U ∩ U') \ U'`, and let `Jb` go back from `P'` to `P` at `χb`, representing the
integrals over `(U' ∩ U) \ U`. Then their compact-picture forms are adjoint for the pairing
`∫_K b(·(k), ·(k)) dk`. -/
theorem compactPicture_adjunction [MeasurableSpace M] [BorelSpace M]
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
    (hχ : ∀ m : M, starRingEnd ℂ (χa.val m : ℂ) * (χb.val m : ℂ) = 1)
    (Ja : (UnramifiedLeviInduction h hU ν χa A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χa A).representation)
    (Jb : (UnramifiedLeviInduction h' hU' ν χb A).representation.IntertwiningMap
      (UnramifiedLeviInduction h hU ν χb A).representation)
    (hJa : ∀ f, HasIntegral h hU U'
      (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa)) ρ f
      (eval P' (leviInflatedInducingRepresentation h' hU'
        (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f)))
    (hJb : ∀ f', HasIntegral h' hU' U
      (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb)) ρ' f'
      (eval P (leviInflatedInducingRepresentation h hU
        (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f')))
    (φ : CompactInductionPicture h K A) (φ' : CompactInductionPicture h' K A) :
    compactPictureHermitianPairing h' K hK A b
        (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr h' hU' hδ' hP' hP'K hr'
          χa A Ja φ) φ' =
      compactPictureHermitianPairing h K hK A b φ
        (compactIntertwiningOperator h' hU' hδ' K hP' hK hP'K ν hν hr' h hU hδ hP hPK hr
          χb A Jb φ') := by
  set f := (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χa A).symm φ
  set f' := (unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χb A).symm φ'
  have e₁ := eval_compactEquiv_symm h hU hδ K hP hK hPK ν hν hr χa φ
  have e₂ := eval_compactEquiv_symm h' hU' hδ' K hP' hK hP'K ν hν hr' χb φ'
  have hm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have key := setIntegral_inner_eq h hU h' hU' b (χ₁ := χa.val.toMonoidHom)
    (χ₂ := χb.val.toMonoidHom) (hχ₁ := unramifiedCharacter_isOpen_ker ν χa)
    (hχ₂ := unramifiedCharacter_isOpen_ker ν χb) hbot K hK hPK hP'K hKsplit hK'split hrec hχ
    hμM hμU hμU' hμI hμI' hρ hρ' (μ := RankinSelberg.normalizedCompactOpenHaar K hK)
    f f' (hJa f) (hJb f')
  unfold compactPictureHermitianPairing CompactInduction.measure
  calc _ = ∫ k : K, b.inner (eval P' (leviInflatedInducingRepresentation h' hU'
          (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f) (k : G))
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) f' (k : G))
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        exact congrArg₂ b.inner rfl (e₂ k)
    _ = ∫ x in (K : Set G), b.inner (eval P' (leviInflatedInducingRepresentation h' hU'
          (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f) x)
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) f' x)
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK) :=
        integral_subtype_comap hm (fun x => b.inner (eval P' (leviInflatedInducingRepresentation
          h' hU' (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) (Ja f) x)
          (eval P' (leviInflatedInducingRepresentation h' hU'
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) f' x))
    _ = ∫ x in (K : Set G), b.inner (eval P (leviInflatedInducingRepresentation h hU
          (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f x)
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f') x)
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK) := key
    _ = ∫ k : K, b.inner (eval P (leviInflatedInducingRepresentation h hU
          (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f (k : G))
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f') (k : G))
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val :=
        (integral_subtype_comap hm (fun x => b.inner (eval P (leviInflatedInducingRepresentation
          h hU (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f x)
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f') x))).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        exact congrArg₂ b.inner (e₁ k).symm rfl

end Compact

end Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction
