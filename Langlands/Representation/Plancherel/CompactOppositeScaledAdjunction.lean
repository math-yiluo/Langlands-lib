import Langlands.Representation.Plancherel.OppositeIntertwiningScaledAdjunction

/-! # Compact-picture scaled adjunction and rescaled positive pairings -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction

open Aubert.General Induction StandardIntertwining

universe uG uV uJ

section Forms

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Rescale a complex sesquilinear form by a real scalar. -/
def scaledSesq (r : ℝ) (s : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) :
    V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := (r : ℂ) • s

@[simp] theorem scaledSesq_apply (r : ℝ) (s : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (v w : V) :
    scaledSesq r s v w = (r : ℂ) * s v w := rfl

/-- Nonnegative real rescaling preserves real nonnegative diagonal values. -/
theorem scaledSesq_self (r : ℝ) (hr : 0 ≤ r) (s : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hs : ∀ v, ∃ a : ℝ, 0 ≤ a ∧ s v v = (a : ℂ)) (v : V) :
    ∃ a : ℝ, 0 ≤ a ∧ scaledSesq r s v v = (a : ℂ) := by
  obtain ⟨a, ha, hv⟩ := hs v
  refine ⟨r * a, mul_nonneg hr ha, ?_⟩
  rw [scaledSesq_apply, hv, Complex.ofReal_mul]

/-- Positive real rescaling preserves nonzero diagonal values. -/
theorem scaledSesq_self_ne_zero (r : ℝ) (hr : 0 < r)
    (s : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (v : V) (hv : s v v ≠ 0) :
    scaledSesq r s v v ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hv

end Forms

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

/-- The actual compact-picture standard operators are adjoint up to the
positive comparison factor for arbitrary supplied compact Iwasawa data. -/
theorem compactPicture_adjunction_scaled [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace U'] [BorelSpace U']
    [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
    [MeasurableSpace (U'.subgroupOf U)] [BorelSpace (U'.subgroupOf U)]
    [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
    [MeasurableSpace (QuotientSpace (U := U') U)] [BorelSpace (QuotientSpace (U := U') U)]
    (hbot : U ⊓ U' = ⊥)
    (hrec : ∀ m : M, HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m *
      HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m = 1)
    {μM : Measure M} [SFinite μM] [μM.IsHaarMeasure] [μM.IsMulRightInvariant]
    {μU : Measure U} [IsHaarMeasure μU] [μU.Regular] [SFinite μU]
    {μU' : Measure U'} [IsHaarMeasure μU'] [μU'.Regular] [SFinite μU']
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
      hermitianAdjunctionScale K μM μU μU' •
      compactPictureHermitianPairing h K hK A b φ
        (compactIntertwiningOperator h' hU' hδ' K hP' hK hP'K ν hν hr' h hU hδ hP hPK hr
          χb A Jb φ') := by
  set f := (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χa A).symm φ
  set f' := (unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χb A).symm φ'
  have e₁ := eval_compactEquiv_symm h hU hδ K hP hK hPK ν hν hr χa φ
  have e₂ := eval_compactEquiv_symm h' hU' hδ' K hP' hK hP'K ν hν hr' χb φ'
  have hm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have key := setIntegral_inner_eq_scaled h hU h' hU' b (μM := μM) (χ₁ := χa.val.toMonoidHom)
    (χ₂ := χb.val.toMonoidHom) (hχ₁ := unramifiedCharacter_isOpen_ker ν χa)
    (hχ₂ := unramifiedCharacter_isOpen_ker ν χb) hbot K hK hPK hP'K hP hP' hr hr' hrec hχ
    hμI hμI' hρ hρ' (μ := RankinSelberg.normalizedCompactOpenHaar K hK)
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
    _ = hermitianAdjunctionScale K μM μU μU' •
        (∫ x in (K : Set G), b.inner (eval P (leviInflatedInducingRepresentation h hU
          (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f x)
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f') x)
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK)) := key
    _ = hermitianAdjunctionScale K μM μU μU' •
        (∫ k : K, b.inner (eval P (leviInflatedInducingRepresentation h hU
          (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f (k : G))
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f') (k : G))
          ∂(RankinSelberg.normalizedCompactOpenHaar K hK).comap Subtype.val) :=
        congrArg (fun z : ℂ => hermitianAdjunctionScale K μM μU μU' • z)
        (integral_subtype_comap hm (fun x => b.inner (eval P (leviInflatedInducingRepresentation
          h hU (A.twist χa.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χa))) f x)
          (eval P (leviInflatedInducingRepresentation h hU
            (A.twist χb.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χb))) (Jb f') x))).symm
    _ = _ := by
        apply congrArg (fun z : ℂ => hermitianAdjunctionScale K μM μU μU' • z)
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        exact congrArg₂ b.inner (e₁ k).symm rfl


end Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction
