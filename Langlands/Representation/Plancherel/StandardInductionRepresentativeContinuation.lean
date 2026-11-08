import Langlands.Representation.Plancherel.StandardInductionSelfComparison
import Langlands.Representation.Plancherel.ContinuedIntertwiningNaturality

/-! # Continuation for equivalent inducing representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe uH uG uI uV uW

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (U' : Subgroup G) (e : H ≃ₜ* M)
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))
  {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

local notation "νM" =>
  (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
local notation "χM" => unramifiedCharactersHomeomorph e ν

/-- Equivalent inducing representations have exactly the same full integral
region, including original-carrier representability and with the same measure. -/
theorem standardIntertwiningFullDomainRegion_equiv
    (φ : A.representation.Equiv B.representation) :
    standardIntertwiningFullDomainRegion h hU U' e ν qν A =
      standardIntertwiningFullDomainRegion h hU U' e ν qν B := by
  apply Set.ext
  intro χ
  exact domain_eq_top_iff_equiv h hU U' qν
    (twistEquiv (χM χ).val.toMonoidHom φ)

variable {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- Naturality of the actual original families for an inducing equivalence.
Full-domain transport supplies the second membership proof. -/
theorem standardInductionIntertwinerFamily_representative_natural
    (φ : A.representation.Equiv B.representation)
    (χ : standardIntertwiningFullDomainRegion h hU U' e ν qν A)
    (f : UnramifiedLeviInduction h hU νM (χM χ.val) A) :
    standardInductionIntertwinerFamily h hU U' e ν qν h' hU'
        μU' μI hqν hM hsq B
        ⟨χ.val, (standardIntertwiningFullDomainRegion_equiv
          h hU U' e ν qν φ ▸ χ.property)⟩
        (inducedMap h hU (twistEquiv (χM χ.val).val.toMonoidHom φ).toIntertwiningMap f) =
      inducedMap h' hU' (twistEquiv (χM χ.val).val.toMonoidHom φ).toIntertwiningMap
        (standardInductionIntertwinerFamily h hU U' e ν qν h' hU'
          μU' μI hqν hM hsq A χ f) := by
  exact congrArg (fun T => T f)
    (fullSourceIntertwiner_natural
      (A := A.twist (χM χ.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (χM χ.val)))
      (B := B.twist (χM χ.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker νM (χM χ.val)))
      h hU h' hU' qν μU' μI hqν hM hsq
      χ.property _ (twistEquiv (χM χ.val).val.toMonoidHom φ).toIntertwiningMap)

variable (hδ : IsUnimodularModulus U hU) (hδ' : IsUnimodularModulus U' hU')
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr : Continuous h.projection) (hr' : Continuous h'.projection)
  (hν : ∀ i, Continuous (ν i))

set_option quotPrecheck false in
local notation "hνM" => (fun i => (hν i).comp e.symm.continuous)

/-- The actual standard integral family, restricted to the fixed compact
pictures and defined on its complete full-domain parameter region. -/
def standardCompactIntertwinerFamily (A : SmoothRep.{0, uG, uV} ℂ M)
    (χ : standardIntertwiningFullDomainRegion h hU U' e ν qν A) :
    CompactInductionPicture h K A →ₗ[ℂ] CompactInductionPicture h' K A :=
  compactIntertwiningOperator h hU hδ K hP hK hPK νM hνM hr
    h' hU' hδ' hP' hP'K hr' (χM χ.val) A
    (standardInductionIntertwinerFamily h hU U' e ν qν h' hU'
      μU' μI hqν hM hsq A χ)

/-- The actual compact square follows from naturality of the original integral;
no comparison square is supplied as an extra premise. -/
theorem standardCompactIntertwinerFamily_representative_natural
    (φ : A.representation.Equiv B.representation)
    (χ : standardIntertwiningFullDomainRegion h hU U' e ν qν A)
    (f : CompactInductionPicture h K A) :
    standardCompactIntertwinerFamily h hU U' e ν qν h' hU' μU' μI hqν hM hsq
        hδ hδ' K hK hP hP' hPK hP'K hr hr' hν B
        ⟨χ.val, (standardIntertwiningFullDomainRegion_equiv
          h hU U' e ν qν φ ▸ χ.property)⟩
        (compactInductionPictureEquiv h K φ f) =
      compactInductionPictureEquiv h' K φ
        (standardCompactIntertwinerFamily h hU U' e ν qν h' hU' μU' μI hqν hM hsq
          hδ hδ' K hK hP hP' hPK hP'K hr hr' hν A χ f) := by
  exact compactIntertwiningOperator_natural h hU hδ K hP hK hPK νM hνM hr
    h' hU' hδ' hP' hP'K hr' (χM χ.val) φ _ _
    (standardInductionIntertwinerFamily_representative_natural
      h hU U' e ν qν h' hU' μU' μI hqν hM hsq φ χ) f

/-- Construct continuation data for the actual equivalent inducing
representative, conjugating the global numerator and keeping its denominator. -/
def standardInductionRepresentativeContinuation
    (φ : A.representation.Equiv B.representation)
    (p : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h hU U' e ν qν A)
      (standardCompactIntertwinerFamily h hU U' e ν qν h' hU'
        μU' μI hqν hM hsq hδ hδ' K hK hP hP' hPK hP'K hr hr' hν A)) :
    RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h hU U' e ν qν B)
      (standardCompactIntertwinerFamily h hU U' e ν qν h' hU'
        μU' μI hqν hM hsq hδ hδ' K hK hP hP' hPK hP'K hr hr' hν B) where
  denominator := p.denominator
  denominator_nonzero χ := p.denominator_nonzero
    ⟨χ.val, (standardIntertwiningFullDomainRegion_equiv
      h hU U' e ν qν φ).symm ▸ χ.property⟩
  numerator χ := (compactInductionPictureEquiv h' K φ).toLinearMap.comp
    ((p.numerator χ).comp (compactInductionPictureEquiv h K φ).symm.toLinearMap)
  polynomial := (p.polynomial.precomp
    (compactInductionPictureEquiv h K φ).symm.toLinearMap).postcomp
      (compactInductionPictureEquiv h' K φ).toLinearMap
  clears χ := by
    apply LinearMap.ext
    intro f
    let χA : standardIntertwiningFullDomainRegion h hU U' e ν qν A :=
      ⟨χ.val, (standardIntertwiningFullDomainRegion_equiv
        h hU U' e ν qν φ).symm ▸ χ.property⟩
    have hn := standardCompactIntertwinerFamily_representative_natural
      h hU U' e ν qν h' hU' μU' μI hqν hM hsq
      hδ hδ' K hK hP hP' hPK hP'K hr hr' hν φ χA
      ((compactInductionPictureEquiv h K φ).symm f)
    rw [Representation.Equiv.apply_symm_apply] at hn
    change (compactInductionPictureEquiv h' K φ)
        (p.numerator χA.val ((compactInductionPictureEquiv h K φ).symm f)) = _
    rw [p.clears χA]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (fun z => p.denominator.val χ.val • z) hn.symm

local notation "transport" => standardInductionRepresentativeContinuation
  h hU U' e ν qν h' hU' μU' μI hqν hM hsq
  hδ hδ' K hK hP hP' hPK hP'K hr hr' hν

/-- The chosen whole-operator denominator is unchanged. -/
@[simp]
theorem standardInductionRepresentativeContinuation_denominator
    (φ : A.representation.Equiv B.representation)
    (p : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h hU U' e ν qν A)
      (standardCompactIntertwinerFamily h hU U' e ν qν h' hU'
        μU' μI hqν hM hsq hδ hδ' K hK hP hP' hPK hP'K hr hr' hν A)) :
    (transport φ p).denominator = p.denominator := rfl

/-- In particular, this transport has exactly the original regular region. -/
@[simp]
theorem standardInductionRepresentativeContinuation_regularRegion
    (φ : A.representation.Equiv B.representation)
    (p : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h hU U' e ν qν A)
      (standardCompactIntertwinerFamily h hU U' e ν qν h' hU'
        μU' μI hqν hM hsq hδ hδ' K hK hP hP' hPK hP'K hr hr' hν A)) :
    (transport φ p).regularRegion = p.regularRegion := rfl

/-- At every regular parameter, the continued operator is conjugated by the
same fixed compact equivalences used in the original actual integral square. -/
theorem standardInductionRepresentativeContinuation_continuedOperator
    (φ : A.representation.Equiv B.representation)
    (p : RationalOperatorContinuationData
      (standardIntertwiningFullDomainRegion h hU U' e ν qν A)
      (standardCompactIntertwinerFamily h hU U' e ν qν h' hU'
        μU' μI hqν hM hsq hδ hδ' K hK hP hP' hPK hP'K hr hr' hν A))
    (χ : p.regularRegion) :
    (transport φ p).continuedOperator χ =
      (compactInductionPictureEquiv h' K φ).toLinearMap.comp
        ((p.continuedOperator χ).comp
          (compactInductionPictureEquiv h K φ).symm.toLinearMap) := by
  apply LinearMap.ext
  intro f
  simp only [RationalOperatorContinuationData.continuedOperator,
    standardInductionRepresentativeContinuation, LinearMap.comp_apply,
    LinearMap.smul_apply, map_smul]

end Langlands.Plancherel
