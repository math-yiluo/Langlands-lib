import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.ProductCompactBaseChange
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Change of base representation for actual compact intertwining operators -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}

/-- A fixed equivalence of ordinary compact section spaces for a change of
base representation. Restoring the fixed twist is identity on vector values. -/
def compactInductionBaseChangeEquiv (τ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation) :
    (smoothInduced (P.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K A)).Equiv
      (smoothInduced (P.comap K.toSubgroup.subtype)
        (compactPictureInducingRepresentation h K B)) :=
  (smoothInducedEquiv _ (equivOfRepresentationEq
    (unramified_compactPictureInducing_eq h K hP hK ν hν hr τ A))).symm.trans
      (compactInductionPictureEquiv h K a)

omit [LocallyCompactSpace G] in
@[simp]
theorem compactInductionBaseChangeEquiv_eval (τ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation)
    (f : CompactInductionPicture h K A) (k : K) :
    eval _ _ (compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a f) k =
      a (eval _ _ f k) := rfl

variable (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- The actual normalized induction comparison restricts to one compact
map independent of the variable character. -/
theorem unramifiedLeviInductionCompactEquiv_baseChange
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation)
    (f : UnramifiedLeviInduction h hU ν (χ * τ) A) :
    unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B
        (inducedMap h hU (productBaseTwistEquiv ν τ χ a).toIntertwiningMap f) =
      compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a
        (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr (χ * τ) A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rfl

/-- The inverse compact restriction square, with the same actual induction
map and the same fixed compact base equivalence. -/
theorem unramifiedLeviInductionCompactEquiv_symm_baseChange
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation)
    (f : CompactInductionPicture h K A) :
    (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B).symm
        (compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a f) =
      inducedMap h hU (productBaseTwistEquiv ν τ χ a).toIntertwiningMap
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr (χ * τ) A).symm f) := by
  apply (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B).injective
  rw [LinearEquiv.apply_symm_apply, unramifiedLeviInductionCompactEquiv_baseChange,
    LinearEquiv.apply_symm_apply]

variable {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)

/-- An actual ambient square between translated parameters gives the fixed
compact base-change square. No standard-integral identification is needed. -/
theorem compactIntertwiningOperator_baseChange (τ χ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation)
    (JA : (UnramifiedLeviInduction h hU ν (χ * τ) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν (χ * τ) A).representation)
    (JB : (UnramifiedLeviInduction h hU ν χ B).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ B).representation)
    (hJ : ∀ f, JB (inducedMap h hU (productBaseTwistEquiv ν τ χ a).toIntertwiningMap f) =
      inducedMap h' hU' (productBaseTwistEquiv ν τ χ a).toIntertwiningMap (JA f))
    (f : CompactInductionPicture h K A) :
    compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' χ B JB
        (compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a f) =
      compactInductionBaseChangeEquiv h' K hP' hK ν hν hr' τ a
        (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
          h' hU' hδ' hP' hP'K hr' (χ * τ) A JA f) := by
  change unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χ B
    (JB ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ B).symm
      (compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a f))) = _
  rw [unramifiedLeviInductionCompactEquiv_symm_baseChange, hJ,
    unramifiedLeviInductionCompactEquiv_baseChange]
  rfl

/-- Restriction to the compact picture also reflects the actual ambient
base-change square at the translated parameter. -/
theorem compactIntertwiningOperator_baseChange_iff (τ χ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation)
    (JA : (UnramifiedLeviInduction h hU ν (χ * τ) A).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν (χ * τ) A).representation)
    (JB : (UnramifiedLeviInduction h hU ν χ B).representation.IntertwiningMap
      (UnramifiedLeviInduction h' hU' ν χ B).representation) :
    (∀ f, JB (inducedMap h hU (productBaseTwistEquiv ν τ χ a).toIntertwiningMap f) =
      inducedMap h' hU' (productBaseTwistEquiv ν τ χ a).toIntertwiningMap (JA f)) ↔
    (∀ f, compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' χ B JB
        (compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a f) =
      compactInductionBaseChangeEquiv h' K hP' hK ν hν hr' τ a
        (compactIntertwiningOperator h hU hδ K hP hK hPK ν hν hr
          h' hU' hδ' hP' hP'K hr' (χ * τ) A JA f)) := by
  constructor
  · intro hJ f
    apply compactIntertwiningOperator_baseChange
    exact hJ
  · intro hJ f
    have hc := hJ
      (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr (χ * τ) A f)
    simp only [compactIntertwiningOperator, LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
    rw [unramifiedLeviInductionCompactEquiv_symm_baseChange,
      LinearEquiv.symm_apply_apply] at hc
    apply (unramifiedLeviInductionCompactEquiv h' hU' hδ' K hP' hK hP'K ν hν hr' χ B).injective
    rw [unramifiedLeviInductionCompactEquiv_baseChange]
    exact hc

section FullDomain

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

/-- The original scalar-integral domain is full at both corresponding
parameters simultaneously. No convergence premise is supplied by the equivalence. -/
theorem standardIntertwining_domain_eq_top_baseChange_iff
    (τ χ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation) :
    domain h hU U'
        (A.twist (χ * τ).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker ν (χ * τ))) qν = ⊤ ↔
      domain h hU U'
        (B.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤ :=
  domain_eq_top_iff_equiv h hU U' qν (productBaseTwistEquiv ν τ χ a)

end FullDomain

section StandardIntegral

variable [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (qν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G)) (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The actual standard integral satisfies base change on its full original
domain, using the same quotient measure and normalization on both sides. -/
theorem standardCompactOperator_baseChange (τ χ : unramifiedCharacters ν)
    (a : (A.twist τ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν τ)).representation.Equiv B.representation)
    (hfullA : domain h hU U'
      (A.twist (χ * τ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (χ * τ))) qν = ⊤)
    (hfullB : domain h hU U'
      (B.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) :
    standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ B hfullB
        (compactInductionBaseChangeEquiv h K hP hK ν hν hr τ a f) =
      compactInductionBaseChangeEquiv h' K hP' hK ν hν hr' τ a
        (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
          h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq (χ * τ) A hfullA f) := by
  apply compactIntertwiningOperator_baseChange
  intro v
  exact congrArg (fun T => T v)
    (fullSourceIntertwiner_natural h hU h' hU' qν μU' μI hqν hM hsq
      hfullA hfullB (productBaseTwistEquiv ν τ χ a).toIntertwiningMap)

end StandardIntegral

end Langlands.Plancherel
