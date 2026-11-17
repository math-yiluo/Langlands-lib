import Langlands.Representation.Plancherel.StandardIntertwiningAmbientTwist

/-! # Ambient character transport of target-valued standard intertwiners -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  (χ : SmoothCharacter ℂ G) (hχU : U ≤ χ.toMonoidHom.ker)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (U' : Subgroup G) (hχU' : U' ≤ χ.toMonoidHom.ker)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

set_option hygiene false in
local notation "Aχ" =>
  A.twist (subgroupSmoothCharacter χ M).toMonoidHom
    (subgroupSmoothCharacter χ M).isOpen_ker

/-- Restriction of ambient character multiplication to the exact domains of
the actual standard integrals. -/
def domainCharacterTwistEquiv :
    (Langlands.twist χ.toMonoidHom
      (domainSubrepresentation h hU U' A ν).toRepresentation).Equiv
      (domainSubrepresentation h hU U' Aχ ν).toRepresentation where
  toLinearEquiv := {
    toFun f := ⟨leviInductionCharacterTwistEquiv h hU χ hχU A f.val,
      (mem_domain_characterTwist_iff h hU χ hχU A U' hχU' ν f.val).mpr f.property⟩
    invFun f := ⟨(leviInductionCharacterTwistEquiv h hU χ hχU A).symm f.val, by
      apply (mem_domain_characterTwist_iff h hU χ hχU A U' hχU' ν _).mp
      rw [Representation.Equiv.apply_symm_apply]
      exact f.property⟩
    map_add' f k := Subtype.ext
      ((leviInductionCharacterTwistEquiv h hU χ hχU A).toLinearEquiv.map_add f.val k.val)
    map_smul' c f := Subtype.ext
      ((leviInductionCharacterTwistEquiv h hU χ hχU A).toLinearEquiv.map_smul c f.val)
    left_inv f := Subtype.ext
      ((leviInductionCharacterTwistEquiv h hU χ hχU A).symm_apply_apply f.val)
    right_inv f := Subtype.ext
      ((leviInductionCharacterTwistEquiv h hU χ hχU A).apply_symm_apply f.val) }
  isIntertwining' t := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (leviInductionCharacterTwistEquiv h hU χ hχU A).toIntertwiningMap t f.val

@[simp]
theorem domainCharacterTwistEquiv_val (f : domain h hU U' A ν) :
    (domainCharacterTwistEquiv h hU χ hχU A U' hχU' ν f).val =
      leviInductionCharacterTwistEquiv h hU χ hχU A f.val := rfl

variable (hM : IsClosed (M : Set G))

/-- Uniqueness in the original carrier identifies the selected integral after
ambient character multiplication on its exact domain. -/
theorem operator_characterTwist (f : domain h hU U' A ν) :
    operator h hU U' Aχ ν hM (domainCharacterTwistEquiv h hU χ hχU A U' hχU' ν f) =
      fun g => (χ.toMonoidHom g : ℂ) • operator h hU U' A ν hM f g :=
  operator_eq h hU U' Aχ ν hM _
    ((hasIntegral_characterTwist_iff h hU χ hχU A U' hχU' ν f.val _).mpr
      (operator_spec h hU U' A ν hM f))

section Target

variable {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  [T2Space G]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The actual target-valued standard integral commutes with ambient
character multiplication on the exact source domains. -/
theorem targetOperator_characterTwist (f : domain h hU U' A ν) :
    targetOperator h hU h' hU' Aχ ν μU' μI hν hM hsq
        (domainCharacterTwistEquiv h hU χ hχU A U' hχU' ν f) =
      leviInductionCharacterTwistEquiv h' hU' χ hχU' A
        (targetOperator h hU h' hU' A ν μU' μI hν hM hsq f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change operator h hU U' Aχ ν hM
      (domainCharacterTwistEquiv h hU χ hχU A U' hχU' ν f) g =
    eval P' (leviInflatedInducingRepresentation h' hU' Aχ)
      (leviInductionCharacterTwistEquiv h' hU' χ hχU' A
        (targetOperator h hU h' hU' A ν μU' μI hν hM hsq f)) g
  rw [leviInductionCharacterTwistEquiv_eval]
  exact congrFun (operator_characterTwist h hU χ hχU A U' hχU' ν hM f) g

/-- The full-source actual integral commutes with character multiplication;
full convergence for the twist is derived from that of the original. -/
theorem fullSourceIntertwiner_characterTwist
    (hfull : domain h hU U' A ν = ⊤)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    fullSourceIntertwiner h hU h' hU' Aχ ν μU' μI hν hM hsq
        ((domain_eq_top_characterTwist_iff h hU χ hχU A U' hχU' ν).mpr hfull)
        (leviInductionCharacterTwistEquiv h hU χ hχU A f) =
      leviInductionCharacterTwistEquiv h' hU' χ hχU' A
        (fullSourceIntertwiner h hU h' hU' A ν μU' μI hν hM hsq hfull f) :=
  targetOperator_characterTwist h hU χ hχU A U' hχU' ν hM h' hU'
    μU' μI hν hsq (sourceToDomain h hU A ν hfull f)

end Target

end Langlands.Plancherel.StandardIntertwining
