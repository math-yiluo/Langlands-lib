import Langlands.Representation.Plancherel.StandardIntertwiningModulus
import Langlands.Representation.Plancherel.StandardIntertwiningNaturality
import Langlands.Representation.Plancherel.StandardIntertwiningMeasure

/-! # Naturality and full-source normalization of the standard intertwiner -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P P' M U U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  [T2Space G]
  {A : Langlands.SmoothRep.{0, uG, uV} ℂ M}
  {B : Langlands.SmoothRep.{0, uG, uW} ℂ M}
  (ν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- The actual target-valued standard integral is natural for every Levi
intertwiner, including maps between independent carrier universes. -/
theorem targetOperator_map (T : A.representation.IntertwiningMap B.representation)
    (f : domain h hU U' A ν) :
    targetOperator h hU h' hU' B ν μU' μI hν hM hsq
        (domainMap h hU U' ν T f) =
      inducedMap h' hU' T
        (targetOperator h hU h' hU' A ν μU' μI hν hM hsq f) := by
  apply Subtype.ext
  apply Subtype.ext
  exact operator_map h hU U' ν hM T f

/-- The naturality square is equality of actual ambient intertwining maps. -/
theorem targetIntertwiner_natural
    (T : A.representation.IntertwiningMap B.representation) :
    (targetIntertwiner h hU h' hU' B ν μU' μI hν hM hsq).comp
        (domainMap h hU U' ν T) =
      (inducedMap h' hU' T).comp
        (targetIntertwiner h hU h' hU' A ν μU' μI hν hM hsq) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact targetOperator_map h hU h' hU' ν μU' μI hν hM hsq T

/-- The change-of-representative square retains the target induced vectors. -/
theorem targetOperator_domainEquiv (e : A.representation.Equiv B.representation)
    (f : domain h hU U' A ν) :
    targetOperator h hU h' hU' B ν μU' μI hν hM hsq
        (domainEquiv h hU U' ν e f) =
      inducedMap h' hU' e.toIntertwiningMap
        (targetOperator h hU h' hU' A ν μU' μI hν hM hsq f) :=
  targetOperator_map h hU h' hU' ν μU' μI hν hM hsq e.toIntertwiningMap f

section FullSource

variable (A) (hfull : domain h hU U' A ν = ⊤)

omit h' hU' μU' μI hν hM hsq
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G] in
/-- Include the whole source in the actual domain only after every input's
scalar convergence and original-carrier representability have been proved. -/
def sourceToDomain :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.IntertwiningMap
      (domainSubrepresentation h hU U' A ν).toRepresentation where
  toLinearMap := {
    toFun f := ⟨f, by
      change f ∈ domain h hU U' A ν
      rw [hfull]
      exact Submodule.mem_top⟩
    map_add' _ _ := Subtype.ext rfl
    map_smul' _ _ := Subtype.ext rfl }
  isIntertwining' _ := LinearMap.ext fun _ => Subtype.ext rfl

omit h' hU' μU' μI hν hM hsq
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G] in
@[simp]
theorem sourceToDomain_val
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    (sourceToDomain h hU A ν hfull f).val = f := rfl

/-- The actual standard integral on the entire normalized induction,
conditional on the explicitly proved full-domain equality. -/
def fullSourceIntertwiner :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.IntertwiningMap
      ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj A).representation :=
  (targetIntertwiner h hU h' hU' A ν μU' μI hν hM hsq).comp
    (sourceToDomain h hU A ν hfull)

@[simp]
theorem fullSourceIntertwiner_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (g : G) :
    eval P' (leviInflatedInducingRepresentation h' hU' A)
        (fullSourceIntertwiner h hU h' hU' A ν μU' μI hν hM hsq hfull f) g =
      operator h hU U' A ν hM (sourceToDomain h hU A ν hfull f) g := rfl

/-- The full-source intertwiner retains the original smooth-dual scalar
integral relation at every input and every ambient argument. -/
theorem fullSourceIntertwiner_spec
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    HasIntegral h hU U' A ν f
      (eval P' (leviInflatedInducingRepresentation h' hU' A)
        (fullSourceIntertwiner h hU h' hU' A ν μU' μI hν hM hsq hfull f)) :=
  operator_spec h hU U' A ν hM (sourceToDomain h hU A ν hfull f)

end FullSource

/-- Naturality of the actual full-source standard integrals, with the
convergence proof for each inducing representation displayed separately. -/
theorem fullSourceIntertwiner_natural
    (hfullA : domain h hU U' A ν = ⊤) (hfullB : domain h hU U' B ν = ⊤)
    (T : A.representation.IntertwiningMap B.representation) :
    (fullSourceIntertwiner h hU h' hU' B ν μU' μI hν hM hsq hfullB).comp
        (inducedMap h hU T) =
      (inducedMap h' hU' T).comp
        (fullSourceIntertwiner h hU h' hU' A ν μU' μI hν hM hsq hfullA) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  exact targetOperator_map h hU h' hU' ν μU' μI hν hM hsq T
    (sourceToDomain h hU A ν hfullA f)

section Diagonal

variable [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (U.subgroupOf U)] [BorelSpace (U.subgroupOf U)]
  [MeasurableSpace (QuotientSpace (U := U) U)]
  [BorelSpace (QuotientSpace (U := U) U)]
  (ν₀ : Measure (QuotientSpace (U := U) U))
  (μU : Measure U) (μI₀ : Measure (U.subgroupOf U))
  [IsHaarMeasure μU] [μU.Regular] [IsMulRightInvariant μU]
  [IsHaarMeasure μI₀] [μI₀.Regular] [IsMulRightInvariant μI₀]
  (hν₀ : QuotientIntegration.IsCompatible (U.subgroupOf U) μU μI₀ ν₀)

omit h' hU' ν μU' μI hν hM hsq
  [T2Space G] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (QuotientSpace (U := U) U)]
  [BorelSpace (QuotientSpace (U := U) U)] in
/-- The actual squared-modulus identity is proved in the diagonal case. -/
theorem squaredModulusCompatibility_diagonal :
    SquaredModulusCompatibility h hU h hU := by
  apply (squaredModulusCompatibility_iff h hU h hU).mpr
  intro m
  simp only [inf_idem, pow_two]

omit h' hU' ν μU' μI hν hsq in
/-- The diagonal target-valued integral is defined on every source function
using the proved full-domain and squared-modulus equalities. -/
def diagonalTargetIntertwiner [IsFiniteMeasure ν₀] (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.IntertwiningMap
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation :=
  fullSourceIntertwiner h hU h hU A ν₀ μU μI₀ hν₀ hM
    (squaredModulusCompatibility_diagonal h hU) (domain_diagonal h hU A ν₀)

omit h' hU' ν μU' μI hν hsq in
/-- The actual full-source diagonal intertwiner has precisely the
total-mass normalization of the original integral. -/
theorem diagonalTargetIntertwiner_eq [IsFiniteMeasure ν₀]
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :
    diagonalTargetIntertwiner h hU hM ν₀ μU μI₀ hν₀ A =
      ((ν₀ Set.univ).toReal : ℂ) •
        Representation.IntertwiningMap.id
          ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  exact operator_diagonal h hU A ν₀ hM
    (sourceToDomain h hU A ν₀ (domain_diagonal h hU A ν₀) f)

omit h' hU' ν μU' μI hν hsq in
/-- A probability diagonal quotient gives the identity as an actual
ambient intertwining map on the whole normalized induction. -/
theorem diagonalTargetIntertwiner_probability [IsProbabilityMeasure ν₀]
    (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) :
    diagonalTargetIntertwiner h hU hM ν₀ μU μI₀ hν₀ A =
      Representation.IntertwiningMap.id
        ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation := by
  rw [diagonalTargetIntertwiner_eq]
  simp only [measure_univ, ENNReal.toReal_one, Complex.ofReal_one, one_smul]

end Diagonal

end Langlands.Plancherel.StandardIntertwining
