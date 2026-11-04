import Langlands.Representation.Plancherel.StandardIntertwiningIntegral

/-! # Naturality of the general standard integral -/

noncomputable section

open MeasureTheory

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  {A : Langlands.SmoothRep.{0, uG, uV} ℂ M}
  {B : Langlands.SmoothRep.{0, uG, uW} ℂ M}

/-- Actual positive Levi-normalized induction of an intertwiner, including
maps between independent carrier universes. -/
def inducedMap (T : A.representation.IntertwiningMap B.representation) :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.IntertwiningMap
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj B).representation :=
  smoothInducedMap P {
    toLinearMap := T.toLinearMap
    isIntertwining' p :=
      (Langlands.twistIntertwining
        (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer) T).isIntertwining'
          (h.projection p) }

@[simp]
theorem inducedMap_eval (T : A.representation.IntertwiningMap B.representation)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (g : G) :
    eval P (leviInflatedInducingRepresentation h hU B) (inducedMap h hU T f) g =
      T (eval P (leviInflatedInducingRepresentation h hU A) f g) := rfl

/-- Postcomposition by the Levi intertwiner commutes with actual quotient
descent. -/
theorem integrand_map (T : A.representation.IntertwiningMap B.representation)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (g : G) :
    integrand h hU U' B g (inducedMap h hU T f) =
      fun q => T (integrand h hU U' A g f q) := by
  funext q
  induction q using Quotient.inductionOn with
  | h u' => rfl

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- Every actual weak integral is preserved by a Levi intertwiner. -/
theorem HasIntegral.map_induced
    (T : A.representation.IntertwiningMap B.representation)
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A} {Jf : G → A}
    (hf : HasIntegral h hU U' A ν f Jf) :
    HasIntegral h hU U' B ν (inducedMap h hU T f) (fun g => T (Jf g)) := by
  intro g
  rw [integrand_map]
  exact HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.map (hf g) T

/-- Naturality preserves the actual convergence and representability domain. -/
theorem inducedMap_mem_domain
    (T : A.representation.IntertwiningMap B.representation)
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A}
    (hf : f ∈ domain h hU U' A ν) :
    inducedMap h hU T f ∈ domain h hU U' B ν := by
  obtain ⟨Jf, hJf⟩ := (mem_domain h hU U' A ν f).mp hf
  exact (mem_domain h hU U' B ν _).mpr
    ⟨_, HasIntegral.map_induced h hU U' ν T hJf⟩

/-- The induced map restricts to an actual ambient intertwiner of domains. -/
def domainMap (T : A.representation.IntertwiningMap B.representation) :
    (domainSubrepresentation h hU U' A ν).toRepresentation.IntertwiningMap
      (domainSubrepresentation h hU U' B ν).toRepresentation where
  toLinearMap := (inducedMap h hU T).toLinearMap.restrict
    (fun _ hf => inducedMap_mem_domain h hU U' ν T hf)
  isIntertwining' t := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ (inducedMap h hU T) t f.val

@[simp]
theorem domainMap_val (T : A.representation.IntertwiningMap B.representation)
    (f : domain h hU U' A ν) :
    (domainMap h hU U' ν T f).val = inducedMap h hU T f.val := rfl

variable (hM : IsClosed (M : Set G))

/-- Naturality of the selected standard integral for every Levi intertwiner,
with no admissibility or full-domain convergence premise. -/
theorem operator_map (T : A.representation.IntertwiningMap B.representation)
    (f : domain h hU U' A ν) :
    operator h hU U' B ν hM (domainMap h hU U' ν T f) =
      fun g => T (operator h hU U' A ν hM f g) :=
  operator_eq h hU U' B ν hM _
    (HasIntegral.map_induced h hU U' ν T (operator_spec h hU U' A ν hM f))

omit hM in
/-- An equivalence of inducing representations identifies exactly the actual
domains of the integral. -/
theorem inducedEquiv_mem_domain_iff
    (e : A.representation.Equiv B.representation)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    inducedMap h hU e.toIntertwiningMap f ∈ domain h hU U' B ν ↔
      f ∈ domain h hU U' A ν := by
  constructor
  · intro hf
    have hf' := inducedMap_mem_domain h hU U' ν e.symm.toIntertwiningMap hf
    have he : inducedMap h hU e.symm.toIntertwiningMap
        (inducedMap h hU e.toIntertwiningMap f) = f := by
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact e.symm_apply_apply _
    exact he ▸ hf'
  · exact inducedMap_mem_domain h hU U' ν e.toIntertwiningMap

omit hM in
/-- The actual integration domains are equivariantly equivalent under a
change of inducing carrier, including across independent universes. -/
def domainEquiv (e : A.representation.Equiv B.representation) :
    (domainSubrepresentation h hU U' A ν).toRepresentation.Equiv
      (domainSubrepresentation h hU U' B ν).toRepresentation where
  toLinearEquiv := {
    (domainMap h hU U' ν e.toIntertwiningMap).toLinearMap with
    invFun := domainMap h hU U' ν e.symm.toIntertwiningMap
    left_inv f := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact e.symm_apply_apply _
    right_inv f := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact e.apply_symm_apply _ }
  isIntertwining' := (domainMap h hU U' ν e.toIntertwiningMap).isIntertwining'

/-- The change-of-representative square commutes on the entire actual domain. -/
theorem operator_domainEquiv (e : A.representation.Equiv B.representation)
    (f : domain h hU U' A ν) :
    operator h hU U' B ν hM (domainEquiv h hU U' ν e f) =
      fun g => e (operator h hU U' A ν hM f g) :=
  operator_map h hU U' ν hM e.toIntertwiningMap f

end Langlands.Plancherel.StandardIntertwining
