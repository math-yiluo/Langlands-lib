import Langlands.Representation.Plancherel.StandardIntertwiningTargetLaws
import Langlands.Representation.Plancherel.ParabolicIntertwiningStatement

/-! # Full-domain transport of the actual standard intertwining integral -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV uW uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  {A : Langlands.SmoothRep.{0, uG, uV} ℂ M}
  {B : Langlands.SmoothRep.{0, uG, uW} ℂ M}
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- Full scalar convergence and original-carrier representability transfer
along an equivariant equivalence of inducing representations. -/
theorem domain_eq_top_of_equiv
    (e : A.representation.Equiv B.representation)
    (hfull : domain h hU U' A ν = ⊤) :
    domain h hU U' B ν = ⊤ := by
  apply top_unique
  intro f _
  have hf : inducedMap h hU e.symm.toIntertwiningMap f ∈ domain h hU U' A ν := by
    rw [hfull]
    exact Submodule.mem_top
  exact (inducedEquiv_mem_domain_iff h hU U' ν e.symm f).mp hf

/-- Equivalent inducing representations have full domain simultaneously,
including across independent carrier universes. -/
theorem domain_eq_top_iff_equiv
    (e : A.representation.Equiv B.representation) :
    domain h hU U' A ν = ⊤ ↔ domain h hU U' B ν = ⊤ :=
  ⟨domain_eq_top_of_equiv h hU U' ν e,
    domain_eq_top_of_equiv h hU U' ν e.symm⟩

section Orbit

variable {I : Type uI} (ξ : I → (M →* ℝ≥0ˣ))
  (π : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (Ω : Set (unramifiedCharacters ξ))

/-- Convergence on a character region extends to every parameter representing
the same actual twist classes. -/
theorem domain_eq_top_on_unramifiedTwistOrbitSaturation
    (hfull : ∀ χ : Ω, domain h hU U'
      (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ξ χ.val)) ν = ⊤) :
    ∀ χ : unramifiedTwistOrbitSaturation ξ π Ω, domain h hU U'
      (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ξ χ.val)) ν = ⊤ := by
  intro χ
  obtain ⟨ψ, hψ, ⟨e⟩⟩ :=
    (mem_unramifiedTwistOrbitSaturation_iff ξ π Ω χ.val).mp χ.property
  exact domain_eq_top_of_equiv h hU U' ν
    (SmoothRep.equivOfIso e) (hfull ⟨ψ, hψ⟩)

/-- Full convergence on a region and on its actual twist-orbit saturation
are equivalent. -/
theorem domain_eq_top_on_unramifiedTwistOrbitSaturation_iff :
    (∀ χ : unramifiedTwistOrbitSaturation ξ π Ω, domain h hU U'
      (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ξ χ.val)) ν = ⊤) ↔
    (∀ χ : Ω, domain h hU U'
      (π.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ξ χ.val)) ν = ⊤) := by
  constructor
  · intro hfull χ
    exact hfull ⟨χ.val, subset_unramifiedTwistOrbitSaturation ξ π Ω χ.property⟩
  · exact domain_eq_top_on_unramifiedTwistOrbitSaturation h hU U' ν ξ π Ω

end Orbit

section Target

variable {P' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

/-- A full-domain proof for one representative supplies both the full-domain
proof for every equivalent representative and the actual naturality square. -/
theorem fullSourceIntertwiner_equivalent_representative
    (hfullA : domain h hU U' A ν = ⊤)
    (e : A.representation.Equiv B.representation) :
    ∃ hfullB : domain h hU U' B ν = ⊤,
      (fullSourceIntertwiner h hU h' hU' B ν μU' μI hν hM hsq hfullB).comp
          (inducedMap h hU e.toIntertwiningMap) =
        (inducedMap h' hU' e.toIntertwiningMap).comp
          (fullSourceIntertwiner h hU h' hU' A ν μU' μI hν hM hsq hfullA) := by
  refine ⟨domain_eq_top_of_equiv h hU U' ν e hfullA, ?_⟩
  exact fullSourceIntertwiner_natural h hU h' hU' ν μU' μI hν hM hsq
    hfullA _ e.toIntertwiningMap

end Target

end Langlands.Plancherel.StandardIntertwining
