import Langlands.Representation.Aubert.General.ConjugateParabolic
import Langlands.Representation.Aubert.General.Conjugation
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Induction from the actual conjugate parabolic -/

noncomputable section

open CategoryTheory
open Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

section Preservation

variable {P M U P' M' U' : Subgroup G}

/-- Finite-length preservation of induction transports to an actual conjugate
parabolic by inverse conjugation, without an additional preservation premise. -/
theorem normalizedInductionFunctor_preservesFiniteLength_of_conjugation
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU)) :
    PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h' hU') := by
  let e := inductionConjugationIso.{uG, uV} h' h g⁻¹
    (conj_inv_iff g hPP') (conj_inv_iff g hMM') (conj_inv_iff g hUU') hU' hU
  exact ((pullbackFunctor_preservesFiniteLength _).comp hl).of_iso e.symm

/-- Short-exact preservation on finite-length terms transports by the same
inverse-conjugation isomorphism. -/
theorem normalizedInductionFunctor_preservesShortExact_of_conjugation
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (hx : PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{uG, uV} h hU)) :
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, uV} h' hU') := by
  let e := inductionConjugationIso.{uG, uV} h' h g⁻¹
    (conj_inv_iff g hPP') (conj_inv_iff g hMM') (conj_inv_iff g hUU') hU' hU
  exact (PreservesFiniteLengthShortExact.comp
    (pullbackFunctor_preservesFiniteLength _) (pullbackFunctor_preservesShortExact _) hx).of_iso
      e.symm

end Preservation

section ActualConjugate

variable {P M U N : Subgroup G}

/-- Actual normalized induction from `g P g⁻¹`, using the supplied actual Levi
`N` and the proved conjugated decomposition and closed radical. -/
def conjugateInductionFunctor (h : IsSemidirectDecomposition P M U) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G)) :
    SmoothRep.{0, uG, uV} ℂ N ⥤ SmoothRep.{0, uG, max uG uV} ℂ G :=
  normalizedInductionFunctor (h.conjugateWithLevi g hMN) (isClosed_conjugateSubgroup g hU)

theorem conjugateInductionFunctor_preservesFiniteLength
    (h : IsSemidirectDecomposition P M U) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU)) :
    PreservesFiniteLength (conjugateInductionFunctor.{uG, uV} h g hMN hU) :=
  normalizedInductionFunctor_preservesFiniteLength_of_conjugation h
    (h.conjugateWithLevi g hMN) g (mem_conjugateSubgroup g P) hMN
    (mem_conjugateSubgroup g U) hU (isClosed_conjugateSubgroup g hU) hl

theorem conjugateInductionFunctor_preservesShortExact
    (h : IsSemidirectDecomposition P M U) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, uV} h hU)) :
    PreservesFiniteLengthShortExact (conjugateInductionFunctor.{uG, uV} h g hMN hU) :=
  normalizedInductionFunctor_preservesShortExact_of_conjugation h
    (h.conjugateWithLevi g hMN) g (mem_conjugateSubgroup g P) hMN
    (mem_conjugateSubgroup g U) hU (isClosed_conjugateSubgroup g hU) hx

/-- The exact-K0 induction map from the actual conjugate parabolic, with
preservation derived from the original induction. -/
def conjugateInductionK0 (h : IsSemidirectDecomposition P M U) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{uG, max uG uV} h hU)) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ N →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  inductionK0 (h.conjugateWithLevi g hMN) (isClosed_conjugateSubgroup g hU)
    (conjugateInductionFunctor_preservesFiniteLength h g hMN hU hl)
    (conjugateInductionFunctor_preservesShortExact h g hMN hU hx)

/-- The canonical conjugate induction map composes with inverse-conjugation
pullback to give the original induction map on the whole exact K0. -/
theorem conjugateInductionK0_comp_conjugationK0
    (h : IsSemidirectDecomposition P M U) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{uG, max uG uV} h hU)) :
    (conjugateInductionK0 h g hMN hU hl hx).comp
      (conjugationK0.{uG, max uG uV} g hMN) = inductionK0 h hU hl hx :=
  inductionK0_comp_conjugationK0 h (h.conjugateWithLevi g hMN) g
    (mem_conjugateSubgroup g P) hMN (mem_conjugateSubgroup g U)
    hU (isClosed_conjugateSubgroup g hU) hl hx
    (conjugateInductionFunctor_preservesFiniteLength h g hMN hU hl)
    (conjugateInductionFunctor_preservesShortExact h g hMN hU hx)

/-- A comparison with the actual conjugate parabolic, on their common actual
Levi `N`, implies the desired induction identity. The comparison is an explicit
remaining hypothesis. -/
theorem inductionK0_comp_conjugationK0_of_sameLevi
    {Q V : Subgroup G} (h : IsSemidirectDecomposition P M U)
    (hN : IsSemidirectDecomposition Q N V) (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hlN : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} hN hV))
    (hxN : PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{uG, max uG uV} hN hV))
    (hsame : inductionK0 hN hV hlN hxN = conjugateInductionK0 h g hMN hU hl hx) :
    (inductionK0 hN hV hlN hxN).comp (conjugationK0.{uG, max uG uV} g hMN) =
      inductionK0 h hU hl hx := by
  rw [hsame]
  exact conjugateInductionK0_comp_conjugationK0 h g hMN hU hl hx

end ActualConjugate

end Langlands.Aubert.General
