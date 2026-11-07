import Langlands.Correspondence.SphericalStandardModulePrerequisites
import Langlands.Correspondence.OrderedUnramifiedTemperedRealizationProof
import Langlands.Representation.Unramified.SphericalGenerationReduction
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof
import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Unramified.OrderedSphericalQuotient

/-! Spherical generation of every Langlands-ordered unramified principal series. -/

noncomputable section

namespace Langlands.Correspondence

open Classification Unramified

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance generationFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance generationGLTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance generationGLGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

private theorem head_of_head_quotient
    {G : Type uF} [Group G]
    {V W X : Type uF} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W} {σ : Representation ℂ G X}
    (hh : IsIrreducibleHead ρ π) (hq : IsIrreducibleQuotient ρ σ) :
    IsIrreducibleHead ρ σ := by
  obtain ⟨_, q₀, hq₀, huniq⟩ := hh
  obtain ⟨hσ, q, hq⟩ := hq
  refine ⟨hσ, q, hq, ?_⟩
  intro W' _ _ π' hπ' q' hq'
  exact (huniq W' π' hπ' q' hq').trans (huniq X σ hσ q hq).symm

/-- Actual tempered realization supplies finite length and a strong head;
a spherical irreducible quotient makes that head spherical. -/
theorem eq_top_of_temperedRealization_sphericalQuotient
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (d : F.canonicalTopologicalData.TemperedLanglandsDatum.{uF, uF} (r + 1))
    (e : d.standardModule.representation.Equiv (principalSeriesOfTuple F z))
    (B : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) F.Carrier))
    (hq : IsIrreducibleQuotient (principalSeriesOfTuple F z) B.representation)
    (hB : fixedVectors B.representation (sphericalSubgroup F r) ≠ ⊥)
    (S : Subrepresentation (principalSeriesOfTuple F z))
    (hS : fixedVectors S.toRepresentation (sphericalSubgroup F r) ≠ ⊥) :
    S = ⊤ := by
  let T := F.canonicalTopologicalData
  let A := SmoothRep.of (principalSeriesOfTuple F z) (isSmooth_principalSeriesOfTuple F z)
  obtain ⟨H, hH⟩ := glRegularLanglandsHeadExistence.{uF, uF} p F T
    (r + 1) (Nat.succ_pos r) d
  have hhead : IsIrreducibleHead A.representation B.representation :=
    head_of_head_quotient (hH.of_equiv e) hq
  have hd : d.standardModule.HasFiniteLength :=
    RegularHeadExistence.standardModule_finiteLength_of_productPreservation T d
      (Nat.succ_pos r) (admissibleFiniteLengthProductPreservation F T)
  have hA : A.HasFiniteLength :=
    ProductLengthProof.finiteLength_of_surjective e.toIntertwiningMap e.surjective hd
  exact SphericalGeneration.eq_top_of_finiteLength_spherical_head A B hA hhead
    (Unramified.sphericalOpenSubgroup F r) (Unramified.sphericalOpenSubgroup_isCompact F r)
    (SphericalGeneration.scalarEvaluation F z) (SphericalGeneration.scalarEvaluation_injective F z)
    hB S hS

/-- Actual spherical quotients and a supplied tempered realization give the
unchanged ordered spherical-generation proposition. -/
theorem orderedUnramifiedSphericalGeneration_of_temperedRealization
    (hrealize : OrderedUnramifiedTemperedRealizationStatement.{uF, uF} F) :
    OrderedUnramifiedSphericalGenerationStatement F := by
  intro r z hz S hS
  obtain ⟨d, ⟨e⟩⟩ := hrealize r z hz
  obtain ⟨B, hq, hB⟩ := exists_spherical_irreducible_quotient F z hz
  exact eq_top_of_temperedRealization_sphericalQuotient F z d e B hq hB S hS

/-- Every subrepresentation of a Langlands-ordered actual unramified principal
series with a nonzero spherical fixed vector is the whole principal series. -/
theorem orderedUnramifiedSphericalGeneration :
    OrderedUnramifiedSphericalGenerationStatement F :=
  orderedUnramifiedSphericalGeneration_of_temperedRealization F
    (orderedUnramifiedTemperedRealization.{uF, uF} F)

end Langlands.Correspondence
