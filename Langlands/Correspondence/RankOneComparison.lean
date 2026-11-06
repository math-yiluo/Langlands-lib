import Langlands.Correspondence.OperationCompatibility
import Langlands.Weil.Representation.CharacterNormalizationProof

/-!
# Rank-one comparison along a supplied reciprocity candidate

Every continuous rank-one Weil class comes from a field character along the
specified candidate. Rank-one compatibility then determines the rank-one part
of a supercuspidal family.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- Forgetting the rank and the continuity/irreducibility certificates is injective. -/
theorem weilClassForget_injective {n : ℕ+} :
    Function.Injective (weilClassForget.{uF, uP} F (n := n)) := by
  intro σ τ h
  apply Subtype.ext
  exact FiniteRepresentation.forgetPropertyClass_injective _ h

/-- Two rank-one Weil classes represented by the same scalar character agree. -/
theorem IsRankOneWeilCharacter.class_unique
    {χ : Weil.Local.localWeilGroup F →* ℂˣ}
    {σ τ : IrreducibleWeilClass.{uF, uP} F 1}
    (hσ : IsRankOneWeilCharacter F χ σ)
    (hτ : IsRankOneWeilCharacter F χ τ) : σ = τ := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hσ
  obtain ⟨B, hB, ⟨eB⟩⟩ := hτ
  apply weilClassForget_injective F
  exact hA.symm.trans
    (((FiniteRepresentation.classOf_eq_iff A B).mpr ⟨eA.symm.trans eB⟩).trans hB)

/-- Every continuous rank-one Weil class is the pullback of a field character
along any supplied reciprocity candidate. -/
theorem exists_rankOneWeilFieldCharacter (e : ReciprocityCandidate F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ χ : QuasiCharacter F, IsRankOneWeilCharacter F (weilCharacter F e χ) σ := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  have hclass : FiniteRepresentation.classOf A.val = weilClassForget F σ := by
    exact congrArg (FiniteRepresentation.forgetPropertyClass _) hA
  have hrank : Module.finrank ℂ A.val = 1 := by
    exact (congrArg FiniteRepresentation.classRank hclass).trans σ.property
  obtain ⟨χ, ⟨hχ, ⟨eχ⟩⟩, _⟩ :=
    (Weil.representationCharacterNormalization
      (Weil.Local.localWeilGroup F) A.val A.val.representation A.property.1).2 hrank
  let η : Weil.Local.localWeilGroup F →ₜ* ℂˣ :=
    { toMonoidHom := χ, continuous_toFun := hχ }
  refine ⟨LocalFactor.RankOne.fieldCharacter F e η, A.val, hclass, ?_⟩
  have hη : weilCharacter F e (LocalFactor.RankOne.fieldCharacter F e η) = χ :=
    congrArg ContinuousMonoidHom.toMonoidHom
      (LocalFactor.RankOne.weilCharacter_fieldCharacter F e η)
  rw [hη]
  exact ⟨eχ.symm⟩

/-- A field character whose scalar pullback represents the specified rank-one class. -/
def rankOneWeilFieldCharacter (e : ReciprocityCandidate F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) : QuasiCharacter F :=
  Classical.choose (exists_rankOneWeilFieldCharacter F e σ)

/-- The chosen field character represents the original actual Weil class. -/
theorem rankOneWeilFieldCharacter_spec (e : ReciprocityCandidate F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) :
    IsRankOneWeilCharacter F
      (weilCharacter F e (rankOneWeilFieldCharacter F e σ)) σ :=
  Classical.choose_spec (exists_rankOneWeilFieldCharacter F e σ)

/-- Actual automorphic classes equivalent to the same scalar character agree. -/
theorem IsRankOneCharacter.class_unique {χ : QuasiCharacter F}
    {π π' : AutomorphicClass.{uF, uA} F 1}
    (hπ : IsRankOneCharacter F χ π)
    (hπ' : IsRankOneCharacter F χ π') : π = π' := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hπ
  obtain ⟨B, hB, ⟨eB⟩⟩ := hπ'
  exact hA.symm.trans
    (((automorphicClassOf_eq_iff F A B).mpr ⟨eA.symm.trans eB⟩).trans hB)

/-- The rank-one character relation determines a supercuspidal class uniquely. -/
theorem IsSupercuspidalRankOneCharacter.class_unique {χ : QuasiCharacter F}
    {π π' : SupercuspidalAutomorphicClass.{uF, uA} F 1}
    (hπ : IsSupercuspidalRankOneCharacter F χ π)
    (hπ' : IsSupercuspidalRankOneCharacter F χ π') : π = π' :=
  supercuspidalToAutomorphic_injective F
    (IsRankOneCharacter.class_unique F hπ hπ')

/-- Rank-one compatibility along one common supplied candidate forces equality
of the rank-one parts of two supercuspidal families. -/
theorem supercuspidalRankOne_eq_of_compatibility (e : ReciprocityCandidate F)
    {c d : SupercuspidalMap.{uF, uP, uA} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (hd : SupercuspidalRankOneCompatibility F e d) : c 1 = d 1 := by
  funext σ
  let χ := rankOneWeilFieldCharacter F e σ
  have hσ := rankOneWeilFieldCharacter_spec F e σ
  obtain ⟨σc, hσc, hπc⟩ := hc χ
  obtain ⟨σd, hσd, hπd⟩ := hd χ
  have hcσ : σc = σ := IsRankOneWeilCharacter.class_unique F hσc hσ
  have hdσ : σd = σ := IsRankOneWeilCharacter.class_unique F hσd hσ
  subst σc
  subst σd
  exact IsSupercuspidalRankOneCharacter.class_unique F hπc hπd

end Langlands.Correspondence
