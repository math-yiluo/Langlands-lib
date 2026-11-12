import Langlands.Representation.Induction.NormalLevelInducedFixedVectors

/-! # Normalized induced fixed vectors and the literal Levi intersection -/

noncomputable section

namespace Langlands.Aubert.General

universe uG uV

section Factorization

variable {G : Type uG} [Group G] {P M U Ubar L : Subgroup G}

/-- The literal Iwahori intersection factorization preserves the Levi
projection whenever the opposite radical meets the parabolic trivially. -/
theorem IsSemidirectDecomposition.projection_mem_of_iwahoriIntersection
    (h : IsSemidirectDecomposition P M U)
    (hL : BruhatTits.SpecialCompact.HasIwahoriIntersectionDecomposition L M U Ubar)
    (hPUbar : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1)
    (p : P) (hp : (p : G) ∈ L) :
    ((h.projection p : M) : G) ∈ L := by
  obtain ⟨⟨n, m, u⟩, he⟩ := hL.surjective ⟨p, hp⟩
  have hpe : (p : G) = (n : G) * (m : G) * (u : G) :=
    (congrArg Subtype.val he).symm
  have hn : (n : G) = 1 := by
    apply hPUbar n _ n.property.2
    have heq : (n : G) = (p : G) * ((m : G) * (u : G))⁻¹ := by
      rw [hpe]
      group
    rw [heq]
    exact P.mul_mem p.property
      (P.inv_mem (P.mul_mem (h.levi_le m.property.2)
        (h.unipotent_le u.property.2)))
  have hproj : h.projection p = ⟨m, m.property.2⟩ := by
    apply (h.projection_eq_iff p ⟨m, m.property.2⟩).mpr
    rw [hpe, hn, one_mul, inv_mul_cancel_left]
    exact u.property.2
  rw [hproj]
  exact m.property.1

end Factorization

section Normalized

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hprojection : ∀ p : P, (p : G) ∈ K → ((h.projection p : M) : G) ∈ K)

include hP hK hprojection in
/-- On a compact intersection stable under the Levi projection, the actual
normalized coefficient fixed space is the literal `K ∩ M` fixed space. -/
theorem inducingRepresentation_fixedVectors_eq
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    fixedVectors (inducingRepresentation h hU A) (K.toSubgroup.comap P.subtype) =
      fixedVectors A.representation (K.toSubgroup.comap M.subtype) := by
  ext v
  rw [mem_fixedVectors_iff, mem_fixedVectors_iff]
  have hact (p : P) (hp : (p : G) ∈ K) :
      inducingRepresentation h hU A p v = A.representation (h.projection p) v := by
    change (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
      A.representation (h.projection p) v = _
    rw [HaarModulus.closedHalfCharacter_eq_one_of_mem_compactOpen U P hU
      h.le_normalizer hP K hK hp]
    exact one_smul ℂ _
  constructor
  · intro hv m
    let p : P := ⟨(m.val : G), h.levi_le m.val.property⟩
    have hp : (p : G) ∈ K := m.property
    have he := hv ⟨p, hp⟩
    change inducingRepresentation h hU A p v = v at he
    rw [hact p hp] at he
    simpa only [p, h.projection_levi] using he
  · intro hv p
    change inducingRepresentation h hU A p.val v = v
    rw [hact p.val p.property]
    exact hv ⟨h.projection p.val, hprojection p.val p.property⟩

variable (K₀ : Subgroup G)
  (hnormal : K₀ ≤ Subgroup.normalizer (K : Set G))

/-- Restriction of a normalized induced fixed vector to `K₀`, with values
in the actual literal Levi-intersection fixed space. -/
def normalLevelNormalizedEvaluation (A : SmoothRep.{0, uG, uV} ℂ M) :
    fixedVectors ((normalizedInductionFunctor h hU).obj A).representation K.toSubgroup →ₗ[ℂ]
      (K₀ → fixedVectors A.representation (K.toSubgroup.comap M.subtype)) where
  toFun f k := ⟨Induction.eval P (inducingRepresentation h hU A) f.val k, by
    rw [← inducingRepresentation_fixedVectors_eq h hU hP K hK hprojection A]
    exact (Induction.normalLevelEvaluation P (inducingRepresentation h hU A)
      K K₀ hnormal f k).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Covariance and `G=P K₀` make the normalized restriction injective. -/
theorem normalLevelNormalizedEvaluation_injective
    (hfactor : ∀ x : G, ∃ p : P, ∃ k : K₀, x = (p : G) * (k : G))
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Injective
      (normalLevelNormalizedEvaluation h hU hP K hK hprojection K₀ hnormal A) := by
  intro f g hfg
  apply Induction.normalLevelEvaluation_injective P (inducingRepresentation h hU A)
    K K₀ hnormal hfactor
  funext k
  apply Subtype.ext
  exact congrArg (fun a => (a k).val) hfg

include hP hK hprojection hnormal in
/-- The exact prescribed normal-level nontriviality criterion for actual
normalized induction, with the literal `K ∩ M` subgroup. -/
theorem nontrivial_fixedVectors_normalizedInduction_iff
    (hfactor : ∀ x : G, ∃ p : P, ∃ k : K₀, x = (p : G) * (k : G))
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    Nontrivial (fixedVectors
      ((normalizedInductionFunctor h hU).obj A).representation K.toSubgroup) ↔
      Nontrivial (fixedVectors A.representation (K.toSubgroup.comap M.subtype)) := by
  change Nontrivial (fixedVectors
    (Induction.smoothInduced P (inducingRepresentation h hU A)) K.toSubgroup) ↔ _
  rw [Induction.nontrivial_fixedVectors_smoothInduced_iff P
    (inducingRepresentation h hU A) K hK K₀ hnormal hfactor,
    inducingRepresentation_fixedVectors_eq h hU hP K hK hprojection A]

end Normalized

end Langlands.Aubert.General
