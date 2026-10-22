import Langlands.Representation.CompactCoefficient.ConditionalProjection

/-!
# Conditional orthogonal compact-isotypic projector families

Schur's lemma separates distinct intrinsic isotypic subspaces from outgoing
maps to the other class. Fixed vectors belong to the annihilator of a class
with no fixed vectors. These facts give orthogonality and fixed-vector
vanishing for the family constructed from supplied complementary pairs.
-/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Intertwiners between representatives of distinct classes vanish. -/
theorem intertwiningMap_eq_zero_of_ne
    {D E : IrreducibleCompactCoefficientRep.{uG, uV} G}
    (h : ofRep D ≠ ofRep E)
    (f : D.obj.representation.IntertwiningMap E.obj.representation) : f = 0 := by
  let : D.obj.representation.IsIrreducible := D.property.1
  let : E.obj.representation.IsIrreducible := E.property.1
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
  · exact False.elim (h ((ofRep_eq_iff D E).2
      ⟨CategoryTheory.ObjectProperty.isoMk _ (SmoothRep.mkIso (f.ofBijective hf))⟩))
  · exact hf

/-- The isotypic subspace of one class lies in the annihilator of another. -/
theorem isotypicSubrepresentation_le_annihilator_of_ne
    {c d : CompactCoefficientClass.{uG, uV} G} (h : c ≠ d)
    (A : SmoothRep.{0, uG, uW} ℂ G) :
    isotypicSubrepresentation c A ≤ annihilatorSubrepresentation d A := by
  refine (isotypicSubrepresentation_le_iff _).2 fun D hD f => ?_
  refine (le_annihilatorSubrepresentation_iff _).2 fun E hE g => ?_
  have hz : g.comp f = 0 := intertwiningMap_eq_zero_of_ne
    (fun hDE => h (hD.symm.trans (hDE.trans hE))) (g.comp f)
  rintro _ ⟨v, rfl⟩
  change g (f v) = 0
  exact congrArg (fun t : D.obj.representation.IntertwiningMap E.obj.representation => t v) hz

/-- Orthogonality follows from range/kernel containment alone; idempotence is
not needed for this implication. -/
theorem comp_eq_zero_of_isotypic_range_annihilator_ker
    {c d : CompactCoefficientClass.{uG, uV} G} (h : c ≠ d)
    {A : SmoothRep.{0, uG, uW} ℂ G}
    (P Q : A.representation.IntertwiningMap A.representation)
    (hP : P.range ≤ isotypicSubrepresentation c A)
    (hQ : annihilatorSubrepresentation d A ≤ Q.ker) : Q.comp P = 0 := by
  ext v
  exact hQ (isotypicSubrepresentation_le_annihilator_of_ne h A (hP ⟨v, rfl⟩))

/-- If a class has no nonzero fixed vector, every fixed ambient vector lies in
its annihilator. The subgroup need not be compact or open. -/
theorem fixedVectors_le_annihilator_of_not_hasFixedVector
    (c : CompactCoefficientClass.{uG, uV} G) (K : Subgroup G)
    (hc : ¬ HasFixedVector K c) (A : SmoothRep.{0, uG, uW} ℂ G) :
    fixedVectors A.representation K ≤ (annihilatorSubrepresentation c A).toSubmodule := by
  intro v hv
  apply (mem_annihilatorSubrepresentation_iff v).2
  intro D hD f
  have hD0 : fixedVectors D.obj.representation K = ⊥ := by
    by_contra hn
    exact hc (hD ▸ (hasFixedVector_ofRep K D).2 hn)
  have hf : f v ∈ fixedVectors D.obj.representation K :=
    (fixedVectorsMap f K ⟨v, hv⟩).property
  rw [hD0] at hf
  exact hf

/-- Every endomorphism whose kernel contains the intrinsic annihilator kills
fixed vectors when the class has no nonzero fixed vector. -/
theorem apply_eq_zero_of_annihilator_le_ker
    (c : CompactCoefficientClass.{uG, uV} G) (K : Subgroup G)
    (hc : ¬ HasFixedVector K c) {A : SmoothRep.{0, uG, uW} ℂ G}
    (P : A.representation.IntertwiningMap A.representation)
    (hP : annihilatorSubrepresentation c A ≤ P.ker)
    {v : A} (hv : v ∈ fixedVectors A.representation K) : P v = 0 :=
  hP (fixedVectors_le_annihilator_of_not_hasFixedVector c K hc A hv)

/-- The actual isotypic projector family, conditional on complementarity for
every class and ambient smooth representation in the specified universes. -/
def isotypicProjectorFamilyOfIsCompl
    (h : ∀ (c : CompactCoefficientClass.{uG, uV} G)
      (A : SmoothRep.{0, uG, uW} ℂ G),
      IsCompl (isotypicSubrepresentation c A).toSubmodule
        (annihilatorSubrepresentation c A).toSubmodule)
    (c : CompactCoefficientClass.{uG, uV} G) (A : SmoothRep.{0, uG, uW} ℂ G) :
    A.representation.IntertwiningMap A.representation :=
  isotypicProjectorOfIsCompl c (h c A)

section Family

variable (h : ∀ (c : CompactCoefficientClass.{uG, uV} G)
    (A : SmoothRep.{0, uG, uW} ℂ G),
    IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule)

theorem isotypicProjectorFamilyOfIsCompl_orthogonal
    {c d : CompactCoefficientClass.{uG, uV} G} (hcd : c ≠ d)
    (A : SmoothRep.{0, uG, uW} ℂ G) :
    (isotypicProjectorFamilyOfIsCompl h d A).comp
      (isotypicProjectorFamilyOfIsCompl h c A) = 0 := by
  apply comp_eq_zero_of_isotypic_range_annihilator_ker hcd
  · exact le_of_eq (isotypicProjectorOfIsCompl_range c (h c A))
  · exact le_of_eq (isotypicProjectorOfIsCompl_ker d (h d A)).symm

theorem isotypicProjectorFamilyOfIsCompl_vanishes_on_fixedVectors
    (c : CompactCoefficientClass.{uG, uV} G) (A : SmoothRep.{0, uG, uW} ℂ G)
    (K : Subgroup G) (hc : ¬ HasFixedVector K c)
    {v : A} (hv : v ∈ fixedVectors A.representation K) :
    isotypicProjectorFamilyOfIsCompl h c A v = 0 :=
  apply_eq_zero_of_annihilator_le_ker c K hc _
    (le_of_eq (isotypicProjectorOfIsCompl_ker c (h c A)).symm) hv

end Family
end Langlands.CompactCoefficientClass
