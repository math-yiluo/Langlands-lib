import Langlands.Representation.CompactCoefficient.SelectedCoverage

/-! Conjugation stability of the classes in a supplied finite spanning family. -/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uC uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A spanning family of maps from selected representatives fills the selected sum. -/
theorem selectedIsotypic_eq_top_of_finiteFamily_span
    {ι : Type uI} [Fintype ι]
    (D : ι → IrreducibleCompactCoefficientRep.{uG, uC} G)
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (f : ∀ i, (D i).obj.representation.IntertwiningMap A.representation)
    (hspan : (⨆ i, (f i).range.toSubmodule) = ⊤) :
    (selectedIsotypicSubrepresentation (classesOfFiniteFamily D) A).toSubmodule = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply iSup_le
  intro i
  have hi : ofRep (D i) ∈ classesOfFiniteFamily D :=
    (mem_classesOfFiniteFamily D _).2 ⟨i, rfl⟩
  exact (range_le_isotypicSubrepresentation (D i) rfl (f i)).trans
    (le_iSup (fun c : classesOfFiniteFamily D => isotypicSubrepresentation c.val A) ⟨_, hi⟩)

/-- With the selected intrinsic complements, a spanning family has zero common annihilator. -/
theorem selectedAnnihilator_eq_bot_of_finiteFamily_span
    {ι : Type uI} [Fintype ι]
    (D : ι → IrreducibleCompactCoefficientRep.{uG, uC} G)
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (f : ∀ i, (D i).obj.representation.IntertwiningMap A.representation)
    (hspan : (⨆ i, (f i).range.toSubmodule) = ⊤)
    (h : ∀ c : classesOfFiniteFamily D,
      IsCompl (isotypicSubrepresentation c.val A).toSubmodule
        (annihilatorSubrepresentation c.val A).toSubmodule) :
    (selectedAnnihilatorSubrepresentation (classesOfFiniteFamily D) A).toSubmodule = ⊥ := by
  have hd := (selected_isCompl (classesOfFiniteFamily D) h).disjoint.symm
  rw [selectedIsotypic_eq_top_of_finiteFamily_span D f hspan] at hd
  exact disjoint_top.mp hd

section Ambient

variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    {ι : Type uI} [Fintype ι]
    (D : ι → IrreducibleCompactCoefficientRep.{uG, uC} N)
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (f : ∀ i, (D i).obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N A).representation)
    (hf : ∀ i, Function.Injective (f i))
    (hspan : (⨆ i, (f i).range.toSubmodule) = ⊤)
    (h : ∀ c : classesOfFiniteFamily D,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule)

include hf hspan h in
/-- Ambient conjugation sends each class of the supplied spanning family into that family. -/
theorem pullback_conjugation_mem_classesOfFiniteFamily
    (g : G) (c : CompactCoefficientClass.{uG, uC} N)
    (hc : c ∈ classesOfFiniteFamily D) :
    pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈
      classesOfFiniteFamily D := by
  obtain ⟨i, rfl⟩ := (mem_classesOfFiniteFamily D c).1 hc
  let e := SmoothRep.normalSubgroupInverseConjugation N g
  let E := IrreducibleCompactCoefficientRep.pullback e (D i)
  let F : E.obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N A).representation :=
    (SmoothRep.restrictionConjugationMap N A g).comp (SmoothRep.pullbackMap e (f i))
  have hF : Function.Injective F :=
    (A.representation.apply_bijective g).injective.comp (hf i)
  let : Representation.IsIrreducible E.obj.representation := E.property.1
  have hd : Disjoint F.range.toSubmodule
      (selectedAnnihilatorSubrepresentation (classesOfFiniteFamily D)
        (SmoothRep.restrictSubgroup N A)).toSubmodule := by
    rw [selectedAnnihilator_eq_bot_of_finiteFamily_span D f hspan h]
    exact disjoint_bot_right
  obtain ⟨j, ⟨a⟩⟩ := exists_equiv_finiteFamily_of_disjoint_selectedAnnihilator D F hF hd
  have heq : ofRep E = ofRep (D j) :=
    (ofRep_eq_iff E (D j)).2 ⟨IrreducibleCompactCoefficientRep.isoOfEquiv a⟩
  exact (mem_classesOfFiniteFamily D _).2 ⟨j, heq.symm⟩

include hf hspan h in
/-- Conjugation preserves membership in the finite set of selected classes. -/
theorem mem_classesOfFiniteFamily_conjugation_iff
    (g : G) (c : CompactCoefficientClass.{uG, uC} N) :
    c ∈ classesOfFiniteFamily D ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈
        classesOfFiniteFamily D := by
  classical
  let e := pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g)
  have hm : (classesOfFiniteFamily D).map e.toEmbedding = classesOfFiniteFamily D := by
    apply Finset.map_eq_of_subset
    intro d hd
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hd
    exact pullback_conjugation_mem_classesOfFiniteFamily N D f hf hspan h g b hb
  constructor
  · exact pullback_conjugation_mem_classesOfFiniteFamily N D f hf hspan h g c
  · intro hc
    change e c ∈ classesOfFiniteFamily D at hc
    rw [← hm] at hc
    obtain ⟨b, hb, heq⟩ := Finset.mem_map.1 hc
    exact e.injective heq ▸ hb

/-- The actual permutation of the selected class subtype induced by ambient conjugation. -/
def finiteFamilyConjugationEquiv (g : G) :
    classesOfFiniteFamily D ≃ classesOfFiniteFamily D :=
  (pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g)).subtypeEquiv
    (mem_classesOfFiniteFamily_conjugation_iff N D f hf hspan h g)

@[simp]
theorem finiteFamilyConjugationEquiv_val (g : G) (c : classesOfFiniteFamily D) :
    (finiteFamilyConjugationEquiv N D f hf hspan h g c).val =
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c.val := rfl

end Ambient

end Langlands.CompactCoefficientClass
