import Langlands.Representation.CompactCoefficient.SelectedProjector

/-! Type detection by the selected common annihilator. -/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uC uV uW uI

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The distinct classes occurring in a supplied finite family. -/
def classesOfFiniteFamily {ι : Type uI} [Fintype ι]
    (D : ι → IrreducibleCompactCoefficientRep.{uG, uC} G) :
    Finset (CompactCoefficientClass.{uG, uC} G) := by
  classical
  exact Finset.univ.image fun i => ofRep (D i)

@[simp]
theorem mem_classesOfFiniteFamily {ι : Type uI} [Fintype ι]
    (D : ι → IrreducibleCompactCoefficientRep.{uG, uC} G)
    (c : CompactCoefficientClass.{uG, uC} G) :
    c ∈ classesOfFiniteFamily D ↔ ∃ i, ofRep (D i) = c := by
  classical
  simp only [classesOfFiniteFamily, Finset.mem_image, Finset.mem_univ, true_and]

/-- An irreducible representation embedded disjointly from the selected common
annihilator has one of the selected types. -/
theorem exists_equiv_of_disjoint_selectedAnnihilator
    (t : Finset (CompactCoefficientClass.{uG, uC} G))
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}
    [Representation.IsIrreducible B.representation]
    (f : B.representation.IntertwiningMap A.representation)
    (hf : Function.Injective f)
    (hd : Disjoint f.range.toSubmodule
      (selectedAnnihilatorSubrepresentation t A).toSubmodule) :
    ∃ (c : t) (D : IrreducibleCompactCoefficientRep.{uG, uC} G),
      ofRep D = c.val ∧ Nonempty (B.representation.Equiv D.obj.representation) := by
  classical
  let : Nontrivial B := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ G) B.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : B)
  have hfv : f v ≠ 0 := fun hz => hv (hf (hz.trans (map_zero f).symm))
  have hnot : f v ∉ selectedAnnihilatorSubrepresentation t A := by
    intro hmem
    have hzero : f v ∈ (⊥ : Submodule ℂ A) :=
      hd.le_bot ⟨⟨v, rfl⟩, hmem⟩
    exact hfv hzero
  have hex : ∃ (c : t) (D : IrreducibleCompactCoefficientRep.{uG, uC} G),
      ofRep D = c.val ∧
      ∃ g : A.representation.IntertwiningMap D.obj.representation, g (f v) ≠ 0 := by
    by_contra hn
    apply hnot
    rw [selectedAnnihilatorSubrepresentation, Subrepresentation.mem_iInf]
    intro c
    apply (mem_annihilatorSubrepresentation_iff (f v)).2
    intro D hD g
    by_contra hne
    exact hn ⟨c, D, hD, g, hne⟩
  obtain ⟨c, D, hD, g, hg⟩ := hex
  let : Representation.IsIrreducible D.obj.representation := D.property.1
  have hgf : g.comp f ≠ 0 := by
    intro hz
    exact hg (congrArg
      (fun q : B.representation.IntertwiningMap D.obj.representation => q v) hz)
  exact ⟨c, D, hD, ⟨(g.comp f).ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero (g.comp f)).resolve_right hgf)⟩⟩

/-- Every irreducible subrepresentation of a summand disjoint from the selected
annihilator has one of the selected types. -/
theorem subrepresentation_type_of_disjoint_selectedAnnihilator
    (t : Finset (CompactCoefficientClass.{uG, uC} G))
    {A : SmoothRep.{0, uG, uV} ℂ G} (S : Subrepresentation A.representation)
    (hd : Disjoint S.toSubmodule
      (selectedAnnihilatorSubrepresentation t A).toSubmodule)
    (W : Subrepresentation S.toRepresentation)
    [Representation.IsIrreducible W.toRepresentation] :
    ∃ (c : t) (D : IrreducibleCompactCoefficientRep.{uG, uC} G),
      ofRep D = c.val ∧ Nonempty (W.toRepresentation.Equiv D.obj.representation) := by
  let B := SmoothRep.subrepresentation (SmoothRep.subrepresentation A S) W
  let : Representation.IsIrreducible B.representation :=
    inferInstanceAs (Representation.IsIrreducible W.toRepresentation)
  let f : B.representation.IntertwiningMap A.representation :=
    (SmoothRep.hom (SmoothRep.subtype A S)).comp
      (SmoothRep.hom (SmoothRep.subtype (SmoothRep.subrepresentation A S) W))
  apply exists_equiv_of_disjoint_selectedAnnihilator t f
  · exact Subtype.val_injective.comp Subtype.val_injective
  · apply hd.mono_left
    rintro _ ⟨w, rfl⟩
    exact w.val.property

/-- Type detection returns an index in the original family, even if the family
contains several equivalent representations. -/
theorem exists_equiv_finiteFamily_of_disjoint_selectedAnnihilator
    {ι : Type uI} [Fintype ι]
    (D : ι → IrreducibleCompactCoefficientRep.{uG, uC} G)
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}
    [Representation.IsIrreducible B.representation]
    (f : B.representation.IntertwiningMap A.representation)
    (hf : Function.Injective f)
    (hd : Disjoint f.range.toSubmodule
      (selectedAnnihilatorSubrepresentation (classesOfFiniteFamily D) A).toSubmodule) :
    ∃ i, Nonempty (B.representation.Equiv (D i).obj.representation) := by
  obtain ⟨c, E, hE, ⟨e⟩⟩ := exists_equiv_of_disjoint_selectedAnnihilator
    (classesOfFiniteFamily D) f hf hd
  obtain ⟨i, hi⟩ := (mem_classesOfFiniteFamily D c.val).1 c.property
  obtain ⟨a⟩ := (ofRep_eq_iff E (D i)).1 (hE.trans hi.symm)
  exact ⟨i, ⟨e.trans (SmoothRep.equivOfIso
    ((irreducibleCompactCoefficientProperty G).ι.mapIso a))⟩⟩

end Langlands.CompactCoefficientClass
