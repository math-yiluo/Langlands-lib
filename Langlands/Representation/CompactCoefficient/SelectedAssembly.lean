import Langlands.Representation.CompactCoefficient.SelectedBlock
import Langlands.Representation.CompactCoefficient.SelectedConjugation
import Langlands.Representation.CompactCoefficient.TotalCompactness

/-! Assembly of finite-type isolation from a supplied finite restriction family. -/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal]

/-- The actual selected range/kernel pair determined by a finite spanning
family in the restriction of an ambient object. -/
def finiteFamilyBlockPair
    {ι : Type uI} [Fintype ι]
    (E : ι → IrreducibleCompactCoefficientRep.{uG, uV} N)
    (D : SmoothRep.{0, uG, uV} ℂ G)
    (f : ∀ i, (E i).obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N D).representation)
    (hf : ∀ i, Function.Injective (f i))
    (hspan : (⨆ i, (f i).range.toSubmodule) = ⊤)
    (hsplit : ∀ (c : CompactCoefficientClass.{uG, uV} N)
      (X : SmoothRep.{0, uG, uV} ℂ N),
      IsCompl (isotypicSubrepresentation c X).toSubmodule
        (annihilatorSubrepresentation c X).toSubmodule)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    Subrepresentation A.representation × Subrepresentation A.representation :=
  selectedBlockPair N (classesOfFiniteFamily E)
    (mem_classesOfFiniteFamily_conjugation_iff N E f hf hspan
      (fun c => hsplit c.val (SmoothRep.restrictSubgroup N D))) A
    (fun c => hsplit c.val (SmoothRep.restrictSubgroup N A))

variable
    [T2Space N] [LocallyCompactSpace N] [TotallyDisconnectedSpace N]
    [MeasurableSpace N] [BorelSpace N]
    (μ : MeasureTheory.Measure N) [μ.IsHaarMeasure]

include μ in
/-- A finite spanning family in the compact restriction of an irreducible
object yields block isolation, assuming intrinsic complementarity. -/
theorem finiteFamilyBlockIsolation_of_isCompl
    (hsplit : ∀ (c : CompactCoefficientClass.{uG, uV} N)
      (X : SmoothRep.{0, uG, uV} ℂ N),
      IsCompl (isotypicSubrepresentation c X).toSubmodule
        (annihilatorSubrepresentation c X).toSubmodule)
    (A D : SmoothRep.{0, uG, uV} ℂ G) (hD : D.IsIrreducible)
    (hcD : HasCompactSmoothDualCoefficients (SmoothRep.restrictSubgroup N D).representation)
    {ι : Type uI} [Fintype ι]
    (V : ι → Subrepresentation (SmoothRep.restrictSubgroup N D).representation)
    (hV : ∀ i, Representation.IsIrreducible (V i).toRepresentation)
    (hspan : (⨆ i, (V i).toSubmodule) = ⊤) :
    Representation.IsSemisimpleRepresentation (SmoothRep.restrictSubgroup N D).representation ∧
      ∃ (S Q : Subrepresentation A.representation),
        IsCompl S.toSubmodule Q.toSubmodule ∧
        Representation.IsSemisimpleRepresentation
          (SmoothRep.restrictSubgroup N (SmoothRep.subrepresentation A S)).representation ∧
        (∀ W : Subrepresentation
          (SmoothRep.restrictSubgroup N (SmoothRep.subrepresentation A S)).representation,
          Representation.IsIrreducible W.toRepresentation →
          ∃ i, Nonempty (W.toRepresentation.Equiv (V i).toRepresentation)) ∧
        ¬ SmoothRep.IsSubquotient D (SmoothRep.subrepresentation A Q) := by
  classical
  have hcof : ∀ K : OpenSubgroup N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance N ∅ K
    exact ⟨L, hL, hLK⟩
  let E : ι → IrreducibleCompactCoefficientRep.{uG, uV} N := fun i =>
    ⟨SmoothRep.subrepresentation (SmoothRep.restrictSubgroup N D) (V i), hV i,
      hasCompactSmoothDualCoefficients_subrepresentation hcof
        (SmoothRep.restrictSubgroup N D) hcD (V i)⟩
  let f : ∀ i, (E i).obj.representation.IntertwiningMap
      (SmoothRep.restrictSubgroup N D).representation := fun i =>
    SmoothRep.hom (SmoothRep.subtype (SmoothRep.restrictSubgroup N D) (V i))
  have hf : ∀ i, Function.Injective (f i) := fun _ => Subtype.val_injective
  have hfrange : ∀ i, (f i).range.toSubmodule = (V i).toSubmodule := by
    intro i
    ext v
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property, fun hv => ⟨⟨v, hv⟩, rfl⟩⟩
  have hfspan : (⨆ i, (f i).range.toSubmodule) = ⊤ := by
    simpa only [hfrange] using hspan
  let t := classesOfFiniteFamily E
  have ht : ∀ (g : G) c, c ∈ t ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈ t :=
    mem_classesOfFiniteFamily_conjugation_iff N E f hf hfspan
      (fun c => hsplit c.val (SmoothRep.restrictSubgroup N D))
  let h : ∀ (X : SmoothRep.{0, uG, uV} ℂ N) (c : t),
      IsCompl (isotypicSubrepresentation c.val X).toSubmodule
        (annihilatorSubrepresentation c.val X).toSubmodule :=
    fun X c => hsplit c.val X
  let S := (finiteFamilyBlockPair N E D f hf hfspan hsplit A).1
  let Q := (finiteFamilyBlockPair N E D f hf hfspan hsplit A).2
  have hS : S.toSubmodule =
      (selectedIsotypicSubrepresentation t (SmoothRep.restrictSubgroup N A)).toSubmodule :=
    ambientSelectedProjector_range N t ht (h (SmoothRep.restrictSubgroup N A))
  refine ⟨CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
    μ _ (SmoothRep.restrictSubgroup N D).isSmooth hcD, S, Q,
    selectedBlockPair_isCompl N t ht A (h (SmoothRep.restrictSubgroup N A)), ?_, ?_, ?_⟩
  · let SN : Subrepresentation (SmoothRep.restrictSubgroup N A).representation :=
      ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule g.val hv⟩
    have hSN : SN.toSubmodule ≤
        compactCoefficientVectors (SmoothRep.restrictSubgroup N A).representation := by
      change S.toSubmodule ≤ _
      rw [hS]
      apply le_trans _ (totalIsotypicSubrepresentation_le_compactCoefficientVectors
        (SmoothRep.restrictSubgroup N A))
      change selectedIsotypicSubrepresentation t (SmoothRep.restrictSubgroup N A) ≤ _
      exact iSup_le fun c =>
        isotypicSubrepresentation_le_totalIsotypicSubrepresentation
          (SmoothRep.restrictSubgroup N A) c.val
    exact CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
      μ _ (SmoothRep.restrictSubgroup N (SmoothRep.subrepresentation A S)).isSmooth
      (hasCompactSmoothDualCoefficients_subrepresentation_of_le hcof
        (SmoothRep.restrictSubgroup N A) SN hSN)
  · intro W hW
    let B := SmoothRep.subrepresentation
      (SmoothRep.restrictSubgroup N (SmoothRep.subrepresentation A S)) W
    let : Representation.IsIrreducible B.representation := hW
    let j : B.representation.IntertwiningMap
        (SmoothRep.restrictSubgroup N A).representation :=
      (SmoothRep.restrictSubgroupMap N (SmoothRep.hom (SmoothRep.subtype A S))).comp
        (SmoothRep.hom (SmoothRep.subtype
          (SmoothRep.restrictSubgroup N (SmoothRep.subrepresentation A S)) W))
    have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
    have hrange : j.range.toSubmodule ≤
        (selectedIsotypicSubrepresentation t (SmoothRep.restrictSubgroup N A)).toSubmodule := by
      rw [← hS]
      rintro _ ⟨w, rfl⟩
      exact w.val.property
    exact exists_equiv_finiteFamily_of_disjoint_selectedAnnihilator E j hj
      ((selected_isCompl t (h (SmoothRep.restrictSubgroup N A))).disjoint.mono_left hrange)
  · let : Representation.IsIrreducible D.representation := hD
    let : Nontrivial D := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ G) D.representation.asModule
    have hi : Nonempty ι := by
      by_contra hn
      let : IsEmpty ι := not_nonempty_iff.mp hn
      have hb : (⊥ : Submodule ℂ (SmoothRep.restrictSubgroup N D)) = ⊤ := by
        simpa only [iSup_of_empty] using hspan
      obtain ⟨v, hv⟩ := exists_ne (0 : D)
      apply hv
      have hvbot : v ∈ (⊥ : Submodule ℂ (SmoothRep.restrictSubgroup N D)) := by
        rw [hb]
        trivial
      exact hvbot
    let i := Classical.choice hi
    exact selectedBlockPair_not_isSubquotient N t ht h A D (V i) (hV i)
      (E i).property.2 ((mem_classesOfFiniteFamily E _).2 ⟨i, rfl⟩)

end Langlands.CompactCoefficientClass
