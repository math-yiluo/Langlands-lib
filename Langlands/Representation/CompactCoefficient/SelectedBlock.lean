import Langlands.Representation.CompactCoefficient.SelectedProjector
import Langlands.Representation.Category.RestrictionSubquotients

/-! Selected block objects and conditional exclusion of selected subquotients. -/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uC uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A selected representative is fixed by the selected projector. -/
theorem selectedProjectorOfIsCompl_fixes_representative
    (t : Finset (CompactCoefficientClass.{uG, uC} G))
    (D : IrreducibleCompactCoefficientRep.{uG, uC} G) (hD : ofRep D ∈ t)
    (h : ∀ c : t, IsCompl (isotypicSubrepresentation c.val D.obj).toSubmodule
      (annihilatorSubrepresentation c.val D.obj).toSubmodule) (v : D.obj) :
    selectedProjectorOfIsCompl t h v = v := by
  have hv : v ∈ selectedIsotypicSubrepresentation t D.obj :=
    (le_iSup (fun c : t => isotypicSubrepresentation c.val D.obj) ⟨ofRep D, hD⟩)
      (range_le_isotypicSubrepresentation D rfl
        (Representation.IntertwiningMap.id D.obj.representation) ⟨v, rfl⟩)
  rw [← selectedProjectorOfIsCompl_range t h] at hv
  obtain ⟨w, hw⟩ := hv
  rw [← hw]
  exact congrArg (fun q : D.obj →ₗ[ℂ] D.obj => q w)
    (selectedProjectorOfIsCompl_idempotent t h)

/-- An object embedded in the common annihilator has no selected representative
as a subquotient, provided the intrinsic complements exist on all intermediate
smooth representations. -/
theorem not_isSubquotient_of_range_le_selectedAnnihilator
    (t : Finset (CompactCoefficientClass.{uG, uV} G))
    (h : ∀ (B : SmoothRep.{0, uG, uV} ℂ G) (c : t),
      IsCompl (isotypicSubrepresentation c.val B).toSubmodule
        (annihilatorSubrepresentation c.val B).toSubmodule)
    (D : IrreducibleCompactCoefficientRep.{uG, uV} G) (hD : ofRep D ∈ t)
    {A Q : SmoothRep.{0, uG, uV} ℂ G}
    (f : Q.representation.IntertwiningMap A.representation) (hf : Function.Injective f)
    (hQ : f.range ≤ selectedAnnihilatorSubrepresentation t A) :
    ¬ SmoothRep.IsSubquotient D.obj Q := by
  intro hs
  have hzeroQ : ∀ v : Q, selectedProjectorOfIsCompl t (h Q) v = 0 := by
    intro v
    apply hf
    rw [map_zero, ← selectedProjectorOfIsCompl_natural t (h Q) (h A) f v]
    have hv := hQ ⟨v, rfl⟩
    rw [← selectedProjectorOfIsCompl_ker t (h A)] at hv
    exact hv
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hs
  have hzeroC : ∀ v : C, selectedProjectorOfIsCompl t (h C) v = 0 := by
    intro v
    apply hi
    rw [map_zero, ← selectedProjectorOfIsCompl_natural t (h C) (h Q) (SmoothRep.hom i) v,
      hzeroQ]
  let : Representation.IsIrreducible D.obj.representation := D.property.1
  let : Nontrivial D.obj := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ G) D.obj.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : D.obj)
  obtain ⟨w, hw⟩ := hq v
  apply hv
  calc
    v = selectedProjectorOfIsCompl t (h D.obj) v :=
      (selectedProjectorOfIsCompl_fixes_representative t D hD (h D.obj) v).symm
    _ = SmoothRep.hom q (selectedProjectorOfIsCompl t (h C) w) := by
      rw [← hw]
      exact selectedProjectorOfIsCompl_natural t (h C) (h D.obj) (SmoothRep.hom q) w
    _ = 0 := by rw [hzeroC, map_zero]

section Ambient

variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (t : Finset (CompactCoefficientClass.{uG, uC} N))
    (ht : ∀ (g : G) c, c ∈ t ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈ t)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (h : ∀ c : t,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule)

/-- The actual invariant selected block and its complementary annihilator block. -/
def selectedBlockPair : Subrepresentation A.representation × Subrepresentation A.representation :=
  ((ambientSelectedProjector N t ht h).range, (ambientSelectedProjector N t ht h).ker)

theorem selectedBlockPair_isCompl :
    IsCompl (selectedBlockPair N t ht A h).1.toSubmodule
      (selectedBlockPair N t ht A h).2.toSubmodule :=
  LinearMap.IsIdempotentElem.isCompl (ambientSelectedProjector_idempotent N t ht h)

end Ambient

/-- A selected actual subrepresentation of the restricted candidate excludes the
candidate from the ambient annihilator block. -/
theorem selectedBlockPair_not_isSubquotient
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (t : Finset (CompactCoefficientClass.{uG, uV} N))
    (ht : ∀ (g : G) c, c ∈ t ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈ t)
    (h : ∀ (B : SmoothRep.{0, uG, uV} ℂ N) (c : t),
      IsCompl (isotypicSubrepresentation c.val B).toSubmodule
        (annihilatorSubrepresentation c.val B).toSubmodule)
    (A D : SmoothRep.{0, uG, uV} ℂ G)
    (W : Subrepresentation (SmoothRep.restrictSubgroup N D).representation)
    (hWirr : Representation.IsIrreducible W.toRepresentation)
    (hWcomp : HasCompactSmoothDualCoefficients W.toRepresentation)
    (hW : ofRep (⟨SmoothRep.subrepresentation (SmoothRep.restrictSubgroup N D) W,
      hWirr, hWcomp⟩ : IrreducibleCompactCoefficientRep.{uG, uV} N) ∈ t) :
    ¬ SmoothRep.IsSubquotient D
      (SmoothRep.subrepresentation A
        (selectedBlockPair N t ht A (h (SmoothRep.restrictSubgroup N A))).2) := by
  let Q := (selectedBlockPair N t ht A (h (SmoothRep.restrictSubgroup N A))).2
  let E : IrreducibleCompactCoefficientRep.{uG, uV} N :=
    ⟨SmoothRep.subrepresentation (SmoothRep.restrictSubgroup N D) W, hWirr, hWcomp⟩
  apply SmoothRep.not_isSubquotient_of_restricted_subrepresentation N W
  apply not_isSubquotient_of_range_le_selectedAnnihilator t h E hW
    (SmoothRep.restrictSubgroupMap N (SmoothRep.hom (SmoothRep.subtype A Q)))
  · exact SmoothRep.subtype_injective A Q
  · rintro _ ⟨v, rfl⟩
    change (v.val : A) ∈
      (selectedAnnihilatorSubrepresentation t (SmoothRep.restrictSubgroup N A)).toSubmodule
    rw [← ambientSelectedProjector_ker N t ht (h (SmoothRep.restrictSubgroup N A))]
    exact v.property

end Langlands.CompactCoefficientClass
