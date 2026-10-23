import Langlands.Representation.CompactCoefficient.AmbientProjector

/-! Finite selected-class projectors, conditional on intrinsic complements. -/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uH uC uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The sum of the intrinsic parts for a finite set of distinct classes. -/
def selectedIsotypicSubrepresentation
    (t : Finset (CompactCoefficientClass.{uG, uC} G))
    (A : SmoothRep.{0, uG, uV} ℂ G) : Subrepresentation A.representation :=
  ⨆ c : t, isotypicSubrepresentation c.val A

/-- The common intrinsic annihilator for a finite set of distinct classes. -/
def selectedAnnihilatorSubrepresentation
    (t : Finset (CompactCoefficientClass.{uG, uC} G))
    (A : SmoothRep.{0, uG, uV} ℂ G) : Subrepresentation A.representation :=
  ⨅ c : t, annihilatorSubrepresentation c.val A

section Selected

variable (t : Finset (CompactCoefficientClass.{uG, uC} G))
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (h : ∀ c : t, IsCompl (isotypicSubrepresentation c.val A).toSubmodule
      (annihilatorSubrepresentation c.val A).toSubmodule)

/-- Sum the intrinsic projectors only over the supplied finite set.
Complementarity is required only for its selected classes. -/
def selectedProjectorOfIsCompl : A.representation.IntertwiningMap A.representation :=
  pointwiseFiniteSum (fun c : t => isotypicProjectorOfIsCompl c.val (h c))
    (fun _ => Set.toFinite _)

private theorem selected_components_orthogonal (c d : t) (hcd : c ≠ d) (v : A) :
    isotypicProjectorOfIsCompl c.val (h c)
      (isotypicProjectorOfIsCompl d.val (h d) v) = 0 := by
  have hdc : d.val ≠ c.val := fun heq => hcd (Subtype.ext heq.symm)
  exact congrArg (fun f : A.representation.IntertwiningMap A.representation => f v)
    (comp_eq_zero_of_isotypic_range_annihilator_ker hdc
      (isotypicProjectorOfIsCompl d.val (h d))
      (isotypicProjectorOfIsCompl c.val (h c))
      (isotypicProjectorOfIsCompl_range d.val (h d)).le
      (isotypicProjectorOfIsCompl_ker c.val (h c)).symm.le)

private theorem selected_components_idempotent (c : t) (v : A) :
    isotypicProjectorOfIsCompl c.val (h c)
      (isotypicProjectorOfIsCompl c.val (h c) v) =
      isotypicProjectorOfIsCompl c.val (h c) v := by
  exact congrArg (fun f : A →ₗ[ℂ] A => f v)
    (isotypicProjectorOfIsCompl_idempotent c.val (h c))

theorem selectedProjectorOfIsCompl_idempotent :
    IsIdempotentElem (selectedProjectorOfIsCompl t h).toLinearMap := by
  apply LinearMap.ext
  intro v
  exact pointwiseFiniteSum_idempotent
    (fun c : t => isotypicProjectorOfIsCompl c.val (h c)) (fun _ => Set.toFinite _)
    (selected_components_idempotent t h)
    (selected_components_orthogonal t h) v

theorem selectedProjectorOfIsCompl_range :
    (selectedProjectorOfIsCompl t h).range = selectedIsotypicSubrepresentation t A := by
  rw [selectedProjectorOfIsCompl, pointwiseFiniteSum_range
    (fun c : t => isotypicProjectorOfIsCompl c.val (h c)) (fun _ => Set.toFinite _)
    (selected_components_idempotent t h)
    (selected_components_orthogonal t h)]
  exact iSup_congr fun c => isotypicProjectorOfIsCompl_range c.val (h c)

theorem selectedProjectorOfIsCompl_ker :
    (selectedProjectorOfIsCompl t h).ker = selectedAnnihilatorSubrepresentation t A := by
  rw [selectedProjectorOfIsCompl, pointwiseFiniteSum_ker
    (fun c : t => isotypicProjectorOfIsCompl c.val (h c)) (fun _ => Set.toFinite _)
    (selected_components_idempotent t h)
    (selected_components_orthogonal t h)]
  exact iInf_congr fun c => isotypicProjectorOfIsCompl_ker c.val (h c)

include h in
theorem selected_isCompl :
    IsCompl (selectedIsotypicSubrepresentation t A).toSubmodule
      (selectedAnnihilatorSubrepresentation t A).toSubmodule := by
  rw [← selectedProjectorOfIsCompl_range t h, ← selectedProjectorOfIsCompl_ker t h]
  exact LinearMap.IsIdempotentElem.isCompl (selectedProjectorOfIsCompl_idempotent t h)

/-- Selected sums are natural, including across independent ambient universes. -/
theorem selectedProjectorOfIsCompl_natural
    {B : SmoothRep.{0, uG, uW} ℂ G}
    (hB : ∀ c : t, IsCompl (isotypicSubrepresentation c.val B).toSubmodule
      (annihilatorSubrepresentation c.val B).toSubmodule)
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    selectedProjectorOfIsCompl t hB (f v) = f (selectedProjectorOfIsCompl t h v) :=
  pointwiseFiniteSum_covariant _ _ _ _ f.toLinearMap (Equiv.refl t)
    (fun c w => (isotypicProjectorOfIsCompl_natural c.val (h c) (hB c) f w).symm) v

end Selected

/-- Transport a selected set along a group equivalence. The membership
equivalence restricts class transport to a bijection of the two finite sets. -/
theorem selectedProjectorOfIsCompl_covariant
    {H : Type uH} [Group H] [TopologicalSpace H] (e : H ≃ₜ* G)
    (t : Finset (CompactCoefficientClass.{uG, uC} G))
    (s : Finset (CompactCoefficientClass.{uH, uC} H))
    (hs : ∀ c, c ∈ t ↔ pullbackEquiv e c ∈ s)
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uH, uW} ℂ H}
    (hA : ∀ c : t, IsCompl (isotypicSubrepresentation c.val A).toSubmodule
      (annihilatorSubrepresentation c.val A).toSubmodule)
    (hB : ∀ c : s, IsCompl (isotypicSubrepresentation c.val B).toSubmodule
      (annihilatorSubrepresentation c.val B).toSubmodule)
    (f : (SmoothRep.pullback e A).representation.IntertwiningMap B.representation)
    (v : A) :
    selectedProjectorOfIsCompl s hB (f v) = f (selectedProjectorOfIsCompl t hA v) := by
  let E : t ≃ s := (pullbackEquiv e).subtypeEquiv hs
  exact pointwiseFiniteSum_covariant
    (fun c : t => SmoothRep.pullbackMap e (isotypicProjectorOfIsCompl c.val (hA c)))
    (fun _ => Set.toFinite _) _ _ f.toLinearMap E
    (fun c w => (isotypicProjectors_covariant e c.val
      (isotypicProjectorOfIsCompl c.val (hA c))
      (isotypicProjectorOfIsCompl (E c).val (hB (E c)))
      (isotypicProjectorOfIsCompl_idempotent c.val (hA c))
      (isotypicProjectorOfIsCompl_idempotent (E c).val (hB (E c)))
      (isotypicProjectorOfIsCompl_range c.val (hA c))
      (isotypicProjectorOfIsCompl_ker c.val (hA c))
      (isotypicProjectorOfIsCompl_range (E c).val (hB (E c)))
      (isotypicProjectorOfIsCompl_ker (E c).val (hB (E c))) f w).symm) v

section Ambient

variable [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (t : Finset (CompactCoefficientClass.{uG, uC} N))
    (ht : ∀ (g : G) c, c ∈ t ↔
      pullbackEquiv (SmoothRep.normalSubgroupInverseConjugation N g) c ∈ t)
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (h : ∀ c : t,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N A)).toSubmodule)

/-- A conjugation-stable selection gives an actual ambient equivariant
projector, conditional only on the selected intrinsic complements. -/
def ambientSelectedProjector : A.representation.IntertwiningMap A.representation where
  toLinearMap := (selectedProjectorOfIsCompl t h).toLinearMap
  isIntertwining' g := by
    ext v
    exact selectedProjectorOfIsCompl_covariant
      (SmoothRep.normalSubgroupInverseConjugation N g) t t (ht g) h h
      (SmoothRep.restrictionConjugationMap N A g) v

theorem ambientSelectedProjector_idempotent :
    IsIdempotentElem (ambientSelectedProjector N t ht h).toLinearMap :=
  selectedProjectorOfIsCompl_idempotent t h

/-- The ambient range is exactly the selected intrinsic sum on restriction. -/
theorem ambientSelectedProjector_range :
    (ambientSelectedProjector N t ht h).range.toSubmodule =
      (selectedIsotypicSubrepresentation t (SmoothRep.restrictSubgroup N A)).toSubmodule :=
  congrArg Subrepresentation.toSubmodule (selectedProjectorOfIsCompl_range t h)

/-- The ambient kernel is exactly the common selected intrinsic annihilator. -/
theorem ambientSelectedProjector_ker :
    (ambientSelectedProjector N t ht h).ker.toSubmodule =
      (selectedAnnihilatorSubrepresentation t (SmoothRep.restrictSubgroup N A)).toSubmodule :=
  congrArg Subrepresentation.toSubmodule (selectedProjectorOfIsCompl_ker t h)

theorem ambientSelectedProjector_natural
    {B : SmoothRep.{0, uG, uW} ℂ G}
    (hB : ∀ c : t,
      IsCompl (isotypicSubrepresentation c.val (SmoothRep.restrictSubgroup N B)).toSubmodule
        (annihilatorSubrepresentation c.val (SmoothRep.restrictSubgroup N B)).toSubmodule)
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    ambientSelectedProjector N t ht hB (f v) =
      f (ambientSelectedProjector N t ht h v) :=
  selectedProjectorOfIsCompl_natural t h hB (SmoothRep.restrictSubgroupMap N f) v

end Ambient

end Langlands.CompactCoefficientClass
