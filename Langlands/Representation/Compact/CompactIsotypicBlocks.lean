import Langlands.Representation.Compact.CompactBlockDecompositionStatements
import Langlands.Representation.CompactCoefficient.CompactIsotypicComplementProof
import Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
import Langlands.Representation.Category.IdempotentDecomposition

/-! # Intrinsic projectors and the compact block predicates -/

noncomputable section

universe u v

open CategoryTheory MeasureTheory
open Langlands.CompactCoefficientClass

namespace Langlands.Renard.CompactRepresentation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Cofinality of compact open subgroups in the ambient hypotheses. -/
theorem blockCompactOpenCofinal (K : OpenSubgroup G) :
    ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
  obtain ⟨L, hLK, hL, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
  exact ⟨L, hL, hLK⟩

variable (μ : Measure G) [μ.IsHaarMeasure]

include μ in
/-- The published intrinsic complementary pair, with compact-open cofinality discharged. -/
theorem blockIsCompl (c : CompactCoefficientClass.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) :
    IsCompl (isotypicSubrepresentation c A).toSubmodule
      (annihilatorSubrepresentation c A).toSubmodule :=
  CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
    μ blockCompactOpenCofinal c A

/-- The intrinsic compact-isotypic projector. -/
def blockProjector (c : CompactCoefficientClass.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) : A.representation.IntertwiningMap A.representation :=
  isotypicProjectorOfIsCompl c (blockIsCompl μ c A)

@[simp] theorem blockProjector_range (c : CompactCoefficientClass.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) :
    (blockProjector μ c A).range = isotypicSubrepresentation c A :=
  isotypicProjectorOfIsCompl_range c (blockIsCompl μ c A)

@[simp] theorem blockProjector_ker (c : CompactCoefficientClass.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) :
    (blockProjector μ c A).ker = annihilatorSubrepresentation c A :=
  isotypicProjectorOfIsCompl_ker c (blockIsCompl μ c A)

theorem blockProjector_idempotent (c : CompactCoefficientClass.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) (x : A) :
    blockProjector μ c A (blockProjector μ c A x) = blockProjector μ c A x :=
  LinearMap.congr_fun (isotypicProjectorOfIsCompl_idempotent c (blockIsCompl μ c A)) x

theorem blockProjector_natural (c : CompactCoefficientClass.{u, v} G)
    {A B : SmoothRep.{0, u, v} ℂ G} (f : A ⟶ B) (x : A) :
    blockProjector μ c B (SmoothRep.hom f x) = SmoothRep.hom f (blockProjector μ c A x) :=
  (isotypicProjectorOfIsCompl_natural c (blockIsCompl μ c A) (blockIsCompl μ c B)
    (SmoothRep.hom f) x).symm

theorem blockProjector_orthogonal {c d : CompactCoefficientClass.{u, v} G} (hcd : c ≠ d)
    (A : SmoothRep.{0, u, v} ℂ G) (x : A) :
    blockProjector μ c A (blockProjector μ d A x) = 0 :=
  congrArg (fun f : A.representation.IntertwiningMap A.representation => f x)
    (isotypicProjectorFamilyOfIsCompl_orthogonal (blockIsCompl μ) hcd.symm A)

/-- A compact representative is fixed by its own isotypic projector. -/
theorem blockProjector_rep (D : IrreducibleCompactCoefficientRep.{u, v} G) (x : D.obj) :
    blockProjector μ (ofRep D) D.obj x = x := by
  have hx : x ∈ (blockProjector μ (ofRep D) D.obj).range := by
    rw [blockProjector_range]
    exact range_le_isotypicSubrepresentation D rfl
      (Representation.IntertwiningMap.id _) ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := hx
  exact blockProjector_idempotent μ _ _ y

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The internal direct-sum predicate exhausts the intrinsic isotypic subrepresentation. -/
theorem isotypicSubrepresentation_eq_top_of_isotypicPart
    (c : CompactCoefficientClass.{u, v} G) (A : SmoothRep.{0, u, v} ℂ G)
    (hA : isotypicPart G c A) : isotypicSubrepresentation c A = ⊤ := by
  obtain ⟨ι, W, -, hspan, hW⟩ := hA
  apply top_unique
  rw [← hspan]
  refine iSup_le fun i => ?_
  obtain ⟨hi, hci⟩ := hW i
  have hrange : (SmoothRep.hom (SmoothRep.subtype A (W i))).range = W i := by
    ext x
    exact ⟨fun ⟨w, hw⟩ => hw ▸ w.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [← hrange]
  exact range_le_isotypicSubrepresentation ⟨_, hi⟩ hci _

/-- Zero action of the selected projectors is exactly the avoiding predicate. -/
theorem avoidingPart_iff_blockProjector_zero
    (S : Set (CompactCoefficientClass.{u, v} G)) (A : SmoothRep.{0, u, v} ℂ G) :
    avoidingPart G S A ↔ ∀ c ∈ S, ∀ x : A, blockProjector μ c A x = 0 := by
  classical
  constructor
  · intro hA c hc
    have hzero (f : c.out.obj.representation.IntertwiningMap A.representation) : f = 0 := by
      by_contra hf
      let : Representation.IsIrreducible c.out.obj.representation := c.out.property.1
      have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
      have hsub := SmoothRep.IsSubrepresentation.isSubquotient
        (show SmoothRep.IsSubrepresentation c.out.obj A from ⟨SmoothRep.ofHom f, hi⟩)
      have hn : ofRep c.out ∉ S := hA c.out.obj c.out.property hsub
      have hout : ofRep c.out = c := Quotient.out_eq c
      exact hn (hout.symm ▸ hc)
    have hrange : (blockProjector μ c A).range = ⊥ := by
      rw [blockProjector_range, isotypicSubrepresentation_eq_iSup_range c.out (Quotient.out_eq c)]
      apply iSup_eq_bot.mpr
      intro f
      rw [hzero f]
      ext x
      change (∃ v, (0 : A) = x) ↔ x = 0
      simp only [exists_const, eq_comm]
    intro x
    have hx : blockProjector μ c A x ∈ (⊥ : Subrepresentation A.representation) :=
      hrange ▸ (show blockProjector μ c A x ∈ (blockProjector μ c A).range from ⟨x, rfl⟩)
    exact hx
  · intro hzero D hD hDA hclass
    let E : IrreducibleCompactCoefficientRep.{u, v} G := ⟨D, hD⟩
    obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDA
    have hC (x : C) : blockProjector μ (ofRep E) C x = 0 := by
      apply hi
      rw [← blockProjector_natural μ, hzero _ hclass, map_zero]
    let : Representation.IsIrreducible D.representation := hD.1
    let : Nontrivial D := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) D.representation.asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    obtain ⟨y, rfl⟩ := hq x
    apply hx
    rw [← blockProjector_rep μ E (SmoothRep.hom q y), blockProjector_natural μ, hC, map_zero]

variable [SigmaCompactSpace G] [μ.Regular] [μ.IsMulRightInvariant]

include μ in
/-- Exhaustion by the intrinsic isotypic part supplies the required carrier-small
independent family of compact irreducible subrepresentations. -/
theorem isotypicPart_of_isotypicSubrepresentation_eq_top
    (c : CompactCoefficientClass.{u, v} G) (A : SmoothRep.{0, u, v} ℂ G)
    (hA : isotypicSubrepresentation c A = ⊤) : isotypicPart G c A := by
  classical
  obtain ⟨⟨s, hinj, hind, hspan⟩, -⟩ := compactIsotypicComplement G μ c.out.obj
    c.out.property.1 c.out.property.2 A
  refine ⟨s, fun f => f.val.range, hind, ?_, ?_⟩
  · rw [hspan, ← isotypicSubrepresentation_eq_iSup_range c.out (Quotient.out_eq c), hA]
  · intro f
    let j : c.out.obj.representation.IntertwiningMap f.val.range.toRepresentation :=
      { toLinearMap := f.val.toLinearMap.rangeRestrict
        isIntertwining' g := by
          ext x
          exact Representation.IntertwiningMap.isIntertwining _ _ f.val g x }
    let e := j.ofBijective
      ⟨fun x y h => hinj f.val f.property (congrArg Subtype.val h),
        LinearMap.surjective_rangeRestrict _⟩
    have hj : irreducibleCompactCoefficientProperty G (SmoothRep.subrepresentation A f.val.range) :=
      ⟨(isIrreducible_iff_of_equiv e).mp c.out.property.1,
        (hasCompactSmoothDualCoefficients_iff_of_equiv e).mp c.out.property.2⟩
    refine ⟨hj, ?_⟩
    exact ((ofRep_eq_iff _ c.out).mpr
      ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso e.symm)⟩).trans (Quotient.out_eq c)

/-- The isotypic direct-sum predicate is equivalent to identity action of its projector. -/
theorem isotypicPart_iff_blockProjector_fixed
    (c : CompactCoefficientClass.{u, v} G) (A : SmoothRep.{0, u, v} ℂ G) :
    isotypicPart G c A ↔ ∀ x : A, blockProjector μ c A x = x := by
  constructor
  · intro hA x
    have hx : x ∈ (blockProjector μ c A).range := by
      rw [blockProjector_range, isotypicSubrepresentation_eq_top_of_isotypicPart c A hA]
      trivial
    obtain ⟨y, rfl⟩ := hx
    exact blockProjector_idempotent μ c A y
  · intro hA
    apply isotypicPart_of_isotypicSubrepresentation_eq_top μ c A
    apply top_unique
    intro x _
    rw [← blockProjector_range μ c A]
    exact ⟨x, hA x⟩

end Langlands.Renard.CompactRepresentation
