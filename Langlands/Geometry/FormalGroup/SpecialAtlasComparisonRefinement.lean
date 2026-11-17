import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChangeRefinement
import Langlands.Geometry.FormalGroup.SpecialAtlasClassReduction

/-! # Source squares for refinement through supplied scalars and reduction -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra 𝒪[K] R}
variable {X Y : (letI := α; SpecialAtlas K D ι R)}

/-- The actual left and right source maps intertwine the two specified comparisons. -/
def ComparisonSourceSquare (c d : (letI := α; Comparison X Y)) : Prop :=
  letI := α
  ∃ (hL : c.left.opens = d.left.opens) (hR : c.right.opens = d.right.opens),
    (c.left.orderSourceIso X.order d.left hL).trans d.coordinateIso =
      c.coordinateIso.trans (c.right.orderSourceIso Y.order d.right hR)

set_option backward.isDefEq.respectTransparency false in
/-- Inverting both actual source changes reverses the square. -/
theorem ComparisonSourceSquare.symm {c d : (letI := α; Comparison X Y)}
    (h : (letI := α; ComparisonSourceSquare c d)) :
    (letI := α; ComparisonSourceSquare d c) := by
  let _ := α
  obtain ⟨hL, hR, hs⟩ := h
  refine ⟨hL.symm, hR.symm, ?_⟩
  let sl := c.left.orderSourceIso X.order d.left hL
  let sr := c.right.orderSourceIso Y.order d.right hR
  have ht : d.coordinateIso.hom.comp sl.hom = sr.hom.comp c.coordinateIso.hom :=
    congrArg BasicAtlas.OrderAction.Iso.hom hs
  apply BasicAtlas.OrderAction.Iso.ext_hom
  change c.coordinateIso.hom.comp sl.inv = sr.inv.comp d.coordinateIso.hom
  calc
    c.coordinateIso.hom.comp sl.inv =
        (sr.inv.comp sr.hom).comp (c.coordinateIso.hom.comp sl.inv) := by
      rw [sr.inv_hom, BasicAtlas.OrderAction.Hom.id_comp]
    _ = sr.inv.comp ((sr.hom.comp c.coordinateIso.hom).comp sl.inv) := by
      simp only [BasicAtlas.OrderAction.Hom.comp_assoc]
    _ = sr.inv.comp ((d.coordinateIso.hom.comp sl.hom).comp sl.inv) := by rw [← ht]
    _ = sr.inv.comp d.coordinateIso.hom := by
      rw [BasicAtlas.OrderAction.Hom.comp_assoc, sl.hom_inv,
        BasicAtlas.OrderAction.Hom.comp_id]

/-- Transport an actual further refinement with the scalar-retyped comparison. -/
def reAlgebraComparisonRefinement (c : (letI := α; Comparison X Y))
    (q : (letI := α; BasicAtlas.CoverRefinement c.left.atlas))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; BasicAtlas.CoverRefinement (reAlgebraComparison c β e).left.atlas) := by
  cases e
  exact q

/-- Scalar retyping retains the specified refined comparison. -/
theorem reAlgebraComparison_refine (c : (letI := α; Comparison X Y))
    (q : (letI := α; BasicAtlas.CoverRefinement c.left.atlas))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := α; reAlgebraComparison (c.refine q) β e) =
      (letI := β; (reAlgebraComparison c β e).refine
        (reAlgebraComparisonRefinement c q β e)) := by
  cases e
  rfl

/-- Retyping equal scalars retains the complete actual source square. -/
theorem comparisonSourceSquare_reAlgebra (c d : (letI := α; Comparison X Y))
    (h : (letI := α; ComparisonSourceSquare c d))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; ComparisonSourceSquare
      (reAlgebraComparison c β e) (reAlgebraComparison d β e)) := by
  cases e
  exact h

end AlgebraTransport

variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]
variable {X Y : SpecialAtlas K D ι R}

/-- Extend the actual further cover to the supplied target scalar structure. -/
def baseChangeAlongComparisonRefinement (g : Comparison X Y)
    (q : BasicAtlas.CoverRefinement g.left.atlas) (f : R →ₐ[𝒪[K]] S) :
    BasicAtlas.CoverRefinement (baseChangeAlongComparison g f).left.atlas :=
  reAlgebraComparisonRefinement (baseChangeComparison g (BasicAtlas.coefficientTest f))
    (g.baseChangeRefinement q (BasicAtlas.coefficientTest f)) _
    (BasicAtlas.coefficientAlgebraAlong_eq f)

set_option backward.isDefEq.respectTransparency false in
/-- Refinement and supplied-target extension commute through the actual source maps. -/
theorem baseChangeAlongComparison_refine_source_square (g : Comparison X Y)
    (q : BasicAtlas.CoverRefinement g.left.atlas) (f : R →ₐ[𝒪[K]] S) :
    ComparisonSourceSquare (baseChangeAlongComparison (g.refine q) f)
      ((baseChangeAlongComparison g f).refine (baseChangeAlongComparisonRefinement g q f)) := by
  let T : CommAlgCat.{v} R := BasicAtlas.coefficientTest f
  have hs : (letI := coefficientAlgebra (O := 𝒪[K]) T
    ComparisonSourceSquare
      (baseChangeComparison (g.refine q) T)
      ((baseChangeComparison g T).refine
        (g.baseChangeRefinement q T))) :=
    ⟨rfl, rfl, g.baseChange_refine_source_square q T⟩
  have ht := comparisonSourceSquare_reAlgebra _ _ hs _
    (BasicAtlas.coefficientAlgebraAlong_eq f)
  rw [reAlgebraComparison_refine] at ht
  exact ht

variable {r : R} {A : Nilp.{v, u} R r}

/-- The extended further cover for the same specified comparison after quotient reduction. -/
def reductionComparisonRefinement {X Y : SpecialAtlas K D ι A.obj}
    (g : Comparison X Y) (q : BasicAtlas.CoverRefinement g.left.atlas) :
    BasicAtlas.CoverRefinement (reductionComparison g).left.atlas :=
  baseChangeAlongComparisonRefinement g q (Nilp.quotientO 𝒪[K] A)

/-- Quotient reduction and refinement retain their actual source-corrected square. -/
theorem reductionComparison_refine_source_square {X Y : SpecialAtlas K D ι A.obj}
    (g : Comparison X Y) (q : BasicAtlas.CoverRefinement g.left.atlas) :
    ComparisonSourceSquare (reductionComparison (g.refine q))
      ((reductionComparison g).refine (reductionComparisonRefinement g q)) :=
  baseChangeAlongComparison_refine_source_square g q (Nilp.quotientO 𝒪[K] A)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
