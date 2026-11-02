import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartPullbackLimits
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering

/-! # Weighted rational comparisons over a rational target -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
/-- Unit generation makes bounded maps out of a rational quotient determined
by their composites with its actual structural map. -/
theorem hom_ext_base (d : RationalChart K A)
    {E : Type v} [NormedCommRing E] [NormedAlgebra K E]
    {α β : BoundedAlgHom K d.algebra E}
    (h : α.comp d.baseMap = β.comp d.baseMap) : α = β :=
  RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
    E d.generates α β h

namespace Restriction

variable {e d : RationalChart K A} (h : e ⟶ d)

/-- The actual quotient pushout constructs an inverse comparison whenever
there is an actual bounded restriction to the rational target. -/
def relativeInverse : BoundedAlgHom K (pullback d.baseMap e).algebra e.algebra :=
  RationalPresentation.BaseChange.pushoutLift
    (pullback_denominator_class d.baseMap e).symm
    (fun j => (pullback_numerator_class d.baseMap e j).symm)
    e.algebra (BoundedAlgHom.id K e.algebra) h.restriction
    (by
      change e.baseMap = h.restriction.comp d.baseMap
      exact h.comp_baseMap.symm)

@[simp]
theorem relativeInverse_comp_baseMap :
    h.relativeInverse.comp (pullback d.baseMap e).baseMap = h.restriction :=
  RationalPresentation.BaseChange.pushoutLift_comp_baseMap
    (pullback_denominator_class d.baseMap e).symm
    (fun j => (pullback_numerator_class d.baseMap e j).symm)
    e.algebra (BoundedAlgHom.id K e.algebra) h.restriction
    (by
      change e.baseMap = h.restriction.comp d.baseMap
      exact h.comp_baseMap.symm)

@[simp]
theorem relativeInverse_comp_pullbackMap :
    h.relativeInverse.comp (pullbackMap d.baseMap e) =
      BoundedAlgHom.id K e.algebra :=
  RationalPresentation.BaseChange.pushoutLift_comp_transport
    (pullback_denominator_class d.baseMap e).symm
    (fun j => (pullback_numerator_class d.baseMap e j).symm)
    e.algebra (BoundedAlgHom.id K e.algebra) h.restriction
    (by
      change e.baseMap = h.restriction.comp d.baseMap
      exact h.comp_baseMap.symm)

/-- Quotient transport takes the old restriction to the new structural map. -/
theorem pullbackMap_comp_restriction :
    (pullbackMap d.baseMap e).comp h.restriction =
      (pullback d.baseMap e).baseMap := by
  apply d.hom_ext_base
  rw [BoundedAlgHom.comp_assoc, h.comp_baseMap, pullbackMap_comp_baseMap]

@[simp]
theorem pullbackMap_comp_relativeInverse :
    (pullbackMap d.baseMap e).comp h.relativeInverse =
      BoundedAlgHom.id K (pullback d.baseMap e).algebra := by
  apply (pullback d.baseMap e).hom_ext_base
  rw [BoundedAlgHom.comp_assoc, h.relativeInverse_comp_baseMap,
    h.pullbackMap_comp_restriction, BoundedAlgHom.id_comp]

/-- Both bounded maps and their inverse laws are constructed from the
weighted quotient pushout and rational-map uniqueness. -/
def relativeEquiv :
    BoundedAlgEquiv K e.algebra (pullback d.baseMap e).algebra :=
  BoundedAlgEquiv.ofHomInv (pullbackMap d.baseMap e) h.relativeInverse
    (fun a => congrArg (fun f => f a) h.relativeInverse_comp_pullbackMap)
    (fun a => congrArg (fun f => f a) h.pullbackMap_comp_relativeInverse)

include h in
theorem pullbackMap_injective : Function.Injective (pullbackMap d.baseMap e) :=
  h.relativeEquiv.toAlgEquiv.injective

end Restriction

omit [CompleteSpace K] in
/-- A cover of a rational target pulls back to a whole-spectrum cover of
its actual weighted quotient algebra. -/
theorem FamilyCovers.relative {I : Type u} {d : RationalChart K A}
    {D : I → RationalChart K A} (hc : FamilyCovers d D) :
    ∀ x : BanachSpectrum d.algebra, ∃ i, x ∈ (pullback d.baseMap (D i)).locus := by
  intro x
  obtain ⟨i, hi⟩ := hc _ (d.locusHomeomorph x).property
  refine ⟨i, ?_⟩
  rw [pullback_locus]
  exact hi

/-- Compare the actual pullback of a chosen product intersection with the
chosen intersection after pullback, using the proved representative isomorphism. -/
def intersectionComparison (φ : BoundedAlgHom K A B) (d e : RationalChart K A) :
    BoundedAlgHom K (d.inter e).algebra
      ((pullback φ d).inter (pullback φ e)).algebra :=
  (pullbackInterIso φ d e).inv.restriction.comp (pullbackMap φ (d.inter e))

theorem intersectionComparison_comp_baseMap (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) :
    (intersectionComparison φ d e).comp (d.inter e).baseMap =
      ((pullback φ d).inter (pullback φ e)).baseMap.comp φ := by
  rw [intersectionComparison, BoundedAlgHom.comp_assoc, pullbackMap_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, Restriction.comp_baseMap]

theorem intersectionComparison_comp_left (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) :
    (intersectionComparison φ d e).comp (interLeft d e).restriction =
      (interLeft (pullback φ d) (pullback φ e)).restriction.comp
        (pullbackMap φ d) := by
  apply d.hom_ext_base
  rw [BoundedAlgHom.comp_assoc, Restriction.comp_baseMap,
    intersectionComparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    pullbackMap_comp_baseMap, ← BoundedAlgHom.comp_assoc, Restriction.comp_baseMap]

theorem intersectionComparison_comp_right (φ : BoundedAlgHom K A B)
    (d e : RationalChart K A) :
    (intersectionComparison φ d e).comp (interRight d e).restriction =
      (interRight (pullback φ d) (pullback φ e)).restriction.comp
        (pullbackMap φ e) := by
  apply e.hom_ext_base
  rw [BoundedAlgHom.comp_assoc, Restriction.comp_baseMap,
    intersectionComparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    pullbackMap_comp_baseMap, ← BoundedAlgHom.comp_assoc, Restriction.comp_baseMap]

/-- Compatible elements of the actual quotient rings remain compatible on
the chosen weighted product intersections after bounded coefficient change. -/
theorem compatible_pullbackMap {I : Type v} (D : I → RationalChart K A)
    (φ : BoundedAlgHom K A B) (s : ∀ i, (D i).algebra)
    (hs : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∀ i j, (interLeft (pullback φ (D i)) (pullback φ (D j))).restriction
        (pullbackMap φ (D i) (s i)) =
      (interRight (pullback φ (D i)) (pullback φ (D j))).restriction
        (pullbackMap φ (D j) (s j)) := by
  intro i j
  have hl := congrArg (fun f => f (s i))
    (intersectionComparison_comp_left φ (D i) (D j))
  have hr := congrArg (fun f => f (s j))
    (intersectionComparison_comp_right φ (D i) (D j))
  exact hl.symm.trans
    ((congrArg (intersectionComparison φ (D i) (D j)) (hs i j)).trans hr)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
