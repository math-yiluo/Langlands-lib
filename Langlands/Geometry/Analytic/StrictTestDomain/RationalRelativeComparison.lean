import Langlands.Geometry.Analytic.StrictTestDomain.RationalContinuity
import Langlands.Geometry.Analytic.SpectrumNonemptyProof

/-! # Rational comparison over a target quotient -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

namespace Inclusion

variable {e d : RationalData K P} (h : e ⟶ d)

/-- Pulling an included rational domain back to the target quotient has a
bounded inverse comparison, obtained from the actual extension construction. -/
def relativeInverse : BoundedAlgHom K (e.pullback d.baseMap).algebra e.algebra :=
  e.extension d.baseMap (BoundedAlgHom.id K e.algebra) h.restriction
    (by simp)

@[simp]
theorem relativeInverse_comp_baseMap :
    h.relativeInverse.comp (e.pullback d.baseMap).baseMap = h.restriction :=
  e.extension_comp_baseMap d.baseMap _ _ _

@[simp]
theorem relativeInverse_comp_comparison :
    h.relativeInverse.comp (e.comparison d.baseMap) = BoundedAlgHom.id K e.algebra :=
  e.extension_comp_comparison d.baseMap _ _ _

/-- The relative comparison sends the original restriction to the new base map. -/
theorem comparison_comp_restriction :
    (e.comparison d.baseMap).comp h.restriction = (e.pullback d.baseMap).baseMap := by
  apply d.hom_ext
  rw [BoundedAlgHom.comp_assoc, h.restriction_comp_baseMap,
    e.comparison_comp_baseMap]

@[simp]
theorem comparison_comp_relativeInverse :
    (e.comparison d.baseMap).comp h.relativeInverse =
      BoundedAlgHom.id K (e.pullback d.baseMap).algebra := by
  apply (e.pullback d.baseMap).hom_ext
  rw [BoundedAlgHom.comp_assoc, h.relativeInverse_comp_baseMap,
    h.comparison_comp_restriction, BoundedAlgHom.id_comp]

/-- The actual comparison is a bounded algebra equivalence whenever the
original rational locus is included in the target locus. -/
def relativeEquiv : BoundedAlgEquiv K e.algebra (e.pullback d.baseMap).algebra :=
  BoundedAlgEquiv.ofHomInv (e.comparison d.baseMap) h.relativeInverse
    (fun a => congrArg (fun f => f a) h.relativeInverse_comp_comparison)
    (fun a => congrArg (fun f => f a) h.comparison_comp_relativeInverse)

include h in
theorem comparison_injective : Function.Injective (e.comparison d.baseMap) :=
  (h.relativeEquiv).toAlgEquiv.injective

end Inclusion

/-- A covering of a rational locus becomes a covering of the entire spectrum
of its actual quotient algebra. -/
theorem FamilyCovers.relative {I : Type u} {d : RationalData K P}
    {D : I → RationalData K P} (hc : FamilyCovers d D) :
    ∀ x : BanachSpectrum d.algebra, ∃ i, x ∈ ((D i).pullback d.baseMap).locus := by
  intro x
  exact hc (BanachSpectrum.comap d.baseMap.toBoundedRingHom x) (d.baseMap_hasImageIn x)

/-- The comparison on the explicitly constructed pairwise intersections. -/
def intersectionComparison (d e : RationalData K P) (φ : BoundedAlgHom K P Q) :
    BoundedAlgHom K (d.inter e).algebra ((d.pullback φ).inter (e.pullback φ)).algebra :=
  (pullbackInterIso d e φ).inv.restriction.comp ((d.inter e).comparison φ)

theorem intersectionComparison_comp_baseMap (d e : RationalData K P)
    (φ : BoundedAlgHom K P Q) :
    (intersectionComparison d e φ).comp (d.inter e).baseMap =
      ((d.pullback φ).inter (e.pullback φ)).baseMap.comp φ := by
  rw [intersectionComparison, BoundedAlgHom.comp_assoc, comparison_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap]

theorem intersectionComparison_comp_left (d e : RationalData K P)
    (φ : BoundedAlgHom K P Q) :
    (intersectionComparison d e φ).comp (interLeft d e).restriction =
      (interLeft (d.pullback φ) (e.pullback φ)).restriction.comp (d.comparison φ) := by
  apply d.hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    intersectionComparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    comparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

theorem intersectionComparison_comp_right (d e : RationalData K P)
    (φ : BoundedAlgHom K P Q) :
    (intersectionComparison d e φ).comp (interRight d e).restriction =
      (interRight (d.pullback φ) (e.pullback φ)).restriction.comp (e.comparison φ) := by
  apply e.hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    intersectionComparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    comparison_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    Inclusion.restriction_comp_baseMap]

/-- Compatible actual quotient elements stay compatible after base change. -/
theorem compatible_comparison {I : Type u} (D : I → RationalData K P)
    (φ : BoundedAlgHom K P Q) (s : ∀ i, (D i).algebra)
    (hs : ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
      (interRight (D i) (D j)).restriction (s j)) :
    ∀ i j, (interLeft ((D i).pullback φ) ((D j).pullback φ)).restriction
      ((D i).comparison φ (s i)) =
      (interRight ((D i).pullback φ) ((D j).pullback φ)).restriction
        ((D j).comparison φ (s j)) := by
  intro i j
  have hl := congrArg (fun f => f (s i)) (intersectionComparison_comp_left (D i) (D j) φ)
  have hr := congrArg (fun f => f (s j)) (intersectionComparison_comp_right (D i) (D j) φ)
  exact hl.symm.trans ((congrArg (intersectionComparison (D i) (D j) φ) (hs i j)).trans hr)

/-- An empty actual rational locus has a zero quotient algebra. This argument
uses spectrum nonemptiness for nonzero presented strict affinoids. -/
theorem subsingleton_algebra_of_locus_empty (d : RationalData K P)
    (hd : d.locus = ∅) : Subsingleton d.algebra := by
  by_contra h
  have : Nontrivial d.algebra := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨x⟩ := PresentedStrictAffinoidAlgebra.spectrum_nonempty d.algebra
  have hx := d.baseMap_hasImageIn x
  rw [hd] at hx
  exact hx

/-- Empty covering families force the target quotient to have one element. -/
theorem subsingleton_algebra_of_empty_cover {I : Type u} [IsEmpty I]
    {d : RationalData K P} {D : I → RationalData K P} (hc : FamilyCovers d D) :
    Subsingleton d.algebra := by
  apply subsingleton_algebra_of_locus_empty d
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, _⟩ := hc x hx
  exact isEmptyElim i

/-- The full unique section assertion for an empty covering family. -/
theorem existsUnique_gluing_empty {I : Type u} [IsEmpty I]
    (d : RationalData K P) (D : I → RationalData K P) (f : ∀ i, D i ⟶ d)
    (hc : FamilyCovers d D) (s : ∀ i, (D i).algebra) :
    ∃! a : d.algebra, ∀ i, (f i).restriction a = s i := by
  let := subsingleton_algebra_of_empty_cover hc
  exact ⟨0, fun i => isEmptyElim i, fun _ _ => Subsingleton.elim _ _⟩

end Langlands.Analytic.StrictTestDomain.RationalData
