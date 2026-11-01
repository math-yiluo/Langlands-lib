import Langlands.Representation.Aubert.CorrectedOrbitCoefficientJacquet
import Langlands.Representation.Aubert.CorrectedGradedCutComparison
import Langlands.Representation.Geometric.RefinementSolomonCoefficients

/-! Vanishing of the actual corrected graded pieces outside whole targets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport

universe uF

variable (F : Type uF) [CommRing F] [Nontrivial F] {n : ℕ}
  (B C : BlockShape n) (w : Equiv.Perm (Fin n)) (S : BlockRefinement B)

/-- A proper target intersection forces the actual flattened source
intersection to have strictly more blocks than the target. -/
theorem flattened_length_gt_of_not_wholeTarget
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hW : blockWeyl C ⊓ (blockWeyl B).comap
      (MulAut.conj w⁻¹).toMonoidHom ≠ blockWeyl C) :
    C.length < (B.flatten S).length := by
  let Q := B.flatten S
  have hrel := (TypeASolomon.intersection_eq_iff B C Q w).mp
    (blockWeyl_flatten_eq_intersection F B C w S hS).symm
  have hlabel (x : Fin n) :
      blockIndex C (w x) = blockMap Q C w (blockIndex Q x) :=
    ((hrel x (Q.index (blockIndex Q x) ⟨0, Q.positive _⟩)).mp
      (blockIndex_index Q (blockIndex Q x) ⟨0, Q.positive _⟩).symm).2
  have hsurj : Function.Surjective (blockMap Q C w) := by
    intro j
    refine ⟨blockIndex Q (w.symm (C.index j ⟨0, C.positive j⟩)), ?_⟩
    rw [← hlabel, Equiv.apply_symm_apply, blockIndex_index]
  have hnotinj : ¬ Function.Injective (blockMap Q C w) := by
    intro hinj
    apply hW
    apply (TypeASolomon.intersection_eq_iff C B C w⁻¹).mpr
    intro a b
    constructor
    · intro hab
      refine ⟨hab, ?_⟩
      have hf : blockMap Q C w (blockIndex Q (w.symm a)) =
          blockMap Q C w (blockIndex Q (w.symm b)) := by
        rw [← hlabel, ← hlabel, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hab
      exact ((hrel (w.symm a) (w.symm b)).mp (hinj hf)).1
    · exact And.left
  simpa only [Fintype.card_fin] using
    Fintype.card_lt_of_surjective_not_injective (blockMap Q C w) hsurj hnotinj

end Langlands.Geometric

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

section Inactive

variable
  (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))

/-- An inactive singleton removal has equal actual support images and zero
actual successive quotient. -/
theorem cutSupportQuotient_subsingleton_of_not_active
    (hw : w ∉ weylSupport B C θ) :
    letI := T.topology
    Subsingleton (cutSupportQuotient T A C B (θ \ {w}) θ) := by
  let := T.topology
  have hcore : weylSupport B C θ = weylSupport B C (θ \ {w}) := by
    by_contra hne
    exact hw ((twoSidedCore_diff_singleton_ne_iff
      (blockWeyl C) (blockWeyl B) θ w).mp hne)
  have heq := correctedJacquetSupport_eq_of_core_eq T B C hcore
  have hz (z : cutSupportQuotient T A C B (θ \ {w}) θ) : z = 0 := by
    obtain ⟨q, rfl⟩ := (correctedJacquetSupport T B C (θ \ {w})).quotientProjection_surjective
      (correctedJacquetSupport T B C θ) ((T.normalizedJacquetFunctor B).obj A) z
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change q.val ∈ (correctedJacquetSupport T B C (θ \ {w})).obj
      ((T.normalizedJacquetFunctor B).obj A)
    rw [← heq]
    exact q.property
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- A length-ordered singleton step can be active only at the actual minimal
representative of its double coset. -/
theorem cutSupportQuotient_subsingleton_of_not_minimal
    (hTail : ∀ v ∈ θ \ {w}, inversionLength w ≤ inversionLength v)
    (hw : ¬ IsMinimalRepresentative B C w) :
    letI := T.topology
    Subsingleton (cutSupportQuotient T A C B (θ \ {w}) θ) := by
  apply cutSupportQuotient_subsingleton_of_not_active T A B C θ w
  intro hactive
  exact hw (singleton_drop_isMinimalRepresentative B C θ w hTail
    ((twoSidedCore_diff_singleton_ne_iff
      (blockWeyl C) (blockWeyl B) θ w).mpr hactive))

end Inactive

section BlockBound

variable
  (A : letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (hbound : letI := T.topology
    CuspidalSupport.HasJacquetBlockBound F T C A)
  (hwInc : TypeASolomon.SourceIncreasing B w)
  (hW : blockWeyl C ⊓ (blockWeyl B).comap
    (MulAut.conj w⁻¹).toMonoidHom ≠ blockWeyl C)

include hbound hwInc hW

/-- The actual nested orbit coefficient vanishes outside whole target
intersections under the target Jacquet block bound. -/
theorem cutOrbitCoefficient_subsingleton_of_not_wholeTarget :
    letI := T.topology
    Subsingleton (Representation.Coinvariants
      (cutOrbitNestedCoefficient T A.representation C w B)) := by
  let := T.topology
  obtain ⟨S, hS⟩ := exists_standardIntersections F.Carrier B C w hwInc
  have hgt := flattened_length_gt_of_not_wholeTarget F.Carrier B C w S hS.2.1 hW
  exact cutOrbitCoefficient_subsingleton_of_flattened T A B C w S hS (hbound _ hgt)

/-- The genuine graded quotient vanishes by its actual orbit isomorphism
when the target intersection is proper. -/
theorem cutSupportQuotient_subsingleton_of_not_wholeTarget
    (θ : Set (Equiv.Perm (Fin n)))
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
    (hw : w ∈ weylSupport B C θ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    Subsingleton (cutSupportQuotient T A C B (θ \ {w}) θ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := cutOrbitCoefficient_subsingleton_of_not_wholeTarget T A B C w hbound hwInc hW
  exact (Representation.equivOfIso
    (coherentGradedOrbitIntegralIso T A B C θ w hθ hLower hw hwInc)).injective.subsingleton

/-- A canonical zero-module identification for a proper-target graded piece. -/
def cutSupportQuotientZeroEquiv_of_not_wholeTarget
    (θ : Set (Equiv.Perm (Fin n)))
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
    (hw : w ∈ weylSupport B C θ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    cutSupportQuotient T A C B (θ \ {w}) θ ≃ₗ[ℂ] (Fin 0 → ℂ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := cutSupportQuotient_subsingleton_of_not_wholeTarget
    T A B C w hbound hwInc hW θ hθ hLower hw
  exact LinearEquiv.ofSubsingleton _ _

end BlockBound
end Langlands.Aubert.Support
