import Langlands.Representation.Jacquet.FixedVectorGeneratedCategory
import Langlands.Representation.Category.UniverseLiftFunctor
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # Fixed-vector generation and actual subquotients under carrier lifts -/

noncomputable section

open CategoryTheory

universe uX uG uV uW

namespace Langlands.Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (K : Subgroup G)

/-- Generation by fixed vectors is invariant under an actual representation
equivalence, including one between different carrier universes. -/
theorem fixedVectorGenerated_iff_of_equiv
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}
    (e : A.representation.Equiv B.representation) :
    fixedVectorGenerated K A ↔ fixedVectorGenerated K B :=
  ⟨fun h => fixedVectorGenerated_of_surjective K h e.toIntertwiningMap e.surjective,
    fun h => fixedVectorGenerated_of_surjective K h e.symm.toIntertwiningMap
      e.symm.surjective⟩

/-- The carrier lift preserves and reflects the exact fixed-vector generation
criterion, without any relation between the group and carrier universes. -/
theorem fixedVectorGenerated_universeLift_iff
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    fixedVectorGenerated K (SmoothRep.universeLift.{uX} A) ↔
      fixedVectorGenerated K A :=
  (fixedVectorGenerated_iff_of_equiv K (SmoothRep.universeLiftEquiv A)).symm

/-- The actual fixed-vector spaces before and after a carrier lift are linearly
equivalent by `up` and `down`. -/
def fixedVectorsUniverseLiftEquiv (A : SmoothRep.{0, uG, uV} ℂ G) :
    fixedVectors A.representation K ≃ₗ[ℂ]
      fixedVectors (SmoothRep.universeLift.{uX} A).representation K :=
  fixedVectorsEquiv (SmoothRep.universeLiftEquiv A) K

@[simp]
theorem fixedVectorsUniverseLiftEquiv_apply
    (A : SmoothRep.{0, uG, uV} ℂ G) (v : fixedVectors A.representation K) :
    (fixedVectorsUniverseLiftEquiv.{uX} K A v : SmoothRep.universeLift.{uX} A) =
      ULift.up (v : A) := rfl

@[simp]
theorem fixedVectorsUniverseLiftEquiv_symm_apply
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (v : fixedVectors (SmoothRep.universeLift.{uX} A).representation K) :
    ((fixedVectorsUniverseLiftEquiv.{uX} K A).symm v : A) = (v.val).down := rfl

/-- A nonzero fixed vector of the lift descends to its actual original carrier,
and every original nonzero fixed vector lifts. -/
theorem exists_nonzero_fixed_universeLift_iff
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    (∃ v : SmoothRep.universeLift.{uX} A,
      v ∈ fixedVectors (SmoothRep.universeLift.{uX} A).representation K ∧ v ≠ 0) ↔
    ∃ v : A, v ∈ fixedVectors A.representation K ∧ v ≠ 0 := by
  let e := SmoothRep.universeLiftEquiv.{uX} A
  constructor
  · rintro ⟨v, hv, hv0⟩
    refine ⟨e.symm v, map_mem_fixedVectors e.symm.toIntertwiningMap hv, ?_⟩
    intro h
    apply hv0
    exact e.symm.injective (h.trans (map_zero e.symm).symm)
  · rintro ⟨v, hv, hv0⟩
    refine ⟨e v, map_mem_fixedVectors e.toIntertwiningMap hv, ?_⟩
    intro h
    apply hv0
    exact e.injective (h.trans (map_zero e).symm)

end Langlands.Jacquet

namespace Langlands.SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Lift the witness and both maps of an actual smooth subquotient presentation.
Injectivity and surjectivity are preserved pointwise by `up` and `down`. -/
theorem IsSubquotient.universeLift
    {A B : SmoothRep.{0, uG, uV} ℂ G} (h : IsSubquotient B A) :
    IsSubquotient (SmoothRep.universeLift.{uX} B) (SmoothRep.universeLift.{uX} A) := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  let F := universeLiftFunctor.{uX, uG, uV} G
  refine isSubquotient_iff_exists.mpr ⟨F.obj C, F.map i, F.map q, ?_, ?_⟩
  · intro x y hxy
    apply ULift.ext
    exact hi (congrArg ULift.down hxy)
  · intro y
    obtain ⟨x, hx⟩ := hq y.down
    refine ⟨ULift.up x, ?_⟩
    apply ULift.ext
    exact hx

end Langlands.SmoothRep
