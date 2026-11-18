import Langlands.Representation.Induction.SplitQuotientProjection
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Plancherel.StandardIntertwiningIntegral

/-! # The standard intertwining quotient in an intermediate Levi -/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Induction

namespace Langlands.Plancherel.StandardIntertwining

universe u

variable {G : Type u} [Group G]
  {Q L N U U' : Subgroup G} (hQ : IsSemidirectDecomposition Q L N)
  (hU'Q : U' ≤ Q) (hNU : N ≤ U) (hNU' : N ≤ U')

/-- The outer Levi projection restricted to the target radical. -/
def nestedTargetRadicalProjection : U' →* U'.subgroupOf L :=
  (hQ.projection.comp (Subgroup.inclusion hU'Q)).codRestrict _
    (hQ.projection_mem_of_radical_le hU'Q hNU')

/-- The inclusion of the target radical inside the intermediate Levi. -/
def nestedTargetRadicalSection : U'.subgroupOf L →* U' where
  toFun x := ⟨(x.val : G), x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem nestedTargetRadicalProjection_section (x : U'.subgroupOf L) :
    nestedTargetRadicalProjection hQ hU'Q hNU' (nestedTargetRadicalSection x) = x :=
  Subtype.ext (hQ.projection_levi x.val)

include hNU in
/-- The radical of the outer parabolic lies in both radicals. Thus the
kernel of the restricted projection is killed by the ambient quotient. -/
theorem nestedTargetRadicalProjection_ker_le :
    (nestedTargetRadicalProjection hQ hU'Q hNU').ker ≤ U.subgroupOf U' := by
  intro x hx
  exact hNU ((hQ.projection_eq_one_iff ⟨x, hU'Q x.property⟩).mp
    (congrArg Subtype.val (show nestedTargetRadicalProjection hQ hU'Q hNU' x = 1 from hx)))

variable [TopologicalSpace G] (hπ : Continuous hQ.projection)

/-- The actual left quotient for two radicals inside an outer parabolic
identifies with the corresponding left quotient inside its Levi. -/
def nestedRadicalQuotientHomeomorph :
    QuotientSpace (U := U) U' ≃ₜ
      QuotientSpace (U := U.subgroupOf L) (U'.subgroupOf L) := by
  have hinc : Continuous (Subgroup.inclusion hU'Q) :=
    (continuous_subtype_val : Continuous fun x : U' => (x : G)).subtype_mk _
  exact splitQuotientProjectionHomeomorph (nestedTargetRadicalProjection hQ hU'Q hNU')
    nestedTargetRadicalSection (nestedTargetRadicalProjection_section hQ hU'Q hNU')
    (U.subgroupOf U') (nestedTargetRadicalProjection_ker_le hQ hU'Q hNU hNU')
    ((hπ.comp hinc).subtype_mk _)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

@[simp]
theorem nestedRadicalQuotientHomeomorph_mk (x : U') :
    nestedRadicalQuotientHomeomorph hQ hU'Q hNU hNU' hπ (Quotient.mk _ x) =
      Quotient.mk _ (nestedTargetRadicalProjection hQ hU'Q hNU' x) := rfl

@[simp]
theorem nestedRadicalQuotientHomeomorph_symm_mk (x : U'.subgroupOf L) :
    (nestedRadicalQuotientHomeomorph hQ hU'Q hNU hNU' hπ).symm (Quotient.mk _ x) =
      Quotient.mk _ (nestedTargetRadicalSection x) := rfl

variable [IsTopologicalGroup G]
  [MeasurableSpace (QuotientSpace (U := U) U')] [BorelSpace (QuotientSpace (U := U) U')]
  [MeasurableSpace (QuotientSpace (U := U.subgroupOf L) (U'.subgroupOf L))]
  [BorelSpace (QuotientSpace (U := U.subgroupOf L) (U'.subgroupOf L))]

/-- Pushing the ambient measure along the quotient comparison preserves
right invariance for the inner target radical. -/
theorem nestedRadicalQuotientHomeomorph_map_right_invariant
    (ν : Measure (QuotientSpace (U := U) U'))
    (hν : ∀ x : U', MeasurePreserving (QuotientIntegration.rightTranslate (U.subgroupOf U') x) ν ν)
    (x : U'.subgroupOf L) :
    let e := nestedRadicalQuotientHomeomorph hQ hU'Q hNU hNU' hπ
    MeasurePreserving (QuotientIntegration.rightTranslate
      ((U.subgroupOf L).subgroupOf (U'.subgroupOf L)) x) (ν.map e) (ν.map e) := by
  let e := nestedRadicalQuotientHomeomorph hQ hU'Q hNU hNU' hπ
  let R := QuotientIntegration.rightTranslate (U.subgroupOf U') (nestedTargetRadicalSection x)
  let R' := QuotientIntegration.rightTranslate ((U.subgroupOf L).subgroupOf (U'.subgroupOf L)) x
  have hcomm : R' ∘ e = e ∘ R := by
    funext q
    change R' (e q) = e (R q)
    induction q using Quotient.inductionOn with
    | h y =>
      simp only [R, R', e, QuotientIntegration.rightTranslate_mk,
        nestedRadicalQuotientHomeomorph_mk, map_mul, nestedTargetRadicalProjection_section]
  change MeasurePreserving R' (ν.map e) (ν.map e)
  refine ⟨R'.continuous.measurable, ?_⟩
  rw [Measure.map_map R'.continuous.measurable e.continuous.measurable, hcomm,
    ← Measure.map_map e.continuous.measurable R.continuous.measurable]
  rw [(hν (nestedTargetRadicalSection x)).map_eq]

end Langlands.Plancherel.StandardIntertwining
