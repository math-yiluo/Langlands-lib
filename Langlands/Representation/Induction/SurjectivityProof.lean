import Langlands.Representation.Induction.SurjectivityStatement
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Compact.SurjectivityProof
import Mathlib.GroupTheory.DoubleCoset

/-! Surjectivity of smooth induction, using compact fixed-vector lifting. -/

noncomputable section

namespace Langlands.Induction

universe uG uV uW

/-- The intersection of a closed subgroup with a conjugate of a compact open
subgroup is compact in the subgroup topology. -/
theorem isCompact_conjOpenSubgroup {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (P : Subgroup G) (hP : IsClosed (P : Set G))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact (conjOpenSubgroup P K x : Set P) := by
  have hc : IsCompact ((fun k : G => x * k * x⁻¹) '' (K : Set G)) :=
    hK.image ((continuous_const.mul continuous_id).mul_const _)
  have he : (conjOpenSubgroup P K x : Set P) =
      (Subtype.val : P → G) ⁻¹' ((fun k : G => x * k * x⁻¹) '' (K : Set G)) := by
    ext p
    change p ∈ conjOpenSubgroup P K x ↔ _
    rw [mem_conjOpenSubgroup]
    constructor
    · intro hp
      exact ⟨x⁻¹ * (p : G) * x, hp, by simp [mul_assoc]⟩
    · rintro ⟨k, hk, he⟩
      rw [← he]
      simpa [mul_assoc] using hk
  rw [he]
  exact hP.isClosedEmbedding_subtypeVal.isCompact_preimage hc

/-- Smooth induction from a closed subgroup preserves surjectivity under
cofinality of compact open subgroups, with independent group and vector universes. -/
theorem smoothInductionSurjectivity : SmoothInductionSurjectivityStatement.{uG,uV,uW} := by
  classical
  intro G _ _ _ _ hcofinal P hP V _ _ W _ _ sigma tau hsigma htau q hq f
  obtain ⟨U, hU⟩ := smoothInduced_smooth P tau f
  obtain ⟨K, hK, hKU⟩ := hcofinal U
  have hf : f ∈ fixedVectors (smoothInduced P tau) K.toSubgroup := by
    intro k
    exact hU ⟨k.val, hKU k.property⟩
  have hlift : ∀ x : G,
      ∃ v : fixedVectors sigma (conjOpenSubgroup P K x).toSubgroup,
        q v.val = eval P tau f x := by
    intro x
    obtain ⟨v, hv⟩ := Compact.fixedVectorSurjectivity P V W sigma tau hsigma htau
      (conjOpenSubgroup P K x) (isCompact_conjOpenSubgroup P hP K hK x) q hq
      ⟨eval P tau f x, eval_mem_fixedVectors P tau K x hf⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  choose v hv using hlift
  let sectionAt (d : DoubleCoset.Quotient (P : Set G) (K : Set G)) :
      SmoothFunctions P sigma :=
    (compactDoubleCosetSection P sigma K hK d.out (v d.out).val (v d.out).property).val
  let F : G → V := fun x => eval P sigma (sectionAt (DoubleCoset.mk P K.toSubgroup x)) x
  have hcov : ∀ (p : P) (x : G), F ((p : G) * x) = sigma p (F x) := by
    intro p x
    change eval P sigma (sectionAt (DoubleCoset.mk P K.toSubgroup ((p : G) * x)))
      ((p : G) * x) = sigma p (eval P sigma (sectionAt (DoubleCoset.mk P K.toSubgroup x)) x)
    rw [DoubleCoset.mk_mem_mul]
    exact eval_covariant P sigma _ p x
  have hright : ∀ (k : K) (x : G), F (x * (k : G)) = F x := by
    intro k x
    change eval P sigma (sectionAt (DoubleCoset.mk P K.toSubgroup (x * (k : G))))
      (x * (k : G)) = eval P sigma (sectionAt (DoubleCoset.mk P K.toSubgroup x)) x
    rw [DoubleCoset.mk_mul_mem]
    exact compactDoubleCosetSection_mul P sigma K hK _ _ _ k x
  refine ⟨smoothFunctionOf P sigma F hcov K hright, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change q (F x) = eval P tau f x
  let d := DoubleCoset.mk P K.toSubgroup x
  obtain ⟨p, hp, k, hk, hx⟩ := DoubleCoset.eq.mp (DoubleCoset.out_eq' d)
  have hsection : F x = sigma ⟨p, hp⟩ (v d.out).val := by
    change eval P sigma (sectionAt d) x = _
    rw [hx]
    exact compactDoubleCosetSection_apply P sigma K hK d.out
      (v d.out).val (v d.out).property ⟨p, hp⟩ ⟨k, hk⟩
  rw [hsection, q.isIntertwining sigma tau, hv]
  rw [hx, eval_mul_of_mem_fixedVectors P tau K.toSubgroup hf ⟨k, hk⟩]
  exact (eval_covariant P tau f ⟨p, hp⟩ d.out).symm

end Langlands.Induction
