import Langlands.Representation.Induction.CompactSurjectivityStatement
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Induction.CompactQuotientCutoff

/-! Surjectivity of compact induction by cutting off a smooth lift. -/

noncomputable section

namespace Langlands.Induction

universe uR uG uV uW

/-- The actual projected nonzero support of a smooth induced function is open. -/
theorem isOpen_quotientSupport {R : Type uR} {G : Type uG} {V : Type uV}
    [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module R V] (H : Subgroup G) (sigma : Representation R H V)
    (f : SmoothFunctions H sigma) :
    IsOpen (quotientSupport H (eval H sigma f)) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isOpen_preimage.mp
  change IsOpen (quotientMap H ⁻¹' quotientSupport H (eval H sigma f))
  rw [quotientMap_preimage_quotientSupport]
  exact (eval_isLocallyConstant H sigma f).isClosed_fiber 0 |>.isOpen_compl

/-- Compact induction from a closed subgroup preserves surjectivity under
cofinality of compact open subgroups, with independent group and vector universes. -/
theorem compactInductionSurjectivity :
    CompactInductionSurjectivityStatement.{uG,uV,uW} := by
  classical
  intro G _ _ _ _ hcofinal H hH V _ _ W _ _ sigma tau hsigma htau T hT f
  obtain ⟨F, hF⟩ :=
    smoothInductionSurjectivity G hcofinal H hH V W sigma tau hsigma htau T hT f.val
  let C := quotientSupport H (eval H tau f.val)
  have hc : IsCompact C := f.property
  have ho : IsOpen C := isOpen_quotientSupport H tau f.val
  let F' := smoothQuotientCutoff H sigma C hc ho F
  have hcompact : IsCompact (quotientSupport H (eval H sigma F')) := by
    apply hc.of_isClosed_subset (isClosed_quotientSupport H sigma F')
    rw [quotientSupport_smoothQuotientCutoff]
    exact Set.inter_subset_left
  refine ⟨⟨F', hcompact⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change T (eval H sigma (smoothQuotientCutoff H sigma C hc ho F) x) =
    eval H tau f.val x
  rw [eval_smoothQuotientCutoff]
  by_cases hx : quotientMap H x ∈ C
  · rw [ite_eq_left hx]
    exact congrArg (fun s : SmoothFunctions H tau => eval H tau s x) hF
  · rw [ite_eq_right hx, map_zero]
    have hz : eval H tau f.val x = 0 := by
      by_contra hne
      exact hx ⟨x, hne, rfl⟩
    exact hz.symm

end Langlands.Induction
