import Langlands.GroupScheme.AffineQuotientProof
import Langlands.GroupScheme.KernelCoreQuotientDimension
import Langlands.GroupScheme.Rational.SmoothClosedSubgroupInduction
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Unipotent.AdditiveQuotient
import Langlands.GroupScheme.Unipotent.OneDimensionalStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement

/-! # A finite unipotent series from one-dimensional classification -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Unipotent

/-- Closed-subgroup unipotence and one-dimensional classification imply
represented split unipotence over every perfect field. -/
theorem perfectFieldSplit_of_oneDimensional
    (hclosed : UnipotentClosedSubgroupStatement.{u})
    (hone : PerfectFieldOneDimensionalUnipotentStatement.{u})
    (k : Type u) [Field k] [PerfectField k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U) :
    RelativeRoot.IsSplitUnipotent U := by
  classical
  refine smoothAffineGroup_closedSubgroup_induction
    (fun H => ConnectedSpace H.X.left → IsUnipotent H →
      RelativeRoot.IsSplitUnipotent H) ?_ U hUc hUu
  intro H _ _ ih hHc hHu
  let := hHc
  by_cases ht : SubgroupFunctor.range (𝟙 H) = ⊥
  · exact ⟨0, ht⟩
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
    change IsAffineHom (Spec.map
      (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
    infer_instance
  obtain ⟨f, hf, -⟩ := exists_additive_fppf_quotient hHu ht
  let : LocallyOfFiniteType (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  let : IsAffineHom (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have hj : IsClosedSubgroup (KernelCoreQuotient.inclusion f) :=
    inferInstanceAs (IsClosedImmersion (KernelCoreQuotient.inclusion f).hom.hom.left)
  have hKu : IsUnipotent (KernelCoreQuotient.core f) :=
    hclosed k H _ (KernelCoreQuotient.inclusion f) hj hHu
  obtain ⟨n, hn⟩ := ih (KernelCoreQuotient.core f) (KernelCoreQuotient.inclusion f)
    hj (KernelCoreQuotient.inclusion_not_isIso f hf) inferInstance hKu
  let : IsAffineHom (KernelCoreQuotient.groupScheme f).X.hom :=
    affineGroupSchemeQuotient k H _ (KernelCoreQuotient.projection f)
  let : SmoothOfRelativeDimension 1 (KernelCoreQuotient.groupScheme f).X.hom :=
    KernelCoreQuotient.smoothOfRelativeDimension_one f hf
      (VectorGroup.smoothOfRelativeDimension (CommRingCat.of k) 1)
  have hQv : RelativeRoot.IsVectorGroupOfDimension (KernelCoreQuotient.groupScheme f) 1 :=
    hone k _ inferInstance (KernelCoreQuotient.isUnipotent f hHu)
  exact ⟨n + 1, KernelCoreQuotient.core f, KernelCoreQuotient.groupScheme f,
    KernelCoreQuotient.inclusion f, KernelCoreQuotient.projection f, hj,
    inferInstance, inferInstance, KernelCoreQuotient.isNormal f,
    KernelCoreQuotient.isFppfQuotient f, hQv, hn⟩

/-- A chosen finite series length with its full represented-series witness,
conditional on the closed-subgroup and classification inputs. -/
def perfectFieldSplitSeries
    (hclosed : UnipotentClosedSubgroupStatement.{u})
    (hone : PerfectFieldOneDimensionalUnipotentStatement.{u})
    (k : Type u) [Field k] [PerfectField k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U) :
    {n : ℕ // RelativeRoot.HasSplitSeries n U} :=
  ⟨Classical.choose (perfectFieldSplit_of_oneDimensional hclosed hone k U hUc hUu),
    Classical.choose_spec
      (perfectFieldSplit_of_oneDimensional hclosed hone k U hUc hUu)⟩

end Langlands.GroupScheme.Unipotent
