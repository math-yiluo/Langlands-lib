import Langlands.Geometry.Analytic.CompactSmallFibreProduct
import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationProof
import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof

/-! # Clopen comparison of analytic kernel pairs -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P H W R S : LocalizedCategory.{u, v, v} (K := K)}
  {q : P ⟶ H} {f : H ⟶ W}
  {r₁ r₂ : R ⟶ P} {s₁ s₂ : S ⟶ P}

/-- A map of targets induces the canonical morphism from the kernel pair of
`q` to the kernel pair of `q ≫ f`. -/
def kernelPairComparison (hR : IsPullback r₁ r₂ q q)
    (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f)) : R ⟶ S :=
  hS.lift r₁ r₂ (by rw [← Category.assoc, ← Category.assoc, hR.w])

@[reassoc (attr := simp)]
theorem kernelPairComparison_fst (hR : IsPullback r₁ r₂ q q)
    (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f)) :
    kernelPairComparison hR hS ≫ s₁ = r₁ :=
  hS.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem kernelPairComparison_snd (hR : IsPullback r₁ r₂ q q)
    (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f)) :
    kernelPairComparison hR hS ≫ s₂ = r₂ :=
  hS.lift_snd _ _ _

theorem mono_kernelPairComparison (hR : IsPullback r₁ r₂ q q)
    (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f)) :
    Mono (kernelPairComparison hR hS) := by
  constructor
  intro T a b hab
  apply hR.hom_ext
  · simpa only [Category.assoc, kernelPairComparison_fst] using congrArg (· ≫ s₁) hab
  · simpa only [Category.assoc, kernelPairComparison_snd] using congrArg (· ≫ s₂) hab

/-- The kernel-pair comparison is étale if `q` and its composite are étale. -/
theorem etale_kernelPairComparison (hR : IsPullback r₁ r₂ q q)
    (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f))
    (hq : etale q) (hc : etale (q ≫ f)) :
    etale (kernelPairComparison hR hS) := by
  obtain ⟨_, _, _, hR', heR⟩ := localizedEtalePullbackBaseChange q q hq
  obtain ⟨_, _, _, hS', heS⟩ := localizedEtalePullbackBaseChange (q ≫ f) (q ≫ f) hc
  have hr₂ := etale_snd_of_isPullback hR' hR heR
  have hs₂ := etale_snd_of_isPullback hS' hS heS
  have hcancel := etaleRightCancellation_of_finiteOver
    (AffinoidAtlasPresentation.StrongHom.finiteOverRightCancellation K)
  exact hcancel.of_postcomp _ _ hs₂ ((kernelPairComparison_snd hR hS).symm ▸ hr₂)

/-- An étale monomorphism is injective on underlying points. -/
theorem injective_of_etale_of_mono (g : R ⟶ S) [Mono g] (hg : etale g) :
    Function.Injective (localizedSpaceFunctor.map g) := by
  intro x y hxy
  obtain ⟨z, hx, hy⟩ :=
    exists_point_of_isPullback_of_etale (IsKernelPair.id_of_mono g) hg x y hxy
  exact hx.symm.trans hy

/-- The comparison is an open embedding on underlying spaces. -/
theorem isOpenEmbedding_kernelPairComparison
    (hR : IsPullback r₁ r₂ q q) (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f))
    (hq : etale q) (hc : etale (q ≫ f)) :
    IsOpenEmbedding (localizedSpaceFunctor.map (kernelPairComparison hR hS)) := by
  let j := kernelPairComparison hR hS
  let : Mono j := mono_kernelPairComparison hR hS
  have hj := etale_kernelPairComparison hR hS hq hc
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap (localizedSpaceFunctor.map j).hom.continuous
    (injective_of_etale_of_mono j hj) (etaleOpenMap K j hj)

/-- For compact Hausdorff `P` and Hausdorff `H` and `S`, the comparison
has clopen image in the underlying space of the composite's kernel pair. -/
theorem isClopen_range_kernelPairComparison
    (hR : IsPullback r₁ r₂ q q) (hS : IsPullback s₁ s₂ (q ≫ f) (q ≫ f))
    (hq : etale q) (hc : etale (q ≫ f)) (hP : IsCompactSpace P)
    (hH : T2Space (localizedSpaceFunctor.obj H)) (hS₂ : T2Space (localizedSpaceFunctor.obj S)) :
    IsClopen (Set.range (localizedSpaceFunctor.map (kernelPairComparison hR hS))) := by
  let c := compactLocalizedEtalePullback q q hq hP hP hH
  let : CompactSpace (localizedSpaceFunctor.obj R) :=
    (c.compact.of_iso ((IsPullback.of_isLimit c.isLimit).isoIsPullback _ _ hR)).1
  let : T2Space (localizedSpaceFunctor.obj S) := hS₂
  exact ⟨(isCompact_range (localizedSpaceFunctor.map
    (kernelPairComparison hR hS)).hom.continuous).isClosed,
    (isOpenEmbedding_kernelPairComparison hR hS hq hc).isOpen_range⟩

end Langlands.Analytic.SaturatedAtlasPresentation
