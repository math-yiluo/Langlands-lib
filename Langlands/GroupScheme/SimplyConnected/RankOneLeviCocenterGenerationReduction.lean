import Langlands.GroupScheme.SimplyConnected.LeviCocenterKernelGenerationStatement
import Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterStructure
import Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterKernel
import Langlands.GroupScheme.FieldSeparatedProof

/-!
# Reduction of cocenter generation to kernel generation

This module proves `RankOneLeviCocenterGenerationStatement` from
`LeviCocenterKernelGenerationStatement`: the rational kernel of the map from the cocenter of the
minimal Levi subgroup to the cocenter of the standard Levi subgroup of a simple relative root `α`
lies in the image of the rational points of the cocenter of `M ∩ A_α`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Kernel generation of the cocenter implies cocenter generation by rank-one Levi factors. -/
theorem rankOneLeviCocenterGeneration_of_leviCocenterKernelGeneration
    (hker : LeviCocenterKernelGenerationStatement.{u}) :
    RankOneLeviCocenterGenerationStatement.{u} := by
  intro k _ G _ hsc S i hi ν hν M j hj A a ha D d hd Q q hq Dα dα hdα Qα qα hqα φ hsq
  have hGred := hsc.isSemisimple.isConnectedReductive
  have : Smooth G.X.hom := hGred.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- `M` is a closed connected reductive subgroup
  have hjc : IsClosedSubgroup j := by
    have hrep' := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ν ≫ i)
    rw [← hj.isoOfIsRepresentedBy_hom_comp hrep']
    exact IsClosedSubgroup.iso_comp _ (Dynamic.Affine.isClosedSubgroup_centralizerHom _)
  have hMred : IsConnectedReductive M := dynamicCentralizerReductive k G hGred _ M j hjc hj
  have : IsAffineHom M.X.hom := hMred.isAffineHom
  have : Mono j.hom.hom := hj.1
  have hDperf : derivedSubgroup D = ⊤ :=
    semisimplePerfect k D (derivedSubgroupSemisimple k M D d hMred hd)
  -- the quotient `q` is an fpqc cover
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : QuasiCompact q.hom.hom.left := by
    have : IsSeparated Q.X.hom := fieldSeparated k Q
    have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  -- the standard Levi subgroups, their derived groups and the retractions
  choose ζ L l jL E e aE pA δ hζ hl hlc hLred hjL he haE hpA hK hδ using
    fun α : simpleRelativeRoots i ν =>
      rankOneLeviFactor_derivedRetraction k G hsc S i hi ν hν M j hj α.1 α.2 (A α) (a α) (ha α)
        D d hd
  -- the cocenters of the standard Levi subgroups
  choose R r hRaff hr _ _ using fun α : simpleRelativeRoots i ν =>
    cocenterQuotientExistence k (L α) (E α) (e α) (hLred α) (he α)
  have hkernelL : ∀ α, SubgroupFunctor.range (kernelι q) ≤
      (SubgroupFunctor.range (kernelι (r α))).comap (jL α) := fun α =>
    range_kernelι_le_comap_of_derived (jL α) (he α) hd (hr α) hq
  let π : ∀ α, Q ⟶ (R α).toGrp := fun α =>
    SubgroupFunctor.quotientSubgroupHom (jL α) (r α) q (hkernelL α)
  have hπ : ∀ α, q ≫ π α = jL α ≫ r α := fun α =>
    (SubgroupFunctor.quotientSubgroupHom_square (jL α) (r α) q (hkernelL α)).symm
  have hgen := hker k G hsc S i hi ν hν M j hj D d hd Q q hq ζ hζ L l hl jL hjL E e he
    (fun α => (R α).toGrp) r hr π hπ
  refine hgen.trans (Subgroup.closure_mono (Set.iUnion_mono fun α => ?_))
  intro x hx
  have hx1 : x ≫ (π α).hom.hom = 1 := hx
  -- the instances for the intersection `M ∩ A_α`
  have : Mono (a α).hom.hom := (ha α).1.mono_hom
  have : Mono (e α ≫ l α).hom.hom := ((he α).1.comp (hlc α)).mono_hom
  have : IsClosedImmersion (subgroupIntersectionFst j (a α)).hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst j (ha α).1
  have : IsAffineHom (subgroupIntersection j (a α)).X.hom := by
    rw [← Over.w (subgroupIntersectionFst j (a α)).hom.hom]
    infer_instance
  have : QuasiCompact (qα α).hom.hom.left := by
    have : IsSeparated (Qα α).X.hom := fieldSeparated k (Qα α)
    have : QuasiCompact ((qα α).hom.hom.left ≫ (Qα α).X.hom) := by
      rw [Over.w (qα α).hom.hom]
      infer_instance
    exact QuasiCompact.of_comp (qα α).hom.hom.left (Qα α).X.hom
  have : Mono (φ α).hom.hom :=
    mono_of_cocenter_square (haE α) (hpA α) (hK α) (hδ α) hDperf hd hq (hdα α) (hqα α) (φ α)
      (hsq α)
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1
    (mem_range_of_comp_eq_one (haE α) (hpA α) (hK α) hq (qα α) (φ α) (hsq α) (jL α) (hjL α)
      (hr α).2.2.2 (π α) (hπ α) x hx1)
  exact ⟨y, hy⟩

end Langlands.GroupScheme
