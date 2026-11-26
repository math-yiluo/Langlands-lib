import Langlands.GroupScheme.Absolute.BorelUnipotentNormalizerStatement
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Absolute.MaximalUnipotentBorel
import Langlands.GroupScheme.Absolute.NoUnipotentSubgroupTorusProof
import Langlands.GroupScheme.Absolute.RationalNormalizer
import Langlands.GroupScheme.Absolute.SolvableQuotientExtension
import Langlands.GroupScheme.AlgClosedNormalQuotientExistenceProof
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.Reductive.UnipotentKernelQuotient
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.SubgroupPreimageQuotient
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Unipotent.MultiplicativeExtensionPartProof

/-! # The rational-point normalizer of the unipotent part of a Borel subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open SubgroupFunctor in
/-- A smooth connected affine group with a normal maximal smooth connected unipotent
subgroup is solvable: its quotient by that subgroup is a torus. -/
private theorem isSolvableGroupScheme_of_normal_maximalUnipotent
    {k : Type u} [Field k] [IsAlgClosed k] {P U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth P.X.hom] [IsAffineHom P.X.hom] [ConnectedSpace P.X.left]
    (v : U ⟶ P) (hv : IsMaximalUnipotentSubgroup v) (hn : (range v).IsNormal) :
    IsSolvableGroupScheme P := by
  have : Smooth U.X.hom := hv.smooth
  have : ConnectedSpace U.X.left := hv.connectedSpace
  have : IsAffineHom U.X.hom := hv.isClosedSubgroup.isAffineHom
  have : Mono v.hom.hom := hv.isClosedSubgroup.mono_overHom
  obtain ⟨R, r, hRa, _, hr⟩ := algClosedNormalQuotientExistence k P U v inferInstance
    inferInstance hv.isClosedSubgroup hn
  have : IsAffineHom R.X.hom := hRa
  have : Smooth R.X.hom := hr.smooth_target
  have : ConnectedSpace R.X.left := hr.2.1.surj.connectedSpace r.hom.hom.left.continuous
  have : Flat r.hom.hom.left := hr.1
  have : Surjective r.hom.hom.left := hr.2.1
  have : QuasiCompact r.hom.hom.left := HomImage.quasiCompact_hom r
  have : LocallyOfFinitePresentation r.hom.hom.left := hr.2.2.1
  have hker := HasSmoothConnectedUnipotentKernel.of_representative v hv.isClosedSubgroup
    hv.isUnipotent hr
  have : Smooth r.hom.hom.left := hker.smooth
  have : GeometricallyConnected (kernel r).X.hom := hker.geometricallyConnected
  have : IsAffineHom (kernel r).X.hom := KernelRepresentative.isAffineHom r v hr.2.2.2
  have hT : IsTorus R := by
    apply noUnipotentSubgroupTorus k R
    intro V a ha hs hc hu
    have : Smooth V.X.hom := hs
    have : ConnectedSpace V.X.left := hc
    let W := SubgroupPreimage.groupScheme r a
    let w : W ⟶ P := SubgroupPreimage.inclusion r a
    let v' : U ⟶ W := SubgroupPreimage.quotientKernelInclusion r a v hr
    have hv' : v' ≫ w = v := SubgroupPreimage.quotientKernelInclusion_comp r a v hr
    have : IsAffineHom W.X.hom := SubgroupPreimage.isAffineHom r a ha
    have : Flat (SubgroupPreimage.projection r a).hom.hom.left :=
      SubgroupPreimage.flat_projection r a
    have : Surjective (SubgroupPreimage.projection r a).hom.hom.left :=
      SubgroupPreimage.surjective_projection r a
    have : QuasiCompact (SubgroupPreimage.projection r a).hom.hom.left :=
      SubgroupPreimage.quasiCompact_projection r a
    have : IsAffineHom (kernel (SubgroupPreimage.projection r a)).X.hom :=
      SubgroupPreimage.isAffineHom_kernel r a
    have hWu : IsUnipotent W := isUnipotent_of_kernel_of_quotient
      (SubgroupPreimage.projection r a) (SubgroupPreimage.isUnipotent_kernel r a hker.2.2) hu
    have : IsIso v' := hv.maximal W w v' (SubgroupPreimage.isClosedSubgroup r a ha)
      (SubgroupPreimage.smooth r a)
      (SubgroupPreimage.connectedSpace_of_geometricallyConnected_kernel r a) hWu hv'
    apply SubgroupPreimage.range_eq_bot_of_range_inclusion_le_kernel r a
    rw [hr.2.2.2]
    exact range_le_of_factor (inv v') (by rw [← hv', IsIso.inv_hom_id_assoc])
  have : IsCommMonObj R.X := hT.isCommMonObj
  exact isSolvableGroupScheme_of_unipotent_fppfQuotient hv.isUnipotent hr
    (isSolvableGroupScheme_of_isCommMonObj R)

open SubgroupFunctor in
/-- The rational points normalizing the unipotent part of a Borel subgroup are precisely
its Borel points (Milne, Corollary 17.50, on rational points). -/
theorem borelUnipotentNormalizer : BorelUnipotentNormalizerStatement.{u} := by
  intro k _ _ G _ _ _ B U Q i u q hi hu hU hnu hq hQ
  have : IsAffineHom B.X.hom := hi.isClosedSubgroup.isAffineHom
  have : Smooth B.X.hom := hi.smooth
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ B.X.hom
  have hpart : IsUnipotentPart u := by
    obtain ⟨_, _, hs, hc⟩ := multiplicativeExtensionUnipotentPart k B U Q u q hu hU hnu hq hQ
    refine ⟨hu, hs hi.smooth, hc hi.connectedSpace, hU, ?_⟩
    intro V a ha hV
    have := MultiplicativeExtensionUnipotentPart.locallyOfFiniteType_of_isClosedSubgroup a ha
    have := ha.isAffineHom
    exact MultiplicativeExtensionUnipotentPart.range_le_of_isUnipotent a q hV hQ hq
  have hmax := hpart.isMaximalUnipotentSubgroup hi
  have : Smooth U.X.hom := hpart.smooth
  have : IsReduced U.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ U.X.hom
  have hui := hmax.isClosedSubgroup
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, n, hn, hnrep⟩ := (hasClosedRepresentative_normalizer_centralizer_range (u ≫ i) hui).1
  have hBN : range i ≤ range n := by
    rw [hnrep.2]
    intro T x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    exact normalizer_range_le_comap u i T (by
      rw [normalizer_eq_top_of_isNormal hnu]
      exact Subgroup.mem_top y)
  have : Mono i.hom.hom := hi.isClosedSubgroup.mono_overHom
  have : Mono n.hom.hom := hnrep.1
  have : LocallyOfFiniteType N.X.hom :=
    MultiplicativeExtensionUnipotentPart.locallyOfFiniteType_of_isClosedSubgroup n hn
  obtain ⟨b, hb⟩ := exists_factor_of_range_le hBN
  let P := reducedSubgroup N
  let j : P ⟶ G := reducedSubgroupι N ≫ n
  let f : B ⟶ P := ReducedSubgroup.liftHom b
  have hf : f ≫ j = i := by
    change ReducedSubgroup.liftHom b ≫ (reducedSubgroupι N ≫ n) = i
    rw [← Category.assoc, ReducedSubgroup.liftHom_fac, hb]
  have hred : IsClosedSubgroup (reducedSubgroupι N) :=
    inferInstanceAs (IsClosedImmersion (reducedSubgroupι N).hom.hom.left)
  have hj : IsClosedSubgroup j := hred.comp hn
  have : Mono j.hom.hom := hj.mono_overHom
  have : Smooth P.X.hom := ReducedSubgroup.smooth_reducedSubgroup N
  have : IsAffineHom P.X.hom := hj.isAffineHom
  have : ConnectedSpace P.X.left :=
    borelContainingSubgroupConnectedStatement k G P B j i f hj inferInstance hi hf
  let v : U ⟶ P := u ≫ f
  have hv : v ≫ j = u ≫ i := by
    change (u ≫ f) ≫ j = u ≫ i
    rw [Category.assoc, hf]
  have hvmax : IsMaximalUnipotentSubgroup v := by
    refine ⟨IsClosedSubgroup.of_comp hj (hv.symm ▸ hui), hpart.smooth,
      hpart.connectedSpace, hU, ?_⟩
    intro V a g ha hs hc hV hg
    exact hmax.maximal V (a ≫ j) g (ha.comp hj) hs hc hV (by
      rw [← Category.assoc, hg, hv])
  have hvn : (range v).IsNormal := by
    have hvcomap : range v = (range (u ≫ i)).comap j := by
      apply range_eq_comap_of_range_comp_eq_inf
      rw [hv]
      exact SubgroupFunctor.ext fun T =>
        (inf_eq_right.mpr (range_le_of_factor v hv T)).symm
    have hjle : range j ≤ (range (u ≫ i)).normalizer :=
      (range_le_of_factor (reducedSubgroupι N) (rfl : reducedSubgroupι N ≫ n = j)).trans hnrep.2.le
    intro T g x _ hx
    rw [hvcomap] at hx ⊢
    exact conj_mem_of_mem_normalizer (comap_normalizer_le j (range (u ≫ i)) T
      (hjle T (mem_range.mpr ⟨g, rfl⟩))) hx
  have hsolv := isSolvableGroupScheme_of_normal_maximalUnipotent v hvmax hvn
  have : IsIso f := hi.maximal P j f hj inferInstance inferInstance hsolv hf
  have hjle : range j ≤ range i := range_le_of_factor (inv f) (by
    rw [← hf, IsIso.inv_hom_id_assoc])
  have : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  rw [← normalizer_range_carrier_base_eq_algClosed_points hui, ← hnrep.2]
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    apply hjle _
    refine mem_range.mpr ⟨ReducedSubgroup.liftOver y, ?_⟩
    change _ ≫ (reducedSubgroupι N ≫ n).hom.hom = _
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact ReducedSubgroup.liftOver_fac_assoc y _
  · exact hBN _

end Langlands.GroupScheme
