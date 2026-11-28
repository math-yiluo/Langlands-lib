import Langlands.GroupScheme.Dynamic.ParabolicIntersection
import Langlands.GroupScheme.Dynamic.WeightExclusion
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.SubgroupIntersection

/-! # The intersection of three dynamic parabolics with zero sum -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- In a modular, compactly generated lattice, the meet of the suprema of an independent
family over two index sets lies below the supremum over their intersection. -/
theorem biSup_inf_biSup_le_of_iSupIndep {I α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {f : I → α} (hf : iSupIndep f) (s t : Set I) :
    (⨆ i ∈ s, f i) ⊓ (⨆ i ∈ t, f i) ≤ ⨆ i ∈ s ∩ t, f i := by
  have hs : (⨆ i ∈ s, f i) = (⨆ i ∈ s ∩ t, f i) ⊔ ⨆ i ∈ s \ t, f i := by
    rw [← iSup_union, Set.inter_union_sdiff]
  have hle : (⨆ i ∈ s ∩ t, f i) ≤ ⨆ i ∈ t, f i :=
    biSup_mono fun i hi => hi.2
  have hdisj : Disjoint (⨆ i ∈ s \ t, f i) (⨆ i ∈ t, f i) :=
    hf.disjoint_biSup_biSup (Set.disjoint_sdiff_left)
  rw [hs, sup_inf_assoc_of_le _ hle, hdisj.eq_bot, sup_bot_eq]

section Represented

variable {S : Scheme.{u}} {C H G : GroupScheme S}

/-- If `j` represents `E` and `i` represents the preimage of `F` under `j`, then `i ≫ j`
represents `E ⊓ F`. -/
theorem SubgroupFunctor.IsRepresentedBy.comp_comap {E F : SubgroupFunctor G}
    {j : H ⟶ G} {i : C ⟶ H} (hj : E.IsRepresentedBy j) (hi : (F.comap j).IsRepresentedBy i) :
    (E ⊓ F).IsRepresentedBy (i ≫ j) := by
  have : Mono j.hom.hom := hj.1
  have : Mono i.hom.hom := hi.1
  refine ⟨by change Mono (i.hom.hom ≫ j.hom.hom); infer_instance, ?_⟩
  refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ≫ i.hom.hom ∈ (F.comap j).carrier T := by
      rw [← hi.2]
      exact SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hj.2]
      exact SubgroupFunctor.mem_range.2 ⟨y ≫ i.hom.hom, Category.assoc _ _ _⟩
    · have := SubgroupFunctor.mem_comap.1 hy
      change (y ≫ i.hom.hom ≫ j.hom.hom) ∈ F.carrier T
      simpa only [Category.assoc] using this
  · rintro ⟨hE, hF⟩
    rw [← hj.2] at hE
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hE
    have hz : z ∈ (F.comap j).carrier T := SubgroupFunctor.mem_comap.2 hF
    rw [← hi.2] at hz
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hz
    exact ⟨y, by simp only [Grp.comp_hom_hom, Category.assoc]⟩

end Represented

section Weights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For three cocharacters of a split torus with zero sum, a Lie vector of nonnegative weight
for each of them has weight zero for the difference of the first two. -/
theorem nonnegativeWeightSpan_inf_inf_le (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G)
    (ν₁ ν₂ ν₃ : cocharacterLattice T) (hsum : ν₁ + ν₂ + ν₃ = 0) :
    nonnegativeWeightSpan t ν₁ ⊓ nonnegativeWeightSpan t ν₂ ⊓ nonnegativeWeightSpan t ν₃ ≤
      weightSpace (CommGroupScheme.groupHom (ν₁ - ν₂) ≫ t) (Gm.powerHom _ 0) := by
  classical
  have hind := (isInternal_weightSpace_of_isSplitTorus k G T hT t).submodule_iSupIndep
  let s : cocharacterLattice T → Set (characterLattice T) :=
    fun ν => {χ | 0 ≤ latticePairing T χ ν}
  have hA (ν : cocharacterLattice T) :
      nonnegativeWeightSpan t ν = ⨆ χ ∈ s ν, weightSpace t χ := rfl
  rw [hA, hA, hA]
  refine le_trans (inf_le_inf_right _ (biSup_inf_biSup_le_of_iSupIndep hind _ _)) ?_
  refine le_trans (biSup_inf_biSup_le_of_iSupIndep hind _ _) ?_
  refine iSup₂_le fun χ hχ => ?_
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hχ
  have hs := congrArg (latticePairing T χ) hsum
  simp only [map_add, map_zero] at hs
  change 0 ≤ latticePairing T χ ν₁ at h₁
  change 0 ≤ latticePairing T χ ν₂ at h₂
  change 0 ≤ latticePairing T χ ν₃ at h₃
  have h0 : latticePairing T χ (ν₁ - ν₂) = 0 := by
    rw [map_sub]
    omega
  have h := weightSpace_le_weightSpace_cocharacter (ν₁ - ν₂) t χ
  rwa [h0] at h

end Weights

section Intersection

set_option maxHeartbeats 1000000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Three cocharacters of a split torus with zero sum, such that every root with zero
value on the difference of the first two vanishes on all three. The intersection of their
dynamic parabolics is the dynamic centralizer of that difference, on every test scheme. -/
theorem parabolic_inf_parabolic_inf_parabolic_eq_centralizer
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ν₁ ν₂ ν₃ : cocharacterLattice T)
    (hsum : ν₁ + ν₂ + ν₃ = 0)
    (hzero : ∀ α ∈ relativeRoots t, latticePairing T α (ν₁ - ν₂) = 0 →
      latticePairing T α ν₁ = 0 ∧ latticePairing T α ν₂ = 0 ∧ latticePairing T α ν₃ = 0) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν₁ ≫ t) ⊓
        Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ t) ⊓
        Dynamic.parabolic (CommGroupScheme.groupHom ν₃ ≫ t) =
      Dynamic.centralizer (CommGroupScheme.groupHom (ν₁ - ν₂) ≫ t) := by
  have hGa : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  set χ₀ := CommGroupScheme.groupHom (ν₁ - ν₂) ≫ t with hχ₀
  have hZle (ν : cocharacterLattice T)
      (hν : ∀ α ∈ relativeRoots t, latticePairing T α (ν₁ - ν₂) = 0 →
        latticePairing T α ν = 0) :
      Dynamic.centralizer χ₀ ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) :=
    (dynamicCentralizer_le_of_root_zero_imp dynamicConnected hT t _ ν hν).trans
      (Dynamic.centralizer_le_parabolic _)
  have hZ : Dynamic.centralizer χ₀ ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν₁ ≫ t) ⊓
        Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ t) ⊓
        Dynamic.parabolic (CommGroupScheme.groupHom ν₃ ≫ t) :=
    fun U x hx => ⟨⟨hZle ν₁ (fun α hα h => (hzero α hα h).1) U hx,
      hZle ν₂ (fun α hα h => (hzero α hα h).2.1) U hx⟩,
      hZle ν₃ (fun α hα h => (hzero α hα h).2.2) U hx⟩
  refine le_antisymm ?_ hZ
  -- Representatives of the first two parabolics and of their intersection.
  let i₁ := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν₁ ≫ t)
  let i₂ := Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν₂ ≫ t)
  have hi₁ := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν₁ ≫ t)
  have hi₂ := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν₂ ≫ t)
  have hc₁ := Dynamic.Affine.isClosedSubgroup_parabolicHom (CommGroupScheme.groupHom ν₁ ≫ t)
  have hc₂ := Dynamic.Affine.isClosedSubgroup_parabolicHom (CommGroupScheme.groupHom ν₂ ≫ t)
  have : Mono i₁.hom.hom := hi₁.1
  have : Mono i₂.hom.hom := hi₂.1
  obtain ⟨hsm₁₂, hcon₁₂, tH, htH⟩ := smooth_connected_pullback_of_range_eq_parabolic
    dynamicConnected t ν₁ ν₂ hi₁.2 hi₂.2
  let Q := subgroupIntersection i₁ i₂
  let j₁₂ : Q ⟶ G := subgroupIntersectionHom i₁ i₂
  have hj₁₂c : IsClosedSubgroup j₁₂ := isClosedSubgroup_subgroupIntersectionHom hc₁ hc₂
  have hj₁₂ : (Dynamic.parabolic (CommGroupScheme.groupHom ν₁ ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ t)).IsRepresentedBy j₁₂ := by
    rw [← hi₁.2, ← hi₂.2]
    exact isRepresentedBy_subgroupIntersectionHom hc₁ hc₂
  have : Smooth Q.X.hom := hsm₁₂
  have : ConnectedSpace Q.X.left := hcon₁₂ inferInstance
  have : IsClosedImmersion j₁₂.hom.hom.left := hj₁₂c
  have : IsAffineHom Q.X.hom := by
    rw [← Over.w j₁₂.hom.hom]
    infer_instance
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  let tQ : T.toGrp ⟶ Q := tH
  have htQ : tQ ≫ j₁₂ = t := htH
  -- The third parabolic inside the intersection.
  let χ₃ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Q := CommGroupScheme.groupHom ν₃ ≫ tQ
  let iQ := Dynamic.Affine.parabolicHom χ₃
  have hiQ := Dynamic.Affine.isRepresentedBy_parabolicHom χ₃
  have hcQ := Dynamic.Affine.isClosedSubgroup_parabolicHom χ₃
  have hχ₃ : χ₃ ≫ j₁₂ = CommGroupScheme.groupHom ν₃ ≫ t := by
    change (CommGroupScheme.groupHom ν₃ ≫ tQ) ≫ j₁₂ = _
    rw [Category.assoc, htQ]
  have hPQ : Dynamic.parabolic χ₃ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν₃ ≫ t)).comap j₁₂ := by
    rw [← hχ₃]
    exact Dynamic.parabolic_eq_comap_of_isClosedSubgroup χ₃ j₁₂ hj₁₂c
  let c := iQ ≫ j₁₂
  have hc : (Dynamic.parabolic (CommGroupScheme.groupHom ν₁ ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν₃ ≫ t)).IsRepresentedBy c :=
    SubgroupFunctor.IsRepresentedBy.comp_comap hj₁₂ (hPQ ▸ hiQ)
  have : Mono c.hom.hom := hc.1
  let H := Dynamic.Affine.parabolicScheme χ₃
  have : Smooth H.X.hom := (dynamicSmooth k Q χ₃ H iQ).1 hiQ
  have : ConnectedSpace H.X.left := ((dynamicConnected k Q χ₃ H iQ).2 inferInstance).1 hiQ
  have : IsClosedImmersion iQ.hom.hom.left := hcQ
  have : IsAffineHom H.X.hom := by
    rw [← Over.w iQ.hom.hom]
    infer_instance
  -- The centralizer representative inside `H`.
  let jK := Dynamic.Affine.centralizerHom χ₀
  have hjK := Dynamic.Affine.isRepresentedBy_centralizerHom χ₀
  have hjKc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ₀
  let K := Dynamic.Affine.centralizerScheme χ₀
  have : Mono jK.hom.hom := hjK.1
  have : Smooth K.X.hom := (dynamicSmooth k G χ₀ K jK).2.1 hjK
  have hle : SubgroupFunctor.range jK ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν₁ ≫ t) ⊓
        Dynamic.parabolic (CommGroupScheme.groupHom ν₂ ≫ t) ⊓
        Dynamic.parabolic (CommGroupScheme.groupHom ν₃ ≫ t) := hjK.2 ▸ hZ
  let jKH : K ⟶ H := hc.liftOfLE jK hle
  have hjKH : jKH ≫ c = jK := hc.liftOfLE_comp jK hle
  have hjKHh : jKH.hom.hom ≫ c.hom.hom = jK.hom.hom := congrArg (fun f => f.hom.hom) hjKH
  have hjKHc : IsClosedSubgroup jKH := by
    have : IsClosedImmersion jK.hom.hom.left := hjKc
    have : IsClosedImmersion (jKH.hom.hom.left ≫ c.hom.hom.left) := by
      have h := congrArg (fun f => f.hom.hom.left) hjKH
      simp only at h
      change IsClosedImmersion (jKH ≫ c).hom.hom.left
      rw [hjKH]
      infer_instance
    have : IsClosedImmersion c.hom.hom.left := by
      change IsClosedImmersion (iQ.hom.hom.left ≫ j₁₂.hom.hom.left)
      infer_instance
    exact IsClosedImmersion.of_comp jKH.hom.hom.left c.hom.hom.left
  -- Every Lie vector of `H` comes from the centralizer.
  have hLie : ∀ X : lieKernel H k, ∃ Y : lieKernel K k, Y.val ≫ jKH.hom.hom = X.val := by
    intro X
    let X' : lieKernel G k := Lie.targetMap c k X
    have hX'P (ν : cocharacterLattice T)
        (hcν : SubgroupFunctor.range c ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)) :
        Additive.ofMul X' ∈ nonnegativeWeightSpan t ν := by
      rw [mem_nonnegativeWeightSpan_iff_mem_parabolic hT t ν]
      exact hcν _ (SubgroupFunctor.mem_range.2 ⟨X.val, rfl⟩)
    have hrc := hc.2
    have h₁ := hX'P ν₁ (by rw [hrc]; exact fun _ _ hx => hx.1.1)
    have h₂ := hX'P ν₂ (by rw [hrc]; exact fun _ _ hx => hx.1.2)
    have h₃ := hX'P ν₃ (by rw [hrc]; exact fun _ _ hx => hx.2)
    have hw := nonnegativeWeightSpan_inf_inf_le hT t ν₁ ν₂ ν₃ hsum ⟨⟨h₁, h₂⟩, h₃⟩
    have hcent : X'.val ∈ (Dynamic.centralizer χ₀).carrier _ :=
      (dynamicLie k G χ₀ X').1.2 hw
    rw [← hjK.2] at hcent
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hcent
    have hyK : y ∈ lieKernel K k := by
      apply mem_lieKernel_of_comp jK y
      rw [hy]
      exact X'.property
    refine ⟨⟨y, hyK⟩, ?_⟩
    apply (cancel_mono c.hom.hom).1
    change y ≫ jKH.hom.hom ≫ c.hom.hom = X.val ≫ c.hom.hom
    rw [hjKHh, hy]
    rfl
  have htop := lieSubgroupEquality k H K jKH hjKHc hLie
  intro U x hx
  rw [← hc.2] at hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  have hy : y ∈ (SubgroupFunctor.range jKH).carrier U := by rw [htop]; trivial
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hy
  rw [← hjK.2]
  exact SubgroupFunctor.mem_range.2 ⟨z, by rw [Category.assoc, hjKHh]⟩

end Intersection

end Langlands.GroupScheme
