import Langlands.GroupScheme.AlgebraicFundamentalGroupMapCoroots
import Langlands.GroupScheme.AlgebraicFundamentalGroupStructureProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugatorExistence
import Langlands.Geometry.Building.Kottwitz.CentralSurjectionZeroSurjectivity
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.CentralSurjection.DerivedMap
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Geometric inputs for central-torus exactness of fundamental groups

For a closed central torus `i : Z → H` with fppf quotient `p : H → G`, and
maximal-torus factorizations `T_Z → T_H → T_G` of `i` and `p`, this module proves:
the restriction `T_H → T_G` has kernel exactly `T_Z`, so the cocharacter sequence
`X_*(T_Z) → X_*(T_H) → X_*(T_G)` is exact on the left and in the middle; the
second map is surjective; and the preimage tori in the simply connected derived
covers of `H` and `G` are isomorphic compatibly with `T_H → T_G`. -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorus

variable {k : Type u} [Field k]
  {Z : CommGroupScheme (Spec (CommRingCat.of k))}
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  {i : Z.toGrp ⟶ H} {p : H ⟶ G}
  {aZ : Choice k Z.toGrp} {b : Choice k H} {c : Choice k G}
  {e : aZ.torus ⟶ b.torus} {e' : b.torus ⟶ c.torus}

/-- The full kernel of the torus restriction `T_H → T_G` has the same points as the
image of `T_Z → T_H`. -/
theorem range_kernelι_eq_range
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hZ : IsIso aZ.inclusion)
    (he : aZ.inclusion ≫ i = CommGroupScheme.groupHom e ≫ b.inclusion)
    (he' : b.inclusion ≫ p = CommGroupScheme.groupHom e' ≫ c.inclusion) :
    SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom e')) =
      SubgroupFunctor.range (CommGroupScheme.groupHom e) := by
  have hb : Mono b.inclusion.hom.hom.left := b.isMaximal.2.1.mono
  have hb' : Mono b.inclusion.hom.hom := Over.mono_of_mono_left _
  have he₀ := congrArg (fun r => r.hom.hom) he
  have he₀' := congrArg (fun r => r.hom.hom) he'
  simp only [Grp.comp_hom_hom] at he₀ he₀'
  apply le_antisymm
  · intro T x hx
    rw [mem_range_kernelι_iff] at hx
    have hx' : x ≫ b.inclusion.hom.hom ∈
        (SubgroupFunctor.range (kernelι p)).carrier T := by
      rw [mem_range_kernelι_iff, Category.assoc, he₀', ← Category.assoc, hx,
        MonObj.one_comp]
    rw [hq.2.2.2] at hx'
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx'
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ (inv aZ.inclusion).hom.hom, ?_⟩
    apply (cancel_mono b.inclusion.hom.hom).mp
    have hinv : (inv aZ.inclusion).hom.hom ≫ aZ.inclusion.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, IsIso.inv_hom_id]
      rfl
    rw [Category.assoc, Category.assoc, ← he₀, ← Category.assoc
      (inv aZ.inclusion).hom.hom, hinv, Category.id_comp, hy]
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [mem_range_kernelι_iff]
    have : Mono c.inclusion.hom.hom.left := c.isMaximal.2.1.mono
    have : Mono c.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono c.inclusion.hom.hom).mp
    rw [MonObj.one_comp, Category.assoc, ← he₀', ← Category.assoc, Category.assoc y,
      ← he₀, ← Category.assoc]
    have hm : (y ≫ aZ.inclusion.hom.hom) ≫ i.hom.hom ∈
        (SubgroupFunctor.range (kernelι p)).carrier T := by
      rw [hq.2.2.2]
      exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
    rwa [mem_range_kernelι_iff] at hm

/-- The restriction `T_Z → T_H` of a closed subgroup inclusion is a monomorphism
when `T_Z → Z` is an isomorphism. -/
theorem mono_torusMap (hi : IsClosedSubgroup i) (hZ : IsIso aZ.inclusion)
    (he : aZ.inclusion ≫ i = CommGroupScheme.groupHom e ≫ b.inclusion) :
    Mono (CommGroupScheme.groupHom e).hom.hom := by
  have : Mono i.hom.hom.left := hi.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsIso aZ.inclusion.hom.hom := (Grp.forget _).map_isIso aZ.inclusion
  have he₀ := congrArg (fun r => r.hom.hom) he
  simp only [Grp.comp_hom_hom] at he₀
  have hm : Mono ((CommGroupScheme.groupHom e).hom.hom ≫ b.inclusion.hom.hom) := by
    rw [← he₀]
    infer_instance
  exact mono_of_mono _ b.inclusion.hom.hom

/-- The torus `T_Z` is the full actual kernel of the restriction `T_H → T_G`. -/
def kernelIso (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hi : IsClosedSubgroup i) (hZ : IsIso aZ.inclusion)
    (he : aZ.inclusion ≫ i = CommGroupScheme.groupHom e ≫ b.inclusion)
    (he' : b.inclusion ≫ p = CommGroupScheme.groupHom e' ≫ c.inclusion) :
    aZ.torus ≅ CommGroupScheme.kernel e' :=
  letI := mono_torusMap hi hZ he
  CommGroupScheme.isoOfGroupIso
    (KernelRepresentative.iso (CommGroupScheme.groupHom e') (CommGroupScheme.groupHom e)
      (range_kernelι_eq_range hq hZ he he')).symm

@[reassoc]
theorem kernelIso_hom_comp (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hi : IsClosedSubgroup i) (hZ : IsIso aZ.inclusion)
    (he : aZ.inclusion ≫ i = CommGroupScheme.groupHom e ≫ b.inclusion)
    (he' : b.inclusion ≫ p = CommGroupScheme.groupHom e' ≫ c.inclusion) :
    (kernelIso hq hi hZ he he').hom ≫ CommGroupScheme.kernelι e' = e := by
  have := mono_torusMap hi hZ he
  apply Additive.toMul.injective
  change (KernelRepresentative.iso (CommGroupScheme.groupHom e') (CommGroupScheme.groupHom e)
      (range_kernelι_eq_range hq hZ he he')).inv ≫
      GroupScheme.kernelι (CommGroupScheme.groupHom e') = CommGroupScheme.groupHom e
  rw [Iso.inv_comp_eq, KernelRepresentative.iso_hom_comp]

variable (E : Type u) [Field E] [Algebra k E]

/-- Geometric cocharacters: `X_*(T_Z) → X_*(T_H)` is injective with image the
kernel of `X_*(T_H) → X_*(T_G)`. -/
theorem torusLatticeMap_exact (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hi : IsClosedSubgroup i) (hZ : IsIso aZ.inclusion)
    (he : aZ.inclusion ≫ i = CommGroupScheme.groupHom e ≫ b.inclusion)
    (he' : b.inclusion ≫ p = CommGroupScheme.groupHom e' ≫ c.inclusion) :
    Function.Injective (aZ.torusLatticeMap b E
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e)) ∧
      LinearMap.ker (b.torusLatticeMap c E
          ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e')) =
        LinearMap.range (aZ.torusLatticeMap b E
          ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e)) := by
  let ψ := (CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso
      (kernelIso hq hi hZ he he') ≪≫
    CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k E) e'
  let l := (cocharacterLattice.congr ψ).trans
    (cocharacterLattice.kernelEquiv ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e'))
  have hl : ∀ w, (l w).val = w ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map e := by
    intro w
    change (w ≫ ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
        (kernelIso hq hi hZ he he').hom ≫
        (CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k E) e').hom)) ≫
      CommGroupScheme.kernelι ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e') = _
    rw [Category.assoc, Category.assoc, CommGroupScheme.kernelBaseChangeIso_hom_ι,
      ← Functor.map_comp, kernelIso_hom_comp]
  refine ⟨?_, ?_⟩
  · intro w w' h
    apply l.injective
    apply Subtype.ext
    rw [hl, hl]
    exact h
  · ext ν
    constructor
    · intro hν
      obtain ⟨w, hw⟩ := l.surjective ⟨ν, hν⟩
      exact ⟨w, (hl w).symm.trans (congrArg Subtype.val hw)⟩
    · rintro ⟨w, rfl⟩
      have hw := (l w).property
      change (l w).val ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map e' = 0 at hw
      rw [hl w] at hw
      exact hw

/-- Geometric cocharacters: `X_*(T_H) → X_*(T_G)` is surjective. -/
theorem torusLatticeMap_surjective [IsSepClosure k E]
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (hZt : IsTorus Z.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hi : IsClosedSubgroup i) (hc : IsCentral i)
    (he' : b.inclusion ≫ p = CommGroupScheme.groupHom e' ≫ c.inclusion) :
    Function.Surjective (b.torusLatticeMap c E
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e')) := by
  have : Surjective p.hom.hom.left := hq.2.1
  have hp : IsCentral (kernelι p) := by
    rw [isCentral_iff_range_le_center, hq.2.2.2, ← isCentral_iff_range_le_center]
    exact hc
  have : Mono i.hom.hom.left := hi.mono
  have hz : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨Over.mono_of_mono_left _, rfl⟩
  have hker : IsTorus (kernel p) := IsTorus.of_iso (hq.kernelIso hz).symm hZt
  exact Geometry.Building.Kottwitz.cocharacter_surjective_of_central_torus_square E hH hG p hp
    hker b.inclusion c.inclusion e' b.isMaximal c.isMaximal.2.1
    (isSplitTorus_baseChange_of_isSepClosure b.torus b.isMaximal.1)
    (isSplitTorus_baseChange_of_isSepClosure c.torus c.isMaximal.1) he'.symm

/-- The derived cover of `H`, followed by the induced map of derived subgroups, is a
simply connected cover of the derived subgroup of `G`; hence it is identified with the
chosen derived cover of `G`. -/
theorem exists_coverIso (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p) (hc : IsCentral i) :
    ∃ ψ : b.cover ≅ c.cover, ψ.hom ≫ c.covering = b.covering ≫ b.derivedMap c p := by
  have : Surjective p.hom.hom.left := hq.2.1
  have hp : IsCentral (kernelι p) := by
    rw [isCentral_iff_range_le_center, hq.2.2.2, ← isCentral_iff_range_le_center]
    exact hc
  have hpD : IsCentralIsogeny (b.derivedMap c p) :=
    b.isCover.isDerivedSubgroup.isCentralIsogeny_map c.isCover.isDerivedSubgroup p hH hG hp
  have hb := b.isCover.isSimplyConnectedCover
  have hcomp : IsCentralIsogeny (b.covering ≫ b.derivedMap c p) :=
    IsCentralIsogeny.comp_of_derivedSubgroup_eq_top
      (semisimplePerfect k b.cover hb.isSimplyConnected.isSemisimple) hb.isCentralIsogeny hpD
  have hcov : IsSimplyConnectedCover (b.covering ≫ b.derivedMap c p) :=
    ⟨c.isCover.isSimplyConnectedCover.isSemisimple, hb.isSimplyConnected, hcomp,
      simplyConnectedCentralCoverUniversalProperty k _ _ _ hb.isSimplyConnected
        c.isCover.isSimplyConnectedCover.isSemisimple hcomp⟩
  exact ⟨hcov.iso c.isCover.isSimplyConnectedCover,
    hcov.iso_hom_comp c.isCover.isSimplyConnectedCover⟩

/-- A cover identification compatible with `p` restricts to an isomorphism of the
preimage tori, compatible with `T_H → T_G`. -/
theorem exists_scTorusIso (ψ : b.cover ≅ c.cover)
    (hψ : ψ.hom ≫ c.covering = b.covering ≫ b.derivedMap c p)
    (he' : b.inclusion ≫ p = CommGroupScheme.groupHom e' ≫ c.inclusion) :
    ∃ φ : b.scTorus ≅ c.scTorus, φ.hom ≫ c.scToTorus = b.scToTorus ≫ e' := by
  have hcond : (b.scInclusion ≫ ψ.hom) ≫ (c.covering ≫ c.derivedInclusion) =
      (CommGroupScheme.groupHom b.scToTorus ≫ CommGroupScheme.groupHom e') ≫
        c.inclusion := by
    simp only [Category.assoc]
    rw [reassoc_of% hψ, Choice.derivedMap_comp, Choice.scInclusion_comp_assoc, he']
  let φ' : b.scTorus.toGrp ⟶ c.scTorus.toGrp :=
    pullback.lift (b.scInclusion ≫ ψ.hom)
      (CommGroupScheme.groupHom b.scToTorus ≫ CommGroupScheme.groupHom e') hcond
  have hφ₁ : φ' ≫ c.scInclusion = b.scInclusion ≫ ψ.hom := pullback.lift_fst _ _ _
  have hφ₂ : φ' ≫ CommGroupScheme.groupHom c.scToTorus =
      CommGroupScheme.groupHom b.scToTorus ≫ CommGroupScheme.groupHom e' :=
    pullback.lift_snd _ _ _
  have : IsIso φ' :=
    (b.scInclusion_isMaximalTorus.comp_iso ψ).2.2 c.scTorus c.scInclusion φ'
      c.scInclusion_isMaximalTorus.1 c.scInclusion_isMaximalTorus.2.1 hφ₁
  refine ⟨CommGroupScheme.isoOfGroupIso (asIso φ'), ?_⟩
  apply Additive.toMul.injective
  exact hφ₂

end Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorus
