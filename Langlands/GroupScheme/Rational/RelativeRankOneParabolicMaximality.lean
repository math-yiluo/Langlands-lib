import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Rational.RankOneParabolicMinimality
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison

/-! # Maximality from rank-one roots on a Levi split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P L : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- All actual roots on the specified split torus have proportional integral
pairings, expressed without choosing a primitive generator. -/
def HasProportionalRootPairings (i : A.toGrp ⟶ G) : Prop :=
  ∀ α ∈ relativeRoots i, ∀ β ∈ relativeRoots i,
    ∀ ν eta : cocharacterLattice A,
      latticePairing A α ν * latticePairing A β eta =
        latticePairing A β ν * latticePairing A α eta

namespace ParabolicRootPresentation

variable {p : P ⟶ G} {l : L ⟶ P} {a : A.toGrp ⟶ L}
  (r : ParabolicRootPresentation p l a)

include r in
/-- Every rational parabolic containing the specified parabolic has a defining
cocharacter in the split component of its original Levi. -/
theorem exists_splitComponentCocharacter_of_parabolic_le
    (hG : IsConnectedReductive G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}
    (hh : IsParabolicSubgroup h)
    (hle : SubgroupFunctor.range p ≤ SubgroupFunctor.range h) :
    ∃ eta : cocharacterLattice A,
      SubgroupFunctor.range h =
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ a ≫ l ≫ p) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Smooth L.X.hom := r.isCompatible.levi.isConnectedReductive.smooth
  let : IsAffineHom L.X.hom := r.isCompatible.levi.isConnectedReductive.isAffineHom
  obtain ⟨ν, -, hpν, hlν⟩ := r.isCompatible.realization
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG H h hh.isClosedSubgroup).mp hh
  obtain ⟨ξ, hξ⟩ := exists_parabolic_eq_cocharacter_of_parabolic_le
    smoothMaximalSplitTorusConjugacy dynamicSmooth dynamicConnected
    r.isCompatible.maximalSplit ν χ (by rwa [← hpν, ← hχ])
  have hlc : IsClosedSubgroup (l ≫ p) :=
    r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  let : IsClosedImmersion (l ≫ p).hom.hom.left := hlc
  have hlrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ r.data.i)).IsRepresentedBy
      (l ≫ p) := ⟨Over.mono_of_mono_left _, hlν⟩
  let iL : r.data.T.toGrp ⟶ L :=
    Dynamic.torusFactor r.data.i (CommGroupScheme.groupHom ν) hlrep
  have hiL : iL ≫ (l ≫ p) = r.data.i :=
    Dynamic.torusFactor_comp r.data.i (CommGroupScheme.groupHom ν) hlrep
  let ξL : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L :=
    CommGroupScheme.groupHom ξ ≫ iL
  have hξL : ξL ≫ (l ≫ p) = CommGroupScheme.groupHom ξ ≫ r.data.i := by
    dsimp only [ξL]
    rw [Category.assoc, hiL]
  have hLpar : SubgroupFunctor.range (l ≫ p) ≤
      Dynamic.parabolic (ξL ≫ (l ≫ p)) := by
    rw [hξL, ← hξ, ← hχ]
    exact (SubgroupFunctor.range_comp_le l p).trans hle
  have hLtop : Dynamic.parabolic ξL = ⊤ := by
    rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup ξL (l ≫ p) hlc]
    exact SubgroupFunctor.range_le_iff_comap_eq_top.mp hLpar
  have hcentral : IsCentral ξL :=
    (isCentral_iff_dynamicCentralizer_eq_top ξL).mpr
      ((Dynamic.parabolic_eq_top_iff_centralizer_eq_top
        r.isCompatible.levi.isConnectedReductive.hasTrivialUnipotentRadical ξL).mp hLtop)
  obtain ⟨eta, heta⟩ := r.isCompatible.splitComponent.exists_factor isSplitTorus_gm hcentral
  refine ⟨Additive.ofMul eta, ?_⟩
  change SubgroupFunctor.range h = Dynamic.parabolic (eta ≫ a ≫ l ≫ p)
  rw [← Category.assoc eta a, heta, hξL, ← hξ, ← hχ]

end ParabolicRootPresentation

namespace RelativeRoot

/-- A proper dynamic parabolic in a connected reductive group has a positively
pairing actual root on any split torus through which it is presented. -/
theorem exists_pairing_pos_of_parabolic_ne_top
    (hG : IsConnectedReductive G) (hA : IsSplitTorus A.toGrp)
    (i : A.toGrp ⟶ G) (ν : cocharacterLattice A)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤) :
    ∃ α ∈ relativeRoots i, 0 < latticePairing A α ν := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  by_contra h
  have hnonpos : ∀ α ∈ relativeRoots i, latticePairing A α ν ≤ 0 := by
    intro α hα
    exact le_of_not_gt (fun hpos => h ⟨α, hα, hpos⟩)
  have hneg : Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i) = ⊤ := by
    apply Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots hA i (-ν)
    intro α hα
    simpa only [map_neg] using neg_nonneg.mpr (hnonpos α hα)
  have hZ := (Dynamic.parabolic_eq_top_iff_centralizer_eq_top
    hG.hasTrivialUnipotentRadical _).mp hneg
  rw [Dynamic.centralizer_groupHom_neg] at hZ
  exact hproper (Dynamic.parabolic_eq_top_of_centralizer _ hZ)

/-- On a split torus with proportional actual root pairings, a dynamic
parabolic containing a proper dynamic parabolic is equal to it or full. -/
theorem parabolic_eq_or_top_of_proportional_pairings
    (hG : IsConnectedReductive G) (hA : IsSplitTorus A.toGrp)
    (i : A.toGrp ⟶ G) (hrank : HasProportionalRootPairings i)
    (ν eta : cocharacterLattice A)
    (hproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤)
    (hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)) :
    Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ∨
    Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) = ⊤ := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨α, hα, hαν⟩ := exists_pairing_pos_of_parabolic_ne_top hG hA i ν hproper
  have hαeta : 0 ≤ latticePairing A α eta :=
    nonnegative_rootSupport_of_parabolic_le hA i ν eta hle α hα hαν.le
  by_cases hzero : latticePairing A α eta = 0
  · right
    apply Dynamic.parabolic_eq_top_of_nonnegative_relativeRoots hA i eta
    intro β hβ
    have hcross := hrank β hβ α hα eta ν
    rw [hzero, zero_mul] at hcross
    have hβeta := (mul_eq_zero.mp hcross).resolve_right (ne_of_gt hαν)
    exact hβeta.ge
  · left
    have hαeta' : 0 < latticePairing A α eta :=
      lt_of_le_of_ne hαeta (Ne.symm hzero)
    apply le_antisymm ?_ hle
    apply (parabolic_le_iff_nonnegative_rootSupport dynamicConnected hA i eta ν).mpr
    intro β hβ hβeta
    have hcross := hrank β hβ α hα eta ν
    nlinarith

end RelativeRoot

/-- A proper rational parabolic whose actual roots on the split component of
its fixed Levi have proportional pairings is maximal among rational parabolics. -/
theorem isMaximalParabolic_of_proportional_splitComponent_pairings
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : L ⟶ P} {a : A.toGrp ⟶ L}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (ha : IsSplitComponent a) (hproper : ¬ IsIso p)
    (hrank : HasProportionalRootPairings (a ≫ l ≫ p)) :
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G) (f : P ⟶ H),
      IsParabolicSubgroup h → f ≫ h = p → IsIso f ∨ IsIso h := by
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  obtain ⟨r⟩ := parabolicRootPresentationExistence k G hG P L A p l a hp hl ha
  obtain ⟨ν, -, hpν, -⟩ := r.exists_splitComponentCocharacter
  have hpνproper : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) ≠ ⊤ := by
    intro htop
    exact hproper (isIso_of_full_range p (inferInstance : Mono p.hom.hom) (hpν.trans htop))
  intro H h f hh hf
  let : IsClosedImmersion h.hom.hom.left := hh.isClosedSubgroup
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  have hle : SubgroupFunctor.range p ≤ SubgroupFunctor.range h := by
    rw [← hf]
    exact SubgroupFunctor.range_comp_le f h
  obtain ⟨eta, heta⟩ := r.exists_splitComponentCocharacter_of_parabolic_le hG hh hle
  have hνeta : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ a ≫ l ≫ p) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ a ≫ l ≫ p) := by
    rwa [← hpν, ← heta]
  rcases RelativeRoot.parabolic_eq_or_top_of_proportional_pairings hG ha.1.1.1
    (a ≫ l ≫ p) hrank ν eta hpνproper hνeta with heq | htop
  · left
    have hpeq : SubgroupFunctor.range p = SubgroupFunctor.range h :=
      hpν.trans (heq.symm.trans heta.symm)
    have hprep : (SubgroupFunctor.range h).IsRepresentedBy p :=
      ⟨(inferInstance : Mono p.hom.hom), hpeq⟩
    have hhrep : (SubgroupFunctor.range h).IsRepresentedBy h :=
      ⟨(inferInstance : Mono h.hom.hom), rfl⟩
    let e : P ≅ H := hprep.isoOfIsRepresentedBy hhrep
    have he : e.hom ≫ h = p := hprep.isoOfIsRepresentedBy_hom_comp hhrep
    have hfe : f = e.hom := by
      apply Grp.hom_ext
      apply (cancel_mono h.hom.hom).mp
      exact congrArg (fun b => b.hom.hom) (hf.trans he.symm)
    rw [hfe]
    infer_instance
  · right
    exact isIso_of_full_range h (inferInstance : Mono h.hom.hom) (heta.trans htop)

end Langlands.GroupScheme
