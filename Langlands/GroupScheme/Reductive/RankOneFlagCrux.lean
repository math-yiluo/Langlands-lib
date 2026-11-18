import Langlands.GroupScheme.Reductive.RankOneFlagDimension
import Langlands.GroupScheme.SchemeActionProperFixedFromAffine
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Dynamic.HomogeneousCurveUnipotentProof
import Langlands.GroupScheme.Reductive.PositiveRootTangentDimension
import Langlands.GroupScheme.Reductive.RankOneSignedTangentDimension
import Langlands.GroupScheme.Reductive.RankOneLocalCover

/-! # The local line crux in semisimple rank one

A base point of `G/B` fixed by `T` and by `U(-ν)` for `ν` or `-ν`, the kernel step through
the Library curve lemma, and the local line crux. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneFlag

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- Conjugation by the inverse of a rational point, on points. -/
theorem comp_innerIso_inv (n : pt k ⟶ G.X) {W : Over (Spec (CommRingCat.of k))} (u : W ⟶ G.X) :
    u ≫ (G.innerIso n⁻¹).hom.hom.hom = (toUnit W ≫ n)⁻¹ * (u * (toUnit W ≫ n)) := by
  rw [comp_innerIso_hom, constantPoint_inv, inv_inv, FlagData.toUnit_comp, mul_assoc]

/-- **The base point.** A `T`-fixed point fixed by `U(-ν)` lies in `{x₀, x₁}`; hence either
`U(-ν)` or `U(ν)` lies in `B`, and core data exist for `ν` or for `-ν`. -/
theorem exists_coreData [IsAlgClosed k] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (F : FlagData i) (ν : cocharacterLattice T)
    (hZp : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i)
    (hZn : (Dynamic.centralizer (CommGroupScheme.groupHom (-ν) ≫ i)).IsRepresentedBy i)
    (hcp : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).comap
        (G.innerIso (F.n : pt k ⟶ G.X)⁻¹).hom)
    (hcn : Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i) =
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).comap
        (G.innerIso (F.n : pt k ⟶ G.X)⁻¹).hom) :
    ∃ D : CoreData i, D.toFlagData = F ∧ (D.ν = ν ∨ D.ν = -ν) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom (-ν) ≫ i
  let U := Dynamic.Affine.unipotentScheme χ
  let j : U ⟶ G := Dynamic.Affine.unipotentHom χ
  have hj : (Dynamic.unipotent χ).IsRepresentedBy j := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have : IsAffineHom U.X.hom := hjc.isAffineHom
  have : LocallyOfFiniteType U.X.hom := hjc.locallyOfFiniteType
  have : Smooth U.X.hom := (dynamicSmooth k G χ U j).2.2 hj
  have hUc : ConnectedSpace U.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hj
  have hUs : IsSolvableGroupScheme U :=
    isSolvableGroupScheme_of_isUnipotent (dynamicUnipotentUnipotence k G χ U j hj)
  have hne : Nonempty F.X.left := ⟨F.x₀.left (IsLocalRing.closedPoint k)⟩
  obtain ⟨y, hy⟩ := solvableProperFixedPoint k U hUc hUs F.X F.quot.proper hne (F.act.restrict j)
  have hnorm : ∀ (c : cocharacterLattice T) (Q : Over (Spec (CommRingCat.of k)))
      (s : Q ⟶ (Gm (Spec (CommRingCat.of k))).X) (v : Q ⟶ U.X), ∃ v' : Q ⟶ U.X,
        v' ≫ j.hom.hom = (s ≫ (CommGroupScheme.groupHom c ≫ i).hom.hom)⁻¹ * (v ≫ j.hom.hom) *
          (s ≫ (CommGroupScheme.groupHom c ≫ i).hom.hom) := by
    intro c Q s v
    have hg : (s ≫ (CommGroupScheme.groupHom c ≫ i).hom.hom)⁻¹ ∈
        (Dynamic.parabolic χ).carrier Q := by
      apply Dynamic.centralizer_le_parabolic
      rw [← hZn.2]
      refine SubgroupFunctor.mem_range.mpr ⟨(s ≫ (CommGroupScheme.groupHom c).hom.hom)⁻¹, ?_⟩
      rw [GrpObj.inv_comp, Grp.comp_hom_hom, Category.assoc]
    have hv : v ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier Q := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩
    have h := Dynamic.conj_mem_unipotent χ hg hv
    rw [inv_inv, ← hj.2] at h
    exact SubgroupFunctor.mem_range.mp h
  obtain ⟨w, hwT, hwU⟩ := SplitTorusLimitInduction.limit_induction (F.act.restrict i) hT
    (fun w => (F.act.restrict j).IsFixed w)
    (fun w => ∃ w', (F.act.restrict i).IsFixed w' ∧ (F.act.restrict j).IsFixed w')
    (fun c w e he hw => SplitTorusLimitInduction.isFixed_evalZero_of_normalizes F.act
      (CommGroupScheme.groupHom c ≫ i) j (hnorm c)
      ((RankOneFlagCell.isGmOrbitExtension_restrict_restrict_iff _ _ _ _ _).mp he) hw)
    (fun _ _ _ _ _ h => h) (fun w hwT hwP => ⟨w, hwT, hwP⟩) y hy
  rcases F.eq_or_eq_of_isFixed hG hT hi hdep hwT with rfl | rfl
  · have hB : Dynamic.unipotent χ ≤ SubgroupFunctor.range F.b := by
      intro W u hu
      rw [← hj.2] at hu
      obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hu
      have h := (F.isFixed_iff j 1).mp hwU W v
      rwa [MonObj.comp_one, inv_one, one_mul, mul_one] at h
    refine ⟨{ F with ν := ν, hZp := hZp, hZn := hZn, hconj := ?_, hB := hB }, rfl, Or.inl rfl⟩
    intro W u hu
    rw [hcp] at hu
    rw [← comp_innerIso_inv]
    exact hu
  · have hB : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) ≤
        SubgroupFunctor.range F.b := by
      intro W u hu
      let v : W ⟶ G.X := (toUnit W ≫ (F.n : pt k ⟶ G.X)) * u * (toUnit W ≫ (F.n : pt k ⟶ G.X))⁻¹
      have hvu : v ≫ (G.innerIso (F.n : pt k ⟶ G.X)⁻¹).hom.hom.hom = u := by
        rw [comp_innerIso_inv]
        simp only [v]
        group
      have hv : v ∈ (Dynamic.unipotent χ).carrier W := by
        change v ∈ (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier W
        rw [hcn, SubgroupFunctor.mem_comap, hvu]
        exact hu
      rw [← hj.2] at hv
      obtain ⟨v', hv'⟩ := SubgroupFunctor.mem_range.mp hv
      have h := (F.isFixed_iff j F.n).mp hwU W v'
      rw [hv', ← comp_innerIso_inv, hvu] at h
      exact h
    refine ⟨{ F with ν := -ν, hZp := hZn, hZn := ?_, hconj := ?_, hB := ?_ }, rfl, Or.inr rfl⟩
    · rw [neg_neg]; exact hZp
    · intro W u hu
      rw [neg_neg, ← comp_innerIso_inv, ← SubgroupFunctor.mem_comap, ← hcn]
      exact hu
    · rw [neg_neg]; exact hB

/-- **The kernel step.** The quotient curve and noncontainment give the Library curve lemma, so
the tangent of `U(ν)` has dimension at most one. -/
theorem CoreData.finrank_tangent_le_one [IsAlgClosed k] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (D : CoreData i) :
    haveI := hG.isAffineHom
    Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom D.ν ≫ i))) ≤ 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have hdimQ := D.topologicalKrullDim_le_one hG hT hi hdep
  have hnot : ¬ Dynamic.unipotent (CommGroupScheme.groupHom D.ν ≫ D.t ≫ D.b) ≤
      SubgroupFunctor.range D.b := by
    rw [D.ht]
    exact D.not_unipotent_le hT hi
  have h := (HomogeneousQuotient.curveUnipotentDataOfPseudoReductive D.b D.q D.quot.fibers
    hG.isPseudoReductive D.borel.isClosedSubgroup D.borel.isSolvableGroupScheme hT D.t D.ν
    hdimQ hnot).finrank_tangent_le_one
  rwa [D.ht] at h

/-- A root positive on `ν` has a line as weight space when the tangent of `U(ν)` has dimension at
most one. -/
theorem finrank_weightSpace_eq_one [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hT : IsSplitTorus T.toGrp) {χ : characterLattice T} (hχ : χ ∈ roots i)
    {ν : cocharacterLattice T} (hpos : 0 < latticePairing T χ ν)
    (hdim : Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) ≤ 1) :
    Module.finrank k (weightSpace i χ) = 1 := by
  let : Nontrivial (weightSpace i χ) := Submodule.nontrivial_iff_ne_bot.mpr hχ.2
  have h0 : 0 < Module.finrank k (weightSpace i χ) := Module.finrank_pos
  have hle : Module.finrank k (weightSpace i χ) ≤ Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) :=
    Submodule.finrank_mono (RelativeRoot.weightSpace_le_tangentSubmodule_unipotent hT i ν hpos)
  omega

end RankOneFlag

namespace RankOneLocalCover

/-- **The local line crux.** In semisimple rank one over an algebraically closed field, every
root `α` is the only root positive on a suitable cocharacter `ν`, `-α` the only root negative on
it, and the root spaces of `±α` are lines. -/
theorem localLineCrux : LocalLineCrux.{u} := by
  intro k _ _ G hG T hT i hi hdep α hα
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := hi.2.1.mono
  obtain ⟨F⟩ := RankOneFlag.nonempty_flagData hG hT i hi hα
  let n' : normalizerPoints i := F.n⁻¹
  have hn' : (QuotientGroup.mk n' : relativeWeylGroup i) ≠ 1 := by
    simp only [n', QuotientGroup.mk_inv, ne_eq, inv_eq_one]
    exact F.hn
  have hα0 : α ≠ 0 := (mem_relativeRoots.mp hα).1
  obtain ⟨ν₀, hν₀⟩ := RankOneLocalAssembly.exists_latticePairing_pos hT hα0
  let ν := normalizerSymmetrizedCocharacter i n' ν₀
  have hpair : ∀ β ∈ roots i, latticePairing T β ν = 2 * latticePairing T β ν₀ :=
    fun β hβ => hG.latticePairing_normalizerSymmetrizedCocharacter i hi hT hdep n' hn' β ν₀ hβ
  have hαν : 0 < latticePairing T α ν := by
    rw [hpair α hα]
    omega
  have hnegroot : ∀ β ∈ roots i, -β ∈ roots i := by
    intro β hβ
    have h := hG.weylAction_eq_neg_of_rankOne i hi hT hdep n' hn' β hβ
    rw [← h]
    exact weylAction_mapsTo_relativeRoots i n' hβ
  have hZp := rankOne_centralizer_isRepresentedBy dynamicCentralizerReductive hG hT i hi hdep
    α hα ν hαν.ne'
  have hZn := rankOne_centralizer_isRepresentedBy dynamicCentralizerReductive hG hT i hi hdep
    α hα (-ν) (by rw [map_neg]; omega)
  have hsym : normalizerSymmetrizedCocharacter i n' (-ν₀) = -ν := by
    simp only [ν, normalizerSymmetrizedCocharacter, map_neg]
    abel
  have hcp := hG.unipotent_normalizerSymmetrizedCocharacter_conj i hi hT hdep n' ν₀
  have hcn := hG.unipotent_normalizerSymmetrizedCocharacter_conj i hi hT hdep n' (-ν₀)
  rw [hsym, neg_neg] at hcn
  obtain ⟨D, -, hDν⟩ := RankOneFlag.exists_coreData hG hT hi hdep F ν hZp hZn hcp hcn
  have hdimD := D.finrank_tangent_le_one hG hT hi hdep
  have heq := hG.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg i hi hT hdep
    n' ν₀
  have hdim : Module.finrank k (RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) ≤ 1 ∧
      Module.finrank k (RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i))) ≤ 1 := by
    rcases hDν with h | h
    · rw [h] at hdimD
      exact ⟨hdimD, heq ▸ hdimD⟩
    · rw [h] at hdimD
      exact ⟨heq.symm ▸ hdimD, hdimD⟩
  have hpos : ∀ β ∈ roots i, 0 < latticePairing T β ν → β = α := fun β hβ hβν =>
    RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one hT i ν hdim.1
      hβ hα hβν hαν
  refine ⟨ν, hαν, hpos, ?_, ?_, ?_⟩
  · intro β hβ hβν
    have h := hpos (-β) (hnegroot β hβ) (by rw [map_neg, LinearMap.neg_apply]; omega)
    rw [← h, neg_neg]
  · exact Module.nonempty_linearEquiv_of_finrank_eq_one
      (RankOneFlag.finrank_weightSpace_eq_one hT hα hαν hdim.1)
  · exact Module.nonempty_linearEquiv_of_finrank_eq_one
      (RankOneFlag.finrank_weightSpace_eq_one hT (hnegroot α hα)
        (ν := -ν) (by rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg]; exact hαν) hdim.2)

end RankOneLocalCover

end Langlands.GroupScheme
