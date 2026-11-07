import Langlands.GroupScheme.Rational.RankOneFixedCosets
import Langlands.GroupScheme.Dynamic.BruhatCellLimit
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.Dynamic.ProperAffineExtension
import Langlands.GroupScheme.Dynamic.SchemeActionLimit
import Langlands.GroupScheme.Dynamic.FlagQuotientCell
import Langlands.GroupScheme.Dynamic.FlagQuotientDensity
import Langlands.GroupScheme.Dynamic.FlagQuotientFiber
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.FiniteFieldTorsorPointProof
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.ParabolicQuotientProperProof
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement

/-! # Parabolic double-coset covering in a descended rank-one group

The covering yields actual opposite factor pairs, and hence the exact rank-one
factorization target, from full-kernel component reductivity alone. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

section Covering

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0)
    (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (he : e.restrict (CommGroupScheme.groupHom a) = AutomorphicAction.conjugation i)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)

include hG hi ha he hpos

/-- In a connected reductive group whose split-torus conjugation descends
through a nonzero character, every rational point lies in a double coset
`P(k) n P(k)` of the dynamic parabolic of a positively pairing cocharacter,
with `n` an actual rational normalizer point. -/
theorem exists_parabolic_mul_normalizer_mul_parabolic
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ n ∈ normalizerPoints i,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 _)),
      ∃ r ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 _)),
        g = p * n * r := by
  let := hG.smooth
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  -- The actual proper flag quotient of the dynamic parabolic.
  let P := Dynamic.Affine.parabolicScheme χ
  let iP : P ⟶ G := Dynamic.Affine.parabolicHom χ
  have hrepr : (Dynamic.parabolic χ).IsRepresentedBy iP :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hclosed : IsClosedSubgroup iP := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have hP : IsParabolicSubgroup iP :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG iP hclosed χ hrepr.2
  obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqcc, hf⟩ :=
    smoothSubgroupQuotientExistence k G P iP hclosed hP.smooth
  let : IsProper Q.hom :=
    parabolicSubgroupQuotientProper k G hG.connectedSpace P iP hP Q q
      hsep hft hqc hsm hsurj hqcc hf
  have hfdyn : ∀ (V : Over (Spec (CommRingCat.of k))) (x y : V ⟶ G.X),
      x ≫ q = y ≫ q ↔ x⁻¹ * y ∈ (Dynamic.parabolic χ).carrier V := by
    simpa only [hrepr.2] using hf
  let : Mono iP.hom.hom := hrepr.1
  let : Smooth q.left := hsm
  let : Surjective q.left := hsurj
  let : QuasiCompact q.left := hqcc
  -- Every rational point of the quotient lifts to a rational group point.
  let χneg := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let U := Dynamic.Affine.unipotentScheme χneg
  let iU : U ⟶ G := Dynamic.Affine.unipotentHom χneg
  have hU : (Dynamic.unipotent χneg).IsRepresentedBy iU :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χneg
  let : IsOpenImmersion (QuotientCell.multiplication iP iU.hom.hom).left :=
    oppositeCellStatement k G χ U P iU iP hU hrepr
  have hlift : ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = p := by
    rcases finite_or_infinite k with hfin | hinf
    · let : Finite k := hfin
      let : Smooth P.X.hom := hP.smooth
      let : IsClosedImmersion iP.hom.hom.left := hclosed
      let : IsAffineHom P.X.hom := by
        rw [← Over.w iP.hom.hom]
        infer_instance
      let : ConnectedSpace G.X.left := hG.connectedSpace
      have hPconn := DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic
        G χ hrepr
      exact Dynamic.rational_lifts_of_finite_torsor k G P q iP hf
        finiteFieldTorsorPointStatement.{u} hPconn
    · let : Infinite k := hinf
      let seed := Dynamic.flagQuotientCell k iP iU q hf
      have hseed := Dynamic.range_identity_subset_flagQuotientCell k iP iU q hf
      rw [rationalPointEquiv_left] at hseed
      exact Dynamic.rational_lifts_of_reductive_density k G (SubgroupFunctor.range iP) q hf
        reductiveRationalPointDensity.{u} hG seed.1 seed.2 hseed
        (Dynamic.flagQuotientCell_comp k iP iU q hf)
  -- Left translation on the quotient and the extended cocharacter orbit.
  let act := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range iP) q hf
  have hact : ∀ (V : Over (Spec (CommRingCat.of k))) (x y : V ⟶ G.X),
      act.act x (y ≫ q) = (x * y) ≫ q :=
    fun V x y => Dynamic.flagQuotientSchemeAction_act_lift G _ q hf x y
  obtain ⟨ext, hext⟩ :=
    AffineLine.exists_extension_of_isProper Q ((act.restrict χ).gmOrbit (g ≫ q))
  have hext' : (act.restrict χ).IsGmOrbitExtension (g ≫ q) ext := hext
  have hfix := hext'.isFixed_evalZero
  -- A rational representative of the fixed limit coset.
  obtain ⟨g₀, hg₀⟩ := hlift (rationalPointEquiv k Q (Dynamic.evalZero ext))
  let g₁ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
    (rationalPointEquiv k G.X).symm g₀
  have hg₁ : g₁ ≫ q = Dynamic.evalZero ext := by
    apply (rationalPointEquiv k Q).injective
    rw [rationalPointEquiv_natural, Equiv.apply_symm_apply, hg₀]
  have hfixed : ∀ (V : Over (Spec (CommRingCat.of k)))
      (z : V ⟶ (Gm (Spec (CommRingCat.of k))).X),
      ((z ≫ χ.hom.hom) * G.constantPoint g₁ V) ≫ q = G.constantPoint g₁ V ≫ q := by
    intro V z
    have h := hfix V (Over.homMk V.hom (by simp)) z
    rw [SchemeAction.restrict_act, ← hg₁, ← Category.assoc, hact] at h
    exact h
  -- Replace that representative by an actual normalizer point.
  let n := normalizerRepresentativeOfFixedCoset i hi a ha e he ν hpos q hfdyn g₁ hfixed
  have hn : Dynamic.evalZero ext = n.1.val ≫ q := by
    rw [n.2.1, hg₁]
  obtain ⟨b₁, b₂, hb⟩ :=
    Dynamic.BruhatCellLimit.exists_eq_mul_mul_of_mem_normalizerPoints
      iP i q act hact hf (CommGroupScheme.groupHom ν) hrepr n.1.val g n.1.property hext' hn
  refine ⟨n.1.val, n.1.property, b₁ ≫ iP.hom.hom, ?_, b₂ ≫ iP.hom.hom, ?_, hb⟩
  · rw [← hrepr.2]
    exact SubgroupFunctor.mem_range.mpr ⟨b₁, rfl⟩
  · rw [← hrepr.2]
    exact SubgroupFunctor.mem_range.mpr ⟨b₂, rfl⟩

end Covering

/-- Full-kernel component reductivity alone gives actual opposite factor
pairs: the descended rank-one covering above replaces rational Bruhat. -/
theorem exists_oppositeFactorPair_of_componentReductivity
    (hRed : KernelCentralizerComponentReductiveStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0) (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) :
    ∃ p, IsOppositeFactorPair i a x p := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  by_cases hx1 : x = 1
  · subst x
    refine ⟨(1, 1), Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
    simpa only [one_mul] using (normalizerPoints i).one_mem
  obtain ⟨C, j, hj, hjc, hCs, _⟩ :=
    kernelCentralizerStructure k G inferInstance inferInstance T hi.1.1 i a ha
  let : Smooth C.X.hom := hCs
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : IsAffineHom C.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let iC := kernelCentralizerIdentityTorus i hi.1.1 a j hj
  have hC : IsConnectedReductive (identityComponent C) :=
    hRed k G hG T hi.1.1 i a ha C j hj hjc hCs
  let : IsAffineHom (identityComponent C).X.hom := hC.isAffineHom
  let : IsAffine (identityComponent C).X.left :=
    isAffine_of_isAffineHom (identityComponent C).X.hom
  let : Smooth (identityComponent C).X.hom := hC.smooth
  have hneg : (kernelCentralizer i (-a)).IsRepresentedBy j := by
    simpa only [kernelCentralizer_neg] using hj
  have ha' : -a ≠ 0 := neg_ne_zero.mpr ha
  obtain ⟨ν, -, hpos⟩ := exists_genericCocharacter_pairing_pos iC hi.1.1 ha'
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k T hi.1.1 (-a) ha'
  let : QuasiCompact (CommGroupScheme.groupHom (-a)).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom (-a)).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom (-a)).hom.hom.left := hsurj
  -- The covering inside the component, for the descended action through `-a`.
  have hcoverP := exists_parabolic_mul_normalizer_mul_parabolic hC
    (kernelCentralizerIdentityTorus i hi.1.1 (-a) j hneg)
    (hi.kernelCentralizerIdentityTorus (-a) j hneg hjc) (-a) ha'
    (kernelCentralizerIdentityQuotientAction i hi.1.1 (-a) j hneg)
    (kernelCentralizerIdentityQuotientAction_restrict i hi.1.1 (-a) j hneg) ν hpos
  rw [kernelCentralizerIdentityTorus_neg i hi.1.1 a j hj] at hcoverP
  have hU : Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ iC) =
      subgroup iC (-a) := by
    have h := kernelCentralizerIdentity_dynamicUnipotent_eq_subgroup
      i hi.1.1 (-a) ha' j hneg ν hpos
    simpa only [kernelCentralizerIdentityTorus_neg i hi.1.1 a j hj] using h
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ iC) =
      torusCentralizer iC := by
    have h := kernelCentralizerIdentity_dynamicCentralizer_eq_torusCentralizer
      i hi.1.1 (-a) ha' j hneg ν hpos.ne'
    simpa only [kernelCentralizerIdentityTorus_neg i hi.1.1 a j hj] using h
  have hcover := unipotentNormalizerCovering_of_parabolicNormalizerCovering iC ν hZ hcoverP
  apply (forall_exists_oppositeFactorPair_kernelCentralizerIdentity_iff
    i hi.1.1 a ha j hj hjc).mp ?_ x hx hx1
  intro y _hy _hy1
  obtain ⟨n, u, v, heq⟩ := hcover y
  have hu : (u : rationalPoints (identityComponent C)) ∈
      (subgroup iC (-a)).carrier (Over.mk (𝟙 _)) := hU ▸ u.property
  have hv : (v : rationalPoints (identityComponent C)) ∈
      (subgroup iC (-a)).carrier (Over.mk (𝟙 _)) := hU ▸ v.property
  refine ⟨((u : rationalPoints (identityComponent C))⁻¹,
    (v : rationalPoints (identityComponent C))⁻¹),
    Subgroup.inv_mem _ hu, Subgroup.inv_mem _ hv, ?_⟩
  have hn : (u : rationalPoints (identityComponent C))⁻¹ * y *
      (v : rationalPoints (identityComponent C))⁻¹ = n.val := by
    rw [heq]
    simp [mul_assoc]
  rw [hn]
  exact n.property

/-- The actual ordered pair selected from this reduction, with full-kernel
component reductivity as the only geometric input. -/
def oppositeFactorPairOfComponentReductivity
    (hRed : KernelCentralizerComponentReductiveStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ≠ 0) (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) :
    {p // IsOppositeFactorPair i a x p} :=
  ⟨Classical.choose
    (exists_oppositeFactorPair_of_componentReductivity hRed k G hG T i hi a ha x hx),
    Classical.choose_spec
      (exists_oppositeFactorPair_of_componentReductivity hRed k G hG T i hi a ha x hx)⟩

end RelativeRoot

/-- Full-kernel component reductivity implies the exact actual rank-one
factorization target. -/
theorem rootRankOneFactorization_of_componentReductivity
    (hRed : RelativeRoot.KernelCentralizerComponentReductiveStatement.{u}) :
    RootRankOneFactorizationStatement.{u} := by
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let : Smooth G.X.hom := hG.smooth
  exact RelativeRoot.hasRankOneFactorization_of_hasOppositeFactorPairs i hi.1.1
    (fun a ha x hx _ =>
      RelativeRoot.exists_oppositeFactorPair_of_componentReductivity
        hRed k G hG T i hi a ha.1 x hx)

end Langlands.GroupScheme
