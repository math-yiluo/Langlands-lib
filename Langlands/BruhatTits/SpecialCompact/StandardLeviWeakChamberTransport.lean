import Langlands.BruhatTits.SpecialCompact.StandardLeviComponentTransport
import Langlands.BruhatTits.SpecialCompact.StandardLeviIwahoriTransport
import Langlands.BruhatTits.SpecialCompact.WeakIwahoriBasisReduction
import Langlands.Geometry.Building.StandardLeviStrictUniformizerProof

/-! # Weak-chamber preservation inherited by a standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe uG uH u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type uH} [Group H] {G : Type uG} [Group G]

/-- Weak-chamber preservation pulls back when every source conjugation is
realized by one of the original chamber points on the image group. -/
theorem WeakChamberContraction.comap_of_conjugationLifts
    (f : H →* G) (K N Nbar : Subgroup G) (P : Set G) (Q : Set H)
    (h : WeakChamberContraction K N Nbar P)
    (hlift : ∀ m ∈ Q, ∃ p ∈ P, ∀ x : H, f (m * x * m⁻¹) = p * f x * p⁻¹) :
    WeakChamberContraction (K.comap f) (N.comap f) (Nbar.comap f) Q := by
  intro m hm
  obtain ⟨p, hp, hconj⟩ := hlift m hm
  have hconjinv (x : H) : f (m⁻¹ * x * m) = p⁻¹ * f x * p := by
    have he : f x = p * f (m⁻¹ * x * m) * p⁻¹ := by
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one] using
        hconj (m⁻¹ * x * m)
    calc f (m⁻¹ * x * m) = p⁻¹ * (p * f (m⁻¹ * x * m) * p⁻¹) * p := by group
      _ = p⁻¹ * f x * p := by rw [← he]
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    change f (m * x * m⁻¹) ∈ K ⊓ N
    rw [hconj]
    exact (h p hp).1 ⟨f x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    change f (m⁻¹ * x * (m⁻¹)⁻¹) ∈ K ⊓ Nbar
    rw [inv_inv, hconjinv]
    exact (h p hp).2 ⟨f x, hx, by simp only [inv_inv]⟩

end Groups

section Rational

variable {F : Type u} [Field F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  {R : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

/-- Every integral cocharacter annihilating the selected simple roots lifts
to the same compatible component, not only strictly positive ones. -/
theorem IsCompatibleStandardSplitComponent.exists_cocharacter_lift_of_annihilates
    (hA : IsCompatibleStandardSplitComponent i ν R A q)
    (hi : IsMaximalSplitTorus i)
    (hexists : ∃ ζ, IsStandardCocharacter i ν R ζ)
    (eta : cocharacterLattice S) (heta : ∀ α ∈ R, latticePairing S α eta = 0) :
    ∃ d : cocharacterLattice A, cocharacterMapInt (Additive.ofMul q) d = eta := by
  obtain ⟨_, M, j, a, hj, _, hM, ha, hcompat⟩ := hA
  have := hM.isAffineHom
  have := hi.isSplitSubtorus.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let t := standardLeviTorusFactor i ν R hj
  have ht : t ≫ j = i := standardLeviTorusFactor_comp i ν R hj
  obtain ⟨d, hd⟩ := ha.exists_factor isSplitTorus_gm
    (isCentral_standardLeviTorusFactor_of_annihilates i ν R hj
      (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν) hexists eta heta)
  refine ⟨Additive.ofMul d, ?_⟩
  change Additive.ofMul (d ≫ q) = eta
  apply Additive.ofMul.injective
  apply Grp.hom_ext
  apply (cancel_mono i.hom.hom).mp
  have he : (d ≫ q) ≫ i = CommGroupScheme.groupHom eta ≫ i := by
    rw [Category.assoc, ← hcompat, ← Category.assoc, hd, Category.assoc, ht]
  exact congrArg (fun f => f.hom.hom) he

/-- A finite nonnegative integer controlling all original component pairings. -/
def standardLeviWeakChamberShift [Fintype (Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν)]
    (c : cocharacterLattice A) : ℤ :=
  ∑ α : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν,
    |latticePairing A (componentCharacterRestriction q α.val) c|

omit [LocallyOfFiniteType G.X.hom] in
/-- Each absolute pairing is bounded by the finite shift. -/
theorem standardLeviWeakChamberShift_bound
    [Fintype (Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν)]
    (c : cocharacterLattice A) (α : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν) :
    |latticePairing A (componentCharacterRestriction q α.val) c| ≤
      standardLeviWeakChamberShift i ν (q := q) c := by
  unfold standardLeviWeakChamberShift
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun β : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν =>
      |latticePairing A (componentCharacterRestriction q β.val) c|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ α)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

attribute [local instance] Langlands.HarishChandraSchwartz.rationalWeightsIsAffine
  Langlands.HarishChandraSchwartz.rationalWeightsTopology
  Langlands.HarishChandraSchwartz.rationalWeightsTopologicalGroup

variable (J : Set (characterLattice S))

local instance weakChamberLeviAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
local instance weakChamberLeviFiniteType : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  Langlands.HarishChandraSchwartz.leviScheme_locallyOfFiniteType i ν J

/-- Every intrinsic weak-chamber conjugation is realized by an ambient weak
chamber point after a central cocharacter adjustment in the outer Levi. -/
theorem exists_ambientWeakChamber_conjugation
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν) (hRJ : R ⊆ J)
    (hA : IsCompatibleStandardSplitComponent i ν R A q)
    (m : rationalPoints (Standard.leviScheme i ν J))
    (hm : m ∈ standardComponentCAplus (Standard.leviTorusHom i ν J) ν R q) :
    ∃ p ∈ standardComponentCAplus i ν R q,
      ∀ x : rationalPoints (Standard.leviScheme i ν J),
        rationalPoints.map (Standard.leviHom i ν J) (m * x * m⁻¹) =
          p * rationalPoints.map (Standard.leviHom i ν J) x * p⁻¹ := by
  classical
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  let iL := Standard.leviTorusHom i ν J
  let f := rationalPoints.map j
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype (Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν) := hfinite.fintype
  obtain ⟨y, ⟨⟨c, rfl⟩, hy⟩, rfl⟩ := hm
  let c0 := c.toAdd
  have hsimple := Langlands.HarishChandraSchwartz.simpleRelativeRoots_leviScheme i ν J hG hi hν hJ
  obtain ⟨eta, heta⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).1
  obtain ⟨d, hd⟩ := hA.exists_cocharacter_lift_of_annihilates i ν hi
    (standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).1 eta
    (fun α hα => heta.2.1 α (hRJ hα))
  let n := standardLeviWeakChamberShift i ν (q := q) c0
  have hn0 : 0 ≤ n := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hbound (α : characterLattice S) (hα : α ∈ simpleRelativeRoots i ν) :
      -(latticePairing A (componentCharacterRestriction q α) c0) ≤ n := by
    exact (neg_le_abs _).trans (standardLeviWeakChamberShift_bound i ν (q := q) c0 ⟨α, hα⟩)
  have hpositive : ∀ α ∈ simpleRelativeRoots i ν \ R,
      0 ≤ latticePairing A (componentCharacterRestriction q α) (c0 + n • d) := by
    intro α hα
    have he : latticePairing A (componentCharacterRestriction q α) (c0 + n • d) =
        latticePairing A (componentCharacterRestriction q α) c0 + n * latticePairing S α eta := by
      rw [map_add, map_zsmul, componentCharacterRestriction_pairing (q := q) d α, hd]
      rfl
    rw [he]
    by_cases hαJ : α ∈ J
    · rw [heta.2.1 α hαJ, mul_zero, add_zero]
      have ht := hy (componentCharacterRestriction q α) ⟨α, ⟨hsimple.symm ▸ hαJ, hα.2⟩, rfl⟩
      change CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α)
        (CocharacterUniformizer.latticeSection F A (.ofAdd c0)) ≤ 1 at ht
      rw [CocharacterUniformizer.characterNorm_latticeSection] at ht
      have hq : (1 : ℝ) < LocalField.residueCardinality F := by
        exact_mod_cast LocalField.residueCardinality_gt_one F
      have ht' := (zpow_le_one_iff_right₀ hq).mp ht
      omega
    · have hp := heta.2.2 α hα.1 hαJ
      have hb := hbound α hα.1
      have he' : 0 ≤ n * (latticePairing S α eta - 1) :=
        mul_nonneg hn0 (by omega)
      nlinarith
  let p := rationalPoints.map (q ≫ i)
    (CocharacterUniformizer.latticeSection F A (.ofAdd (c0 + n • d)))
  have hp : p ∈ standardComponentCAplus i ν R q := by
    refine ⟨_, ⟨⟨.ofAdd (c0 + n • d), rfl⟩, ?_⟩, rfl⟩
    rintro _ ⟨α, hα, rfl⟩
    rw [CocharacterUniformizer.characterNorm_latticeSection]
    have hq : (1 : ℝ) < LocalField.residueCardinality F := by
      exact_mod_cast LocalField.residueCardinality_gt_one F
    exact (zpow_le_one_iff_right₀ hq).mpr (neg_nonpos.mpr (hpositive α hα))
  let z : rationalPoints L := rationalPoints.map iL
    (CocharacterUniformizer.latticeSection F S (.ofAdd eta))
  have hz : z ∈ Subgroup.center (rationalPoints L) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Langlands.HarishChandraSchwartz.map_leviHom_injective
    have hx := standardLevi_le_dynamicCentralizer i ν heta (Over.mk (𝟙 _))
      (Langlands.HarishChandraSchwartz.leviSchemePointsEquiv i ν J x).property
    rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hx
    have he := hx (Over.mk (𝟙 _)) (𝟙 _)
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
        (SplitTorusValuation.uniformizerUnit F))
    have htorus : (Standard.leviTorusHom i ν J).hom.hom ≫
        (Standard.leviHom i ν J).hom.hom = i.hom.hom :=
      congrArg (fun a => a.hom.hom) (Standard.leviTorusHom_comp i ν J)
    simpa only [map_mul, z, iL, CocharacterUniformizer.latticeSection,
      CocharacterUniformizer.cocharacterPoints, MonoidHom.coe_mk, OneHom.coe_mk,
      MonoidHom.comp_apply, rationalPoints.map_apply, Grp.comp_hom_hom,
      Category.assoc, Category.id_comp, Standard.leviTorusHom_comp, htorus,
      toAdd_ofAdd, MulEquiv.coe_toMonoidHom,
      Langlands.HarishChandraSchwartz.leviSchemePointsEquiv_coe] using he.eq
  have hzmap : f z = rationalPoints.map (q ≫ i)
      (CocharacterUniformizer.latticeSection F A (.ofAdd d)) := by
    have hdmap := CocharacterUniformizer.map_latticeSection (F := F) (Additive.ofMul q) d
    rw [hd] at hdmap
    change rationalPoints.map j (rationalPoints.map iL
      (CocharacterUniformizer.latticeSection F S (.ofAdd eta))) = _
    rw [← Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply,
      Standard.leviTorusHom_comp]
    rw [← hdmap]
    rfl
  have hmmap : f (rationalPoints.map (q ≫ iL)
      (CocharacterUniformizer.latticeSection F A c)) = rationalPoints.map (q ≫ i)
        (CocharacterUniformizer.latticeSection F A c) := by
    change rationalPoints.map j (rationalPoints.map (q ≫ iL) _) = _
    rw [← Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply,
      Category.assoc, Standard.leviTorusHom_comp]
  have hpmap : p = f (rationalPoints.map (q ≫ iL)
      (CocharacterUniformizer.latticeSection F A c) * z ^ n) := by
    rw [map_mul, map_zpow, hmmap, hzmap]
    dsimp only [p]
    rw [ofAdd_add, map_mul, ofAdd_zsmul, map_zpow, map_mul, map_zpow]
    rfl
  refine ⟨p, hp, fun x => ?_⟩
  let m0 := rationalPoints.map (q ≫ iL) (CocharacterUniformizer.latticeSection F A c)
  have hzx : z ^ n * x = x * z ^ n :=
    (Subgroup.mem_center_iff.mp ((Subgroup.center _).zpow_mem hz n) x).symm
  have hconj : (m0 * z ^ n) * x * (m0 * z ^ n)⁻¹ = m0 * x * m0⁻¹ := by
    calc (m0 * z ^ n) * x * (m0 * z ^ n)⁻¹ =
        m0 * (z ^ n * x * (z ^ n)⁻¹) * m0⁻¹ := by group
      _ = m0 * x * m0⁻¹ := by rw [hzx]; group
  change f (m0 * x * m0⁻¹) = p * f x * p⁻¹
  calc f (m0 * x * m0⁻¹) = f ((m0 * z ^ n) * x * (m0 * z ^ n)⁻¹) := congrArg f hconj.symm
    _ = f (m0 * z ^ n) * f x * (f (m0 * z ^ n))⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = p * f x * p⁻¹ := by rw [← hpmap]

omit [LocallyOfFiniteType G.X.hom] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
/-- The actual intrinsic radical and opposite radical are the exact
preimages of the original nested standard radicals. -/
theorem standardLeviRadicalPreimages
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν) (hRJ : R ⊆ J) :
    standardUnipotentPoints (Standard.leviTorusHom i ν J) ν R =
        (standardUnipotentPoints i ν R).comap (rationalPoints.map (Standard.leviHom i ν J)) ∧
    standardOppositeUnipotentPoints (Standard.leviTorusHom i ν J) ν R =
        (standardOppositeUnipotentPoints i ν R).comap (rationalPoints.map (Standard.leviHom i ν J)) := by
  let L := Standard.leviScheme i ν J
  let j := Standard.leviHom i ν J
  let iL := Standard.leviTorusHom i ν J
  have hL := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hνL := Langlands.HarishChandraSchwartz.isGenericCocharacter_leviTorusHom (J := J) hν
  have hsimple := Langlands.HarishChandraSchwartz.simpleRelativeRoots_leviScheme i ν J hG hi hν hJ
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).1
  have hζL : IsStandardCocharacter iL ν R ζ := by
    refine ⟨?_, hζ.2.1, fun α hα hαR => hζ.2.2 α (hJ ?_) hαR⟩
    · rw [hsimple]
      exact hRJ
    · exact hsimple ▸ hα
  have hχ : (CommGroupScheme.groupHom ζ ≫ iL) ≫ j = CommGroupScheme.groupHom ζ ≫ i := by
    rw [Category.assoc, Standard.leviTorusHom_comp]
  have hχop : Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ iL) ≫ j =
      Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i) := by
    simpa only [Dynamic.inverseCocharacter, Dynamic.oppositeCocharacter, Category.assoc] using
      congrArg (fun x => CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ x) hχ
  have hN := ((standardCocharacter F G hG S i hi ν hν R (hRJ.trans hJ)).2 ζ hζ).2.2
  have hNL := ((standardCocharacter F L hL S iL hiL ν hνL R hζL.1).2 ζ hζL).2.2
  have hbar := Langlands.Jacquet.standardOppositeUnipotentPoints_eq_dynamic i ν hG hi hν hζ
  have hbarL := Langlands.Jacquet.standardOppositeUnipotentPoints_eq_dynamic iL ν hL hiL hνL hζL
  constructor
  · rw [standardUnipotentPoints, standardUnipotentPoints, hNL, hN]
    have hc := Dynamic.unipotent_eq_comap_of_isClosedSubgroup
      (CommGroupScheme.groupHom ζ ≫ iL) j (Standard.isClosedSubgroup_leviHom i ν J)
    rw [hχ] at hc
    rw [hc]
    rfl
  · rw [hbarL, hbar]
    have hc := Dynamic.unipotent_eq_comap_of_isClosedSubgroup
      (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ iL)) j
      (Standard.isClosedSubgroup_leviHom i ν J)
    rw [hχop] at hc
    rw [hc]
    rfl

/-- Weak-chamber preservation for the SAME compatible component passes to
the full intrinsic chamber, including the additional intrinsic parameters. -/
theorem weakChamberContraction_leviScheme
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν) (hRJ : R ⊆ J)
    (hA : IsCompatibleStandardSplitComponent i ν R A q)
    {K : Subgroup (rationalPoints G)}
    (hweak : WeakChamberContraction K (standardUnipotentPoints i ν R)
      (standardOppositeUnipotentPoints i ν R) (standardComponentCAplus i ν R q)) :
    WeakChamberContraction (Langlands.HarishChandraSchwartz.leviSchemeCompact K i ν J)
      (standardUnipotentPoints (Standard.leviTorusHom i ν J) ν R)
      (standardOppositeUnipotentPoints (Standard.leviTorusHom i ν J) ν R)
      (standardComponentCAplus (Standard.leviTorusHom i ν J) ν R q) := by
  obtain ⟨hN, hbar⟩ := standardLeviRadicalPreimages i ν J hG hi hν hJ hRJ
  rw [hN, hbar]
  exact hweak.comap_of_conjugationLifts (rationalPoints.map (Standard.leviHom i ν J))
    K (standardUnipotentPoints i ν R) (standardOppositeUnipotentPoints i ν R)
    (standardComponentCAplus i ν R q) (standardComponentCAplus (Standard.leviTorusHom i ν J) ν R q)
    (fun m hm => exists_ambientWeakChamber_conjugation i ν J hG hi hν hJ hRJ hA m hm)

/-- Every compact-open ambient basis member for a nested face gives the
full intrinsic basis-member property for the SAME component, not only its
Iwahori or weak-chamber clauses. -/
theorem StandardParabolicBasisMember.leviScheme
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν) (hRJ : R ⊆ J)
    (hA : IsCompatibleStandardSplitComponent i ν R A q)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hmember : StandardParabolicBasisMember i ν R q K) :
    StandardParabolicBasisMember (Standard.leviTorusHom i ν J) ν R q
      (Langlands.HarishChandraSchwartz.leviSchemeCompact K i ν J) := by
  have hAL := hA.leviScheme i ν hG hi hν J hJ hRJ
  have hweak := weakChamberContraction_leviScheme i ν J hG hi hν hJ hRJ hA hmember.2.2.1
  refine ⟨hasIwahoriIntersectionDecomposition_leviScheme i ν J hG hi hν hJ hRJ hmember.1, ?_⟩
  apply hAL.contractionAndCofinality_of_weak (Standard.leviTorusHom i ν J) ν
    (standardLevi_isConnectedReductive hG i hi ν hν J hJ)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    (Langlands.HarishChandraSchwartz.isGenericCocharacter_leviTorusHom (J := J) hν) ?_
    (Langlands.HarishChandraSchwartz.leviSchemeCompact K i ν J)
    (Langlands.HarishChandraSchwartz.isOpen_leviSchemeCompact hKo)
    (Langlands.HarishChandraSchwartz.isCompact_leviSchemeCompact hKc) hweak
  rw [Langlands.HarishChandraSchwartz.simpleRelativeRoots_leviScheme i ν J hG hi hν hJ]
  exact hRJ

end Rational

end Langlands.BruhatTits.SpecialCompact
