import Langlands.Representation.Aubert.General.RationalGeometricTargetEpsilonFactorization
import Langlands.Representation.Aubert.General.CommonCentralizerFullHaarBalance
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitBalanceModels
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.GroupScheme.Rational.LeviSplitComponentProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Dynamic.DominantCombinationInclusions
import Langlands.GroupScheme.Dynamic.CommutingRefinements
import Langlands.GroupScheme.Dynamic.OppositeCellContraction

/-!
# Cancellation of the two original epsilon corrections

For the actual standard rational-point families, the original source and
target epsilon corrections of the geometric lemma are reciprocal on the whole
literal common Levi `M_I ∩ n M_J n⁻¹`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Two actual cocharacters of the original split torus realizing the
standard Levi and radical of `I` and the forward conjugates by `m` of the
standard Levi and radical of `J`. -/
structure GeometricCocharacterRealization
    (I J : Finset (SimpleRoot i ν)) (m : rationalPoints G) where
  zeta : cocharacterLattice T
  eta : cocharacterLattice T
  levi_left : standardLevi i ν (rootSet i ν I) =
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)
  unipotent_left : standardUnipotent i ν (rootSet i ν I) =
    Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)
  levi_right : (standardLevi i ν (rootSet i ν J)).comap (G.innerIso m).inv =
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)
  unipotent_right :
    (standardUnipotent i ν (rootSet i ν J)).comap (G.innerIso m).inv =
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)

/-- The standard-cocharacter statement and the actual normalizer comparison
supply such a realization at every actual normalizer point. -/
def geometricCocharacterRealization
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I J : Finset (SimpleRoot i ν))
    (m : Group.RelativeWeyl.normalizer (torusPoints i)) :
    GeometricCocharacterRealization i ν I J m := by
  have := hG.smooth
  have := hG.isSeparated
  have hI := hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  let zeta := Classical.choose hI.1
  obtain ⟨-, hMI, hUI⟩ := hI.2 zeta (Classical.choose_spec hI.1)
  have hJ := hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)
  let xi := Classical.choose hJ.1
  obtain ⟨-, hMJ, hUJ⟩ := hJ.2 xi (Classical.choose_spec hJ.1)
  let n : normalizerPoints i := (normalizerEquiv i hN).symm m
  have hm : (n : rationalPoints G) = m :=
    congrArg (fun q : Group.RelativeWeyl.normalizer (torusPoints i) =>
      (q : rationalPoints G)) ((normalizerEquiv i hN).apply_symm_apply m)
  let eta := cocharacterAut (normalizingAut i n) xi
  have he : CommGroupScheme.groupHom eta ≫ i =
      (CommGroupScheme.groupHom xi ≫ i) ≫
        (G.innerIso (m : rationalPoints G)).hom := by
    rw [groupHom_cocharacterAut_comp, hm]
  have hM :
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) =
        (Dynamic.centralizer (CommGroupScheme.groupHom xi ≫ i)).comap
          (G.innerIso (m : rationalPoints G)).inv := by
    rw [he]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using Dynamic.centralizer_eq_comap_of_iso
        ((CommGroupScheme.groupHom xi ≫ i) ≫
          (G.innerIso (m : rationalPoints G)).hom)
        (G.innerIso (m : rationalPoints G)).symm
  have hU :
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) =
        (Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).comap
          (G.innerIso (m : rationalPoints G)).inv := by
    rw [he]
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using Dynamic.unipotent_eq_comap_of_iso
        ((CommGroupScheme.groupHom xi ≫ i) ≫
          (G.innerIso (m : rationalPoints G)).hom)
        (G.innerIso (m : rationalPoints G)).symm
  refine ⟨zeta, eta, hMI, hUI, ?_, ?_⟩
  · rw [hMJ]
    exact hM.symm
  · rw [hUJ]
    exact hU.symm

namespace GeometricCocharacterRealization

variable {i ν} {I J : Finset (SimpleRoot i ν)} {m : rationalPoints G}
    (r : GeometricCocharacterRealization i ν I J m)

local notation "χ" => CommGroupScheme.groupHom r.zeta ≫ i
local notation "τ" => CommGroupScheme.groupHom r.eta ≫ i

theorem levi_left_points :
    (Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints =
      levi i ν I := by
  rw [← r.levi_left]

theorem unipotent_left_points :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints =
      unipotent i ν I := by
  rw [← r.unipotent_left]

omit [IsAffineHom G.X.hom] in
/-- Forward conjugation by `m` as a subgroup image is the preimage under
inverse conjugation. -/
theorem map_conj_eq_comap (H : Subgroup (rationalPoints G)) :
    H.map (MulAut.conj m).toMonoidHom = H.comap (MulAut.conj m⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]

theorem levi_right_points :
    (Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
      (levi i ν J).map (MulAut.conj m).toMonoidHom := by
  rw [map_conj_eq_comap, ← r.levi_right, SubgroupFunctor.rationalPoints_comap,
    rationalPoints_map_innerIso_inv]

theorem unipotent_right_points :
    (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
      (unipotent i ν J).map (MulAut.conj m).toMonoidHom := by
  rw [map_conj_eq_comap, ← r.unipotent_right, SubgroupFunctor.rationalPoints_comap,
    rationalPoints_map_innerIso_inv]

/-- The two cocharacters factor through the same commutative torus, so the
second has image in the centralizer of the first. -/
theorem range_eta_le :
    SubgroupFunctor.range (CommGroupScheme.groupHom r.eta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i) :=
  Dynamic.range_comp_le_centralizer_comp i _ _

variable [LocallyOfFiniteType G.X.hom]

/-- A dominant combination `N ζ + η` of the two cocharacters, computed in the
actual cocharacter lattice, has centralizer the intersection of the two
original centralizers. -/
theorem exists_common_centralizer_cocharacter :
    ∃ mu : cocharacterLattice T,
      Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i) =
        Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
          Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i) := by
  obtain ⟨N, hN⟩ := Dynamic.exists_dominant_inclusions _ _ r.range_eta_le
  refine ⟨(N : ℤ) • r.zeta + r.eta, ?_⟩
  have hform : ∀ (T' : Over (Spec (CommRingCat.of k)))
      (t : T' ⟶ (Gm (Spec (CommRingCat.of k))).X),
      t ≫ (CommGroupScheme.groupHom ((N : ℤ) • r.zeta + r.eta) ≫ i).hom.hom =
        ((t ^ (N : ℤ)) ≫ (CommGroupScheme.groupHom r.zeta ≫ i).hom.hom) *
          (t ≫ (CommGroupScheme.groupHom r.eta ≫ i).hom.hom) := by
    intro T' t
    simp only [Grp.comp_hom_hom]
    rw [← Category.assoc, comp_groupHom_add, comp_groupHom_zsmul, MonObj.mul_comp]
    simp only [GrpObj.zpow_comp, Category.assoc]
  obtain ⟨-, -, hZ⟩ := hN (N : ℤ) le_rfl _ hform
  have heq : CommGroupScheme.groupHom ((N : ℤ) • r.zeta + r.eta) ≫ i =
      Dynamic.cocharacterCombination _ _ r.range_eta_le (N : ℤ) := by
    apply Grp.hom_ext
    have h1 := hform _ (𝟙 _)
    rw [← Dynamic.comp_cocharacterCombination _ _ r.range_eta_le (N : ℤ) (𝟙 _),
      Category.id_comp, Category.id_comp] at h1
    exact h1
  rw [heq] at hZ ⊢
  exact Dynamic.centralizer_combination_eq_inf _ _ r.range_eta_le (N : ℤ) hZ

end GeometricCocharacterRealization

section Injectivity

local instance geometricEpsilonBalanceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- For every cocharacter of the maximal split torus, restriction of rational
characters from the represented centralizer to the torus factor is injective. -/
theorem characterRestrict_torusFactor_injective
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (mu : cocharacterLattice T) :
    Function.Injective (characterRestrict (Dynamic.torusFactor i (CommGroupScheme.groupHom mu)
      (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom mu ≫ i)))) := by
  obtain ⟨hM, hA⟩ := leviSplitComponentStatement k G hG T i hi mu _
    (Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom mu ≫ i))
    (Dynamic.Affine.isClosedSubgroup_centralizerHom _)
    (Dynamic.Affine.isRepresentedBy_centralizerHom _)
  obtain ⟨⟨A_G, iG, hiG⟩, -⟩ := splitComponentStatement k G hG
  obtain ⟨A_M, iM, -, g, hiM, -, hg, -⟩ := hA A_G iG hiG
  have hinj := characterRestrict_injective_of_centralSplitTorusCharacter
    centralSplitTorusCharacter hM hiM
  have hmono := (Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom mu ≫ i)).mono
  have hgj : g ≫ Dynamic.torusFactor i (CommGroupScheme.groupHom mu)
      (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom mu ≫ i)) =
        iM := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (Dynamic.Affine.centralizerHom
      (CommGroupScheme.groupHom mu ≫ i)).hom.hom.left).mp
    have hc : g ≫ Dynamic.torusFactor i (CommGroupScheme.groupHom mu)
        (Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom mu ≫ i)) ≫
          Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom mu ≫ i) =
        iM ≫ Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom mu ≫ i) := by
      rw [Dynamic.torusFactor_comp, hg]
    exact congrArg (fun z : A_M.toGrp ⟶ G => z.hom.hom.left) hc
  intro a b hab
  apply hinj
  rw [← hgj, characterRestrict_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hab]

end Injectivity

section Algebra

/-- Pointwise agreement of five moduli along any map gives agreement of the two
factorized correction products. -/
theorem correctionProduct_apply_eq {H H' : Type*} [Group H] [Group H'] (e : H' → H)
    (u v a b c c₂ : H →* ℝ≥0ˣ) (u' v' a' b' c' : H' →* ℝ≥0ˣ)
    (hu : ∀ z, u (e z) = u' z) (hv : ∀ z, v (e z) = v' z) (ha : ∀ z, a (e z) = a' z)
    (hb : ∀ z, b (e z) = b' z) (hc : ∀ z, c (e z) = c' z) (hc₂ : ∀ z, c₂ (e z) = c' z)
    (z : H') :
    ((Jacquet.complexCharacter (Jacquet.positiveHalfCharacter v) *
        Jacquet.inverseHalfCharacter b * Jacquet.inverseHalfCharacter c) *
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter u) *
        Jacquet.inverseHalfCharacter a * Jacquet.inverseHalfCharacter c₂)) (e z) =
    ((Jacquet.complexCharacter (Jacquet.positiveHalfCharacter v') *
        Jacquet.inverseHalfCharacter b' * Jacquet.inverseHalfCharacter c') *
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter u') *
        Jacquet.inverseHalfCharacter a' * Jacquet.inverseHalfCharacter c')) z := by
  simp only [MonoidHom.mul_apply, Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, MonoidHom.inv_apply,
    hu, hv, ha, hb, hc, hc₂]

theorem closedNormalizerCharacter_congr'
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {U V : Subgroup H}
    (hUV : U = V) (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (x : Subgroup.normalizer (U : Set H)) (y : Subgroup.normalizer (V : Set H))
    (hxy : (x : H) = y) :
    HaarModulus.closedNormalizerCharacter U hU x =
      HaarModulus.closedNormalizerCharacter V hV y := by
  subst V
  congr 1
  exact Subtype.ext hxy

end Algebra

section Balance

open Langlands.AlgebraicGeometry.PointTopology

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Mono i.hom.hom.left]

local instance geometricEpsilonBalancePointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

local instance geometricEpsilonBalanceAffine' : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

/-- **Epsilon cancellation.** For the actual standard rational-point families,
the original source and target epsilon corrections of the geometric lemma are
reciprocal on the whole literal common Levi `M_I ∩ n M_J n⁻¹`. -/
theorem geometricEpsilon_mul_eq_one
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (hroot : HasRelativeRootSystem i)
    (I J : Finset (SimpleRoot i ν))
    (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hU : ∀ H, IsClosed (unipotent i ν H : Set (RationalPoint k G.X)))
    (hP : ∀ H, IsClosed (parabolic i ν H : Set (RationalPoint k G.X)))
    (hM : ∀ H, IsClosed (levi i ν H : Set (RationalPoint k G.X)))
    (hpI : Continuous dI.projection) (hpJ : Continuous dJ.projection) :
    geometricEpsilonOne i ν I J dI dJ n (hU J) (hP I) *
      geometricEpsilonTwo i ν I J dI dJ n (hU I) (hP J) = 1 := by
  have := hG.smooth
  have : SecondCountableTopology (RationalPoint k G.X) :=
    reductiveRationalPoint_secondCountable k G hG
  rw [geometricEpsilonOne_eq_factorized_half i ν hStandard hG hi hν hN I J dI dJ n
      (hP I) (hM I) (hU I) (hU J) hpI,
    geometricEpsilonTwo_eq_factorized_half i ν hStandard hG hi hν hN I J n dJ dI
      (hU I) (hP J) (hM J) (hU J) hpJ]
  let r := geometricCocharacterRealization i ν hStandard hG hi hν hN I J n
  obtain ⟨mu, hmu⟩ := r.exists_common_centralizer_cocharacter
  -- the acting group: the represented common centralizer
  have hZrep := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom mu ≫ i)
  have hZcl := Dynamic.Affine.isClosedSubgroup_centralizerHom (CommGroupScheme.groupHom mu ≫ i)
  have : IsAffineHom (Dynamic.Affine.centralizerScheme
      (CommGroupScheme.groupHom mu ≫ i)).X.hom := hZcl.isAffineHom
  have : IsAffine (Dynamic.Affine.centralizerScheme
      (CommGroupScheme.groupHom mu ≫ i)).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerScheme
      (CommGroupScheme.groupHom mu ≫ i)).X.hom
  have hZ : SubgroupFunctor.range (Dynamic.Affine.centralizerHom
      (CommGroupScheme.groupHom mu ≫ i)) ≤
        Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i) := by
    rw [hZrep.2, hmu]
    exact fun X => inf_le_left
  have hZ' : SubgroupFunctor.range (Dynamic.Affine.centralizerHom
      (CommGroupScheme.groupHom mu ≫ i)) ≤
        Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i) := by
    rw [hZrep.2, hmu]
    exact fun X => inf_le_right
  -- the five represented models
  have hUrep := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom r.zeta ≫ i)
  have hUcl := Dynamic.Affine.isClosedSubgroup_unipotentHom (CommGroupScheme.groupHom r.zeta ≫ i)
  have hVrep := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom r.eta ≫ i)
  have hVcl := Dynamic.Affine.isClosedSubgroup_unipotentHom (CommGroupScheme.groupHom r.eta ≫ i)
  have hMzrep := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom r.zeta ≫ i)
  have hMzcl := Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom r.zeta ≫ i)
  have hMerep := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom r.eta ≫ i)
  have hMecl := Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom r.eta ≫ i)
  have hArep := isRepresentedBy_subgroupIntersectionHom hUcl hMecl
  rw [hUrep.2, hMerep.2] at hArep
  have hAcl := isClosedSubgroup_subgroupIntersectionHom hUcl hMecl
  have hBrep := isRepresentedBy_subgroupIntersectionHom hVcl hMzcl
  rw [hVrep.2, hMzrep.2] at hBrep
  have hBcl := isClosedSubgroup_subgroupIntersectionHom hVcl hMzcl
  have hCrep := isRepresentedBy_subgroupIntersectionHom hUcl hVcl
  rw [hUrep.2, hVrep.2] at hCrep
  have hCcl := isClosedSubgroup_subgroupIntersectionHom hUcl hVcl
  have := hUcl.isAffineHom
  have := hVcl.isAffineHom
  have := hAcl.isAffineHom
  have := hBcl.isAffineHom
  have := hCcl.isAffineHom
  have := hUcl.locallyOfFiniteType
  have := hVcl.locallyOfFiniteType
  have := hAcl.locallyOfFiniteType
  have := hBcl.locallyOfFiniteType
  have := hCcl.locallyOfFiniteType
  -- rational points of the five models and of the acting group
  have hUpts : (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints =
      unipotent i ν I := r.unipotent_left_points
  have hVpts : (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
      (unipotent i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom :=
    r.unipotent_right_points
  have hApts : (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
        geometricTargetIntersection (unipotent i ν I) (levi i ν J) (n : RationalPoint k G.X) := by
    change (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints ⊓
      (Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints = _
    rw [r.unipotent_left_points, r.levi_right_points]
    rfl
  have hBpts : (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints =
        geometricTargetIntersection (levi i ν I) (unipotent i ν J) (n : RationalPoint k G.X) := by
    change (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints ⊓
      (Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints = _
    rw [r.unipotent_right_points, r.levi_left_points, inf_comm]
    rfl
  have hCpts : (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints =
        geometricTargetIntersection (unipotent i ν I) (unipotent i ν J)
          (n : RationalPoint k G.X) := by
    change (Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints ⊓
      (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints = _
    rw [r.unipotent_left_points, r.unipotent_right_points]
    rfl
  have hLpts : (Dynamic.centralizer (CommGroupScheme.groupHom mu ≫ i)).rationalPoints =
      geometricTargetIntersection (levi i ν I) (levi i ν J) (n : RationalPoint k G.X) := by
    rw [hmu]
    change (Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints ⊓
      (Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints = _
    rw [r.levi_left_points, r.levi_right_points]
    rfl
  -- closedness of the five literal point subgroups
  have hUc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).carrier
      (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)) := by
    change IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints :
      Set (RationalPoint k G.X))
    rw [hUpts]
    exact hU I
  have hVc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).carrier
      (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)) := by
    change IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints :
      Set (RationalPoint k G.X))
    rw [hVpts]
    exact isClosed_map_conj _ (hU J) _
  have hAc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i)).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)) := by
    change IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints :
        Set (RationalPoint k G.X))
    rw [hApts]
    exact isClosed_geometricTargetIntersection _ _ (hU I) (hM J) _
  have hBc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)) := by
    change IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i) ⊓
      Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints :
        Set (RationalPoint k G.X))
    rw [hBpts]
    exact isClosed_geometricTargetIntersection _ _ (hM I) (hU J) _
  have hCc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).carrier
        (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)) := by
    change IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints :
        Set (RationalPoint k G.X))
    rw [hCpts]
    exact isClosed_geometricTargetIntersection _ _ (hU I) (hU J) _
  -- the generic five-factor balance on the acting group
  have key := centralizingHaarCharacter_correctionProduct_eq_one_of_characterRestrict_injective
    hroot hi.isSplitSubtorus.1 r.zeta r.eta
    (Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom mu ≫ i)) hZ hZ'
    hUrep hVrep hArep hBrep hCrep
    (Dynamic.torusFactor i (CommGroupScheme.groupHom mu) hZrep)
    (Dynamic.torusFactor_comp i (CommGroupScheme.groupHom mu) hZrep)
    (Lie.finiteCoordinates _) (Lie.finiteCoordinates _) (Lie.finiteCoordinates _)
    (Lie.finiteCoordinates _) (Lie.finiteCoordinates _)
    hUc hVc hAc hBc hCc (characterRestrict_torusFactor_injective i hG hi mu)
  -- transport from the acting group to the literal common Levi
  let e : rationalPoints (Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom mu ≫ i)) ≃*
      Subgroup.subgroupOf (geometricTargetIntersection (levi i ν I) (levi i ν J)
        (n : RationalPoint k G.X)) (levi i ν I) :=
    (hZrep.pointsEquiv (Over.mk (𝟙 _))).trans ((MulEquiv.subgroupCongr hLpts).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm)
  apply MonoidHom.ext
  intro lt
  obtain ⟨z, rfl⟩ := e.surjective lt
  have hk := DFunLike.congr_fun key z
  refine Eq.trans ?_ (hk.trans (by simp))
  refine correctionProduct_apply_eq (⇑e) _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ z
  · intro z
    exact closedNormalizerCharacter_congr' hUpts.symm (hU I) hUc _ _ rfl
  · intro z
    exact closedNormalizerCharacter_congr' hVpts.symm (isClosed_map_conj _ (hU J) _) hVc _ _ rfl
  · intro z
    exact closedNormalizerCharacter_congr' hApts.symm
      (isClosed_geometricTargetIntersection _ _ (hU I) (hM J) _) hAc _ _ rfl
  · intro z
    exact closedNormalizerCharacter_congr' hBpts.symm
      (isClosed_geometricTargetIntersection _ _ (hM I) (hU J) _) hBc _ _ rfl
  · intro z
    exact closedNormalizerCharacter_congr' hCpts.symm
      (isClosed_geometricTargetIntersection _ _ (hU I) (hU J) _) hCc _ _ rfl
  · intro z
    exact closedNormalizerCharacter_congr' hCpts.symm
      (isClosed_geometricTargetIntersection _ _ (hU I) (hU J) _) hCc _ _ rfl

end Balance

end Langlands.Aubert.General.RationalPointFamily
