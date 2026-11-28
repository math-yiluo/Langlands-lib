import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Rational.TypeD5ClosedSubgroupRank
import Langlands.GroupScheme.Rational.TypeE6MarkedParabolicDimensions
import Langlands.LinearAlgebra.CartanE6ComplementaryTypeA2

/-! # The E₆ Levi omitting the short-arm endpoint and the center -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.CartanE6Root Langlands.RootReflectionCoefficients
open scoped BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private local instance finiteTypeBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹LocallyOfFiniteType G.X.hom›

private theorem count_signed_zero_roots :
    Fintype.card {r : Bool × Fin 36 // signedCoefficients r 1 + signedCoefficients r 3 = 0} = 12 := by
  decide

private theorem SplitPinning.card_zero_roots_shortArmAndCenter
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (p : SplitPinning G) (e : p.base.support ≃ Fin 6)
    (hE : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b))
    (ν : cocharacterLattice p.torus) (m : ℤ) (hm : 0 < m)
    (hν : ∀ a : p.base.support, p.rootDatum.root' a.val ν = if e a ∈ shortArmAndCenter then m else 0) :
    Nat.card {r : p.rootIndex // p.rootDatum.root' r ν = 0} = 12 := by
  classical
  let P := p.rootDatum
  let a (i : Fin 6) : p.rootIndex := (e.symm i).val
  let : P.IsReduced := p.isReduced
  have hcart (i j : Fin 6) : P.pairing (a i) (a j) = CartanMatrix.E 6 i j := by
    simpa only [a, e.apply_symm_apply] using hE (e.symm i) (e.symm j)
  have hvals (i : Fin 6) : P.root' (a i) ν = if i ∈ shortArmAndCenter then m else 0 := by
    simpa only [a, e.apply_symm_apply] using hν (e.symm i)
  obtain ⟨f, hf⟩ := exists_signedRootEquiv P p.base e hcart
  have hz (r : Bool × Fin 36) :
      P.root' (f r) ν = 0 ↔ signedCoefficients r 1 + signedCoefficients r 3 = 0 := by
    change P.toLinearMap (P.root (f r)) ν = 0 ↔ _
    rw [hf]
    have h : P.toLinearMap (combination P a (signedCoefficients r)) ν =
        (signedCoefficients r 1 + signedCoefficients r 3) * m := by
      simp only [combination, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      change (∑ i, signedCoefficients r i * P.root' (a i) ν) = _
      rw [Fin.sum_univ_six]
      simp only [hvals]
      norm_num [shortArmAndCenter, add_mul]
    rw [h, mul_eq_zero]
    exact or_iff_left hm.ne'
  rw [← Nat.card_congr (f.subtypeEquiv fun r => (hz r).symm),
    Nat.card_eq_fintype_card]
  exact count_signed_zero_roots

private theorem SplitPinning.dimension_centralizer_shortArmAndCenter
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (p : SplitPinning G) (hsc : IsSimplyConnected G) (e : p.base.support ≃ Fin 6)
    (hE : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b))
    (ν : cocharacterLattice p.torus) (m : ℤ) (hm : 0 < m)
    (hν : ∀ a : p.base.support, p.rootDatum.root' a.val ν = if e a ∈ shortArmAndCenter then m else 0) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
    haveI := (Dynamic.Affine.isClosedSubgroup_centralizerHom χ).isAffineHom
    Lie.dimension (Dynamic.Affine.centralizerScheme χ) = 18 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ p.inclusion
  let M := Dynamic.Affine.centralizerScheme χ
  let j := Dynamic.Affine.centralizerHom χ
  let hj := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let hc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  let : IsAffineHom M.X.hom := hc.isAffineHom
  let : LocallyOfFiniteType M.X.hom := hc.locallyOfFiniteType
  let hM := dynamicCentralizerReductive k G p.isConnectedReductive χ M j hc hj
  have hT : SubgroupFunctor.range p.inclusion ≤ Dynamic.centralizer χ :=
    (range_le_torusCentralizer p.inclusion).trans (torusCentralizer_le_dynamicCentralizer p.inclusion _)
  let t := hj.liftOfLE p.inclusion hT
  have ht : t ≫ j = p.inclusion := hj.liftOfLE_comp _ _
  have htmax : IsMaximalTorus t := IsMaximalTorus.of_comp hc (ht.symm ▸ p.isMaximalTorus)
  obtain ⟨K, hK, Q, hQ, _⟩ := rootDatumExistence k M hM p.torus p.isSplitTorus t htmax
  let : Finite K := hK
  have hroots := relativeRoots_centralizer_factor dynamicLie p.inclusion t j ht ν hj
  have hQroots : Set.range Q.root =
      Set.range (fun r : {r : p.rootIndex // p.rootDatum.root' r ν = 0} => p.rootDatum.root r.val) := by
    rw [hQ.2.1, ← relativeRoots_eq_roots, hroots, relativeRoots_eq_roots, ← p.isRootDatum.2.1]
    ext α
    constructor
    · rintro ⟨⟨r, rfl⟩, hr⟩
      exact ⟨⟨r, by rw [← p.isRootDatum.1] at hr; exact hr⟩, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨⟨r.val, rfl⟩, by rw [← p.isRootDatum.1]; exact r.property⟩
  let f := (Equiv.ofInjective Q.root Q.root.injective).trans
    ((Set.equivOfEq hQroots).trans
      (Equiv.ofInjective _ (fun _ _ h => Subtype.ext (p.rootDatum.root.injective h))).symm)
  have hcard : Nat.card K = 12 :=
    (Nat.card_congr f).trans (p.card_zero_roots_shortArmAndCenter e hE ν m hm hν)
  let : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
  have hdimT : Lie.dimension p.torus.toGrp = 6 := by
    rw [p.torusDimension_eq_card_base_of_isSimplyConnected hsc, Nat.card_congr e, Nat.card_fin]
  change Lie.dimension M = 18
  refine (hQ.finrank_lie_eq_torus_add_card hM p.isSplitTorus htmax).trans ?_
  change Lie.dimension p.torus.toGrp + Nat.card K = 18
  rw [hdimT, hcard]

/-- The marked short-arm endpoint and center give a rational parabolic
of dimension 48 with dynamic Levi of dimension 18. -/
def TypeE6ShortArmCenterLeviDimensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 6), IsSimplyConnected G →
    (∀ a c, d.cartan a c = CartanMatrix.E 6 (e a) (e c)) →
    (∀ a : d.Vertex, e a ∈ shortArmAndCenter → a ∈ d.distinguishedVertices) →
    (∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex),
      e (d.star σ a) ∈ shortArmAndCenter ↔ e a ∈ shortArmAndCenter) →
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    Lie.dimension G = 78 ∧
    ∃ (m : ℤ) (ν : cocharacterLattice d.splitTorus), 0 < m ∧
      (∀ a : d.Vertex, d.pinning.rootDatum.root' a.val
        (cocharacterLattice.baseChange (algebraBaseMap k (SeparableClosure k)) _ (ν ≫ d.torusMap)) =
          if e a ∈ shortArmAndCenter then m else 0) ∧
      let χ := CommGroupScheme.groupHom ν ≫ d.splitInclusion
      haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
      haveI := (Dynamic.Affine.isClosedSubgroup_centralizerHom χ).isAffineHom
      IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ) ∧
        Lie.dimension (Dynamic.Affine.parabolicScheme χ) = 48 ∧
        Lie.dimension (Dynamic.Affine.centralizerScheme χ) = 18

theorem typeE6ShortArmCenterLeviDimension : TypeE6ShortArmCenterLeviDimensionStatement.{u} := by
  intro k _ G _ _ d e hsc hE hmark hstar
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hG, m, ν, hm, hν, hP, hPdim⟩ :=
    typeE6MarkedParabolicDimensions k G d e hsc hE shortArmAndCenter hmark hstar
  have hcount : parabolicCodimension shortArmAndCenter = 30 := parabolicCodimensionCounts.2.2.2
  refine ⟨hG, m, ν, hm, hν, hP, ?_, ?_⟩
  · rw [hcount] at hPdim
    omega
  · let E := SeparableClosure k
    let b := algebraBaseMap k E
    let B := GroupScheme.baseChange b
    let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
    let p := d.pinning.toSplitPinning
    let νE := cocharacterLattice.baseChange b d.pinning.torus (ν ≫ d.torusMap)
    let χ := CommGroupScheme.groupHom ν ≫ d.splitInclusion
    let χE := CommGroupScheme.groupHom νE ≫ p.inclusion
    have hχ : Dynamic.baseChangeCocharacter b χ = χE := by
      have hc : CommGroupScheme.groupHom (ν ≫ d.torusMap) ≫ d.pinning.inclusion = χ := by
        change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom d.torusMap) ≫
          d.pinning.inclusion = _
        rw [Category.assoc, d.square]
      rw [← hc, Dynamic.baseChangeCocharacter_comp_hom]
      rfl
    let M := Dynamic.Affine.centralizerScheme χ
    let hc := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
    let : IsAffineHom M.X.hom := hc.isAffineHom
    let : LocallyOfFiniteType M.X.hom := hc.locallyOfFiniteType
    let : IsAffineHom (Dynamic.Affine.centralizerScheme χE).X.hom :=
      (Dynamic.Affine.isClosedSubgroup_centralizerHom χE).isAffineHom
    have hME : (Dynamic.centralizer χE).IsRepresentedBy
        (B.map (Dynamic.Affine.centralizerHom χ)) := by
      rw [← hχ, Dynamic.centralizer_baseChange]
      exact (Dynamic.Affine.isRepresentedBy_centralizerHom χ).baseChange b
    let a := hME.isoOfIsRepresentedBy (Dynamic.Affine.isRepresentedBy_centralizerHom χE)
    exact (Lie.dimension_fieldExtension (L := E) M).symm.trans
      ((Lie.dimension_eq_of_iso a).trans
        (p.dimension_centralizer_shortArmAndCenter
          (isSimplyConnectedFieldExtension k E G hsc) e hE νE m hm hν))

end Langlands.GroupScheme
