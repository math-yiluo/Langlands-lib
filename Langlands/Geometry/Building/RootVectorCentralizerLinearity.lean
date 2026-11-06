import Langlands.GroupScheme.Rational.VectorActionWeightCommuting
import Langlands.GroupScheme.Rational.VectorLinearizationSupport
import Langlands.GroupScheme.Rational.RootSubgroupCentralizerAction
import Langlands.Geometry.Building.RootVectorCoordinatesOfNoHigherRoots

/-! # Linear torus-centralizer action on actual root vector coordinates

For a relative root `a` without higher positive integral multiples, the represented root
subgroup has actual vector coordinates on which the split torus acts through `a`. Any group
centralizing the torus acts on the root subgroup by actual conjugation, and this action is
scalar linear in those coordinates over every test scheme, in every characteristic.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G K : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual vector coordinates on a represented root subgroup, with the split torus acting through
the root character and a group `K → G` centralizing the torus acting linearly by conjugation. -/
structure CentralizerLinearRootVectorCoordinates (i : S.toGrp ⟶ G) (a : characterLattice S)
    (z : K ⟶ G) where
  rootGroup : GroupScheme (Spec (CommRingCat.of k))
  inclusion : rootGroup ⟶ G
  represented : (RelativeRoot.subgroup i a).IsRepresentedBy inclusion
  dimension : ℕ
  dimension_pos : 0 < dimension
  coordinates : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ rootGroup.X) ≃* Multiplicative (Fin dimension → Γ(T.left, ⊤))
  torusAction : AutomorphicAction S.toGrp rootGroup
  torusAction_comp : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
    (v : T ⟶ rootGroup.X), torusAction.act s v ≫ inclusion.hom.hom =
      (s ≫ i.hom.hom) * (v ≫ inclusion.hom.hom) * (s ≫ i.hom.hom)⁻¹
  weight : RelativeRoot.IsWeightVectorCoordinates torusAction a coordinates
  centralizerAction : AutomorphicAction K rootGroup
  centralizerAction_comp : ∀ (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ K.X)
    (v : T ⟶ rootGroup.X), centralizerAction.act q v ≫ inclusion.hom.hom =
      (q ≫ z.hom.hom) * (v ≫ inclusion.hom.hom) * (q ≫ z.hom.hom)⁻¹
  linear : RelativeRoot.IsLinearVectorCoordinates centralizerAction coordinates

/-- **Linear centralizer action on root vector coordinates.** For a relative root with no higher
positive integral multiple and an affine group mapping into the torus centralizer, the represented
root subgroup has actual vector coordinates of weight `a` in which the conjugation action is
linear, in every characteristic. -/
theorem nonempty_centralizerLinearRootVectorCoordinates_of_noHigherRoots
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom K.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hhigh : RelativeRoot.HasNoHigherRoots i a) (z : K ⟶ G)
    (hz : SubgroupFunctor.range z ≤ torusCentralizer i) :
    Nonempty (CentralizerLinearRootVectorCoordinates i a z) := by
  obtain ⟨H, j, hj, _⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hS i a ha.1
  let b := AutomorphicAction.conjugation i
  have hfirst : RelativeRoot.weightFiltration b a 1 = RelativeRoot.subgroup i a :=
    RelativeRoot.cyclicRootFunctorComparison k G inferInstance inferInstance S hS i a ha.1
  have htwo : RelativeRoot.weightFiltration b a 2 = ⊥ :=
    RelativeRoot.weightFiltration_two_eq_bot_of_noHigherRoots inferInstance hS i ha.1 hhigh
  have hrep : (RelativeRoot.weightFiltration b a 1).IsRepresentedBy j := hfirst.symm ▸ hj
  obtain ⟨V, q, c, d, hq, hc, hdj, hqd⟩ :=
    (RelativeRoot.cyclicWeightFiltration k G inferInstance inferInstance S hS b a ha.1 1
      (by decide)).2 H j hrep
  let : Mono j.hom.hom := hj.1
  have hq0 : RelativeRoot.IsFppfQuotient ⊥ q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
      SubgroupFunctor.comap_bot_of_mono] using hq
  let Q : H ≅ V := hq0.isoOfBot
  obtain ⟨n, ec, hec⟩ := hc.1
  have hweight : RelativeRoot.IsWeightVectorCoordinates c a ec := by
    simpa only [one_smul] using hec
  let e := RelativeRoot.vectorCoordinatesOfIso Q.symm ec
  have he : RelativeRoot.IsWeightVectorCoordinates d a e := by
    refine ⟨RelativeRoot.IsNaturalVectorCoordinates.of_iso hweight.1 Q.symm, ?_⟩
    intro T s v
    change (ec T (d.act s v ≫ q.hom.hom)).toAdd = _ • (ec T (v ≫ q.hom.hom)).toAdd
    rw [← hqd, hweight.2]
  have hdj' (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (v : T ⟶ H.X) :
      d.act s v ≫ j.hom.hom = (s ≫ i.hom.hom) * (v ≫ j.hom.hom) * (s ≫ i.hom.hom)⁻¹ := by
    rw [hdj]
    exact AutomorphicAction.conjugation_act i s _
  have hcZ : SubgroupFunctor.range z ≤
      (AutomorphicAction.conjugation (i ≫ 𝟙 G)).fixedSubgroup := by
    rw [Category.comp_id, AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
    exact hz
  let bZ := RelativeRoot.rootActionOfTorusCentralizer (𝟙 G) z
    (AutomorphicAction.range_id_isNormalizedBy z) i hcZ a j hj
  have hbZ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ K.X) (v : T ⟶ H.X) :
      bZ.act y v ≫ j.hom.hom = (y ≫ z.hom.hom) * (v ≫ j.hom.hom) * (y ≫ z.hom.hom)⁻¹ := by
    simpa only [Category.comp_id] using
      RelativeRoot.rootActionOfTorusCentralizer_act_comp (𝟙 G) z
        (AutomorphicAction.range_id_isNormalizedBy z) i hcZ a j hj y v
  have hcomm (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ K.X) (s : T ⟶ S.X) :
      Commute (y ≫ z.hom.hom) (s ≫ i.hom.hom) := by
    have hm : y ≫ z.hom.hom ∈ (torusCentralizer i).carrier T :=
      hz T (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    simpa only [Category.id_comp] using hm T (𝟙 T) s
  have hbd : ∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ K.X) (s : T ⟶ S.X)
      (v : T ⟶ H.X), bZ.act y (d.act s v) = d.act s (bZ.act y v) := by
    intro T y s v
    apply (cancel_mono j.hom.hom).1
    rw [hbZ, hdj', hdj', hbZ]
    have h1 : (y ≫ z.hom.hom) * ((s ≫ i.hom.hom) * (v ≫ j.hom.hom) * (s ≫ i.hom.hom)⁻¹) *
          (y ≫ z.hom.hom)⁻¹ =
        ((y ≫ z.hom.hom) * (s ≫ i.hom.hom)) * (v ≫ j.hom.hom) *
          ((y ≫ z.hom.hom) * (s ≫ i.hom.hom))⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    have h2 : (s ≫ i.hom.hom) * ((y ≫ z.hom.hom) * (v ≫ j.hom.hom) * (y ≫ z.hom.hom)⁻¹) *
          (s ≫ i.hom.hom)⁻¹ =
        ((s ≫ i.hom.hom) * (y ≫ z.hom.hom)) * (v ≫ j.hom.hom) *
          ((s ≫ i.hom.hom) * (y ≫ z.hom.hom))⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [h1, h2, (hcomm T y s).eq]
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    obtain ⟨g, hg, hg1⟩ := RelativeRoot.exists_rootPoint_of_noHigherRoots hS i ha hhigh
    let T : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
    have hv : (hj.pointsEquiv T).symm ⟨g, hg⟩ = 1 := by
      apply (e T).injective
      apply Multiplicative.toAdd.injective
      funext l
      exact Fin.elim0 (hn0 ▸ l)
    apply hg1
    have hv' := congrArg (fun v => ((hj.pointsEquiv T v : (RelativeRoot.subgroup i a).carrier T) :
      T ⟶ G.X)) hv
    simpa only [MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one] using hv'
  exact ⟨{
    rootGroup := H
    inclusion := j
    represented := hj
    dimension := n
    dimension_pos := hn
    coordinates := e
    torusAction := d
    torusAction_comp := hdj'
    weight := he
    centralizerAction := bZ
    centralizerAction_comp := hbZ
    linear := RelativeRoot.isLinearVectorCoordinates_of_commute hS ha.1 he hbd }⟩

end Langlands.Geometry.Building
