import Langlands.GroupScheme.Rational.NegativeRootPartner
import Langlands.Algebra.RankOneRelationWeyl
import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct

/-! # Opposite factor pairs of linked root parametrizations of arbitrary roots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LinkedRootParametrization

open LocalSplitCell RankOneRootCellRelation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {r : p.rootIndex}
  (X : LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r))

local instance linkedRootOppositePairsMono : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

theorem pairing_root_coroot' :
    latticePairing p.torus (p.rootDatum.root r) (p.rootDatum.coroot r) = 2 := by
  rw [← p.isRootDatum.1]
  exact p.rootDatum.root_coroot_two r

/-- The rank-one data of a linked parametrization of a root of a pinning. -/
def pinnedData : Langlands.Algebra.RankOneRelation.Data k (rationalPoints G) :=
  X.rankOneData pairing_root_coroot'

theorem xpPoint_mem (c : k) :
    X.xpPoint c ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← X.positive_represents.2]
  exact ⟨_, rfl⟩

theorem xmPoint_mem (c : k) :
    X.xmPoint c ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← X.negative_represents.2]
  exact ⟨_, rfl⟩

theorem xpPoint_ne_one {c : k} (hc : c ≠ 0) : X.xpPoint c ≠ 1 := by
  intro h
  have : Mono X.positive.hom.hom := X.positive_represents.1
  have h0 : X.xpPoint 0 = 1 := (X.pinnedData).xp_zero
  rw [← h0] at h
  have h' := (cancel_mono X.positive.hom.hom).mp h
  have h'' := gpt_injective h'
  apply hc
  exact (secMap k).injective h''

/-- `(x₋(-1), x₋(-1))` is the opposite pair of `x₊(1)`. -/
theorem isOppositeFactorPair_xpPoint_one :
    RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r) (X.xpPoint 1)
      (X.xmPoint (-1), X.xmPoint (-1)) := by
  have e1 : rootPoint X.positive (𝟙_ (Over (Spec (CommRingCat.of k)))) 1 = X.xpPoint 1 := by
    rw [xpPoint, map_one]
    rfl
  have e2 : rootPoint X.negative (𝟙_ (Over (Spec (CommRingCat.of k)))) (-1) = X.xmPoint (-1) := by
    rw [xmPoint, map_neg, map_one]
    rfl
  have hx1 : rootPoint X.positive (𝟙_ (Over (Spec (CommRingCat.of k)))) 1 ≠ 1 := by
    rw [e1]
    exact X.xpPoint_ne_one one_ne_zero
  have h := isOppositeFactorPair_weylPoint p.isSplitTorus (p.root_mem_relativeRoots r).1
    X.positive_represents X.negative_represents X.negative_equivariant
    (X.relation _) (p.root_mem_relativeRoots r)
    (splitPinnedOppositeFactorPairs k G p) hx1
  rw [e1, e2] at h
  exact h

/-- The triple product `x₋(-c⁻¹) x₊(c) x₋(-c⁻¹)` is `r^∨(c)` times the triple product at `1`. -/
theorem triple_eq (c : kˣ) :
    X.xmPoint (-(c : k)⁻¹) * X.xpPoint c * X.xmPoint (-(c : k)⁻¹) =
      cocharacterPoint p.inclusion (p.rootDatum.coroot r) c *
        (X.xmPoint (-1) * X.xpPoint 1 * X.xmPoint (-1)) := by
  have h := (X.pinnedData).w_eq_h_mul_w_one c
  simp only [Langlands.Algebra.RankOneRelation.Data.w, inv_one] at h
  exact h

/-- `(x₋(-c⁻¹), x₋(-c⁻¹))` is the opposite pair of `x₊(c)` for every unit `c`. -/
theorem isOppositeFactorPair_xpPoint (c : kˣ) :
    RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r) (X.xpPoint c)
      (X.xmPoint (-(c : k)⁻¹), X.xmPoint (-(c : k)⁻¹)) := by
  refine ⟨X.xmPoint_mem _, X.xmPoint_mem _, ?_⟩
  change X.xmPoint (-(c : k)⁻¹) * X.xpPoint c * X.xmPoint (-(c : k)⁻¹) ∈ _
  rw [X.triple_eq c]
  exact (normalizerPoints p.inclusion).mul_mem
    (SplitPinning.NormalizedRootParametrization.cocharacterPoint_mem_normalizerPoints
      (p := p) _ c) X.isOppositeFactorPair_xpPoint_one.2.2

/-- Every rational point of the root subgroup is a value of `x₊`. -/
theorem exists_xpPoint_eq {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) : ∃ c : k, X.xpPoint c = g := by
  have hvr : (RelativeRoot.subgroup p.inclusion (-(-p.rootDatum.root r))).IsRepresentedBy
      X.positive := by
    rw [neg_neg]
    exact X.positive_represents
  obtain ⟨c, hc⟩ := LocalSplitCell.exists_rootPoint_eq (α := -p.rootDatum.root r) hvr
    (g := g) (by rw [neg_neg]; exact hg)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom c, ?_⟩
  rw [← hc, xpPoint]
  have hsec : secMap k ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom c) = c := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom c = c
    rw [Iso.hom_inv_id]
    rfl
  rw [hsec]
  rfl

/-- Every opposite pair of `x₊(c)` is `(x₋(-c⁻¹), x₋(-c⁻¹))`. -/
theorem eq_of_isOppositeFactorPair (c : kˣ) {q : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r) (X.xpPoint c) q) :
    q = (X.xmPoint (-(c : k)⁻¹), X.xmPoint (-(c : k)⁻¹)) :=
  hq.eq p.inclusion p.isSplitTorus (p.root_mem_relativeRoots r).1 (X.xpPoint_mem c)
    (X.xpPoint_ne_one c.ne_zero) (X.isOppositeFactorPair_xpPoint c)

/-- The product of an opposite pair around a nontrivial root point is `r^∨(c)` times the
triple product at `1`. -/
theorem exists_oppositeProduct_eq {y : rationalPoints G}
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (hy1 : y ≠ 1)
    {q : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r) y q) :
    ∃ c : kˣ, q.1 * y * q.2 = cocharacterPoint p.inclusion (p.rootDatum.coroot r) c *
      (X.xmPoint (-1) * X.xpPoint 1 * X.xmPoint (-1)) := by
  obtain ⟨c, rfl⟩ := X.exists_xpPoint_eq hy
  have hc : c ≠ 0 := by
    rintro rfl
    exact hy1 (X.pinnedData).xp_zero
  refine ⟨Units.mk0 c hc, ?_⟩
  have hq' := X.eq_of_isOppositeFactorPair (Units.mk0 c hc) hq
  rw [hq']
  exact X.triple_eq (Units.mk0 c hc)

end LinkedRootParametrization

namespace SplitPinning

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

/-- The product of two opposite-pair products around nontrivial points of the same root
subgroup lies in the image of the coroot. -/
theorem oppositeProduct_mul_mem_range (r : p.rootIndex) {y y' : rationalPoints G}
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (hy1 : y ≠ 1)
    (hy' : y' ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) (hy'1 : y' ≠ 1)
    {q q' : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r) y q)
    (hq' : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r) y' q') :
    q.1 * y * q.2 * (q'.1 * y' * q'.2) ∈
      (LinkedRootParametrization.cocharacterPoint p.inclusion (p.rootDatum.coroot r)).range := by
  let X := p.linkedRootParametrization r
  obtain ⟨c, hc⟩ := X.exists_oppositeProduct_eq hy hy1 hq
  obtain ⟨c', hc'⟩ := X.exists_oppositeProduct_eq hy' hy'1 hq'
  refine ⟨-(c * c'⁻¹), ?_⟩
  rw [hc, hc']
  have h := (X.pinnedData).h_mul_w_mul_h_mul_w c c'
  simp only [Langlands.Algebra.RankOneRelation.Data.w, inv_one] at h
  exact h.symm

namespace RootParametrization

open LocalSplitCell

variable {r : p.rootIndex} (x : p.RootParametrization r)

/-- A linked parametrization of the roots `±r` whose positive map is exactly `x`. -/
theorem exists_linked :
    ∃ X : LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r),
      X.positive = x.hom := by
  obtain ⟨X⟩ := p.nonempty_linkedRootParametrization r
  obtain ⟨l, hl0, hl⟩ := exists_eq_scaleHom_comp p.isSplitTorus (p.root_mem_relativeRoots r).1
    X.positive_represents x.represents X.positive_equivariant x.torus_equivariant
  set c : kˣ := Units.mk0 l hl0
  have hc : (c : k) = l := rfl
  refine ⟨{ positive := x.hom
            negative := scaleHom l ≫ X.negative
            positive_represents := x.represents
            negative_represents := ?_
            positive_equivariant := x.torus_equivariant
            negative_equivariant := ?_
            relation := ?_ }, rfl⟩
  · refine ⟨?_, ?_⟩
    · have : Mono X.negative.hom.hom := X.negative_represents.1
      rw [Grp.comp_hom_hom, ← hc]
      infer_instance
    · rw [← hc, show scaleHom (c : k) = (scaleIso c).hom from rfl,
        SubgroupFunctor.range_iso_comp]
      exact X.negative_represents.2
  · intro Z t e
    have h := X.negative_equivariant Z t (baseScalar Z l * e)
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_scaleHom, gaCoord,
      VectorGroup.coordinates_scalarPoint, ← Category.assoc, comp_scaleHom,
      gaCoord, VectorGroup.coordinates_scalarPoint, h, mul_left_comm]
  · intro Z
    have h := X.relation Z
    rw [hl] at h
    have h' : RootCell.RelationOver p.inclusion (p.rootDatum.coroot r)
        (scaleHom l ≫ x.hom) (scaleHom 1 ≫ X.negative) Z := by
      rwa [scaleHom_one, Category.id_comp]
    have h'' := relationOver_scaleHom hl0 h'
    rwa [mul_one] at h''

/-- The chosen linked parametrization with positive map `x`. -/
def linked : LinkedRootParametrization p.inclusion (p.rootDatum.root r) (p.rootDatum.coroot r) :=
  x.exists_linked.choose

theorem linked_positive : x.linked.positive = x.hom := x.exists_linked.choose_spec

theorem xpPoint_linked (c : k) : x.linked.xpPoint c = x.rationalPoint c := by
  rw [LinkedRootParametrization.xpPoint, x.linked_positive]
  rfl

/-- The ratio of the opposite-pair products around `x(c)` and `x(1)` is `r^∨(c)`. -/
theorem oppositeProduct_mul_inv (c : kˣ) {q q₁ : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r)
      (x.rationalPoint c) q)
    (hq₁ : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root r)
      (x.rationalPoint 1) q₁) :
    q.1 * x.rationalPoint c * q.2 * (q₁.1 * x.rationalPoint 1 * q₁.2)⁻¹ =
      LinkedRootParametrization.cocharacterPoint p.inclusion (p.rootDatum.coroot r) c := by
  rw [← x.xpPoint_linked] at hq hq₁ ⊢
  rw [← x.xpPoint_linked]
  have e1 : ((1 : kˣ) : k) = 1 := Units.val_one
  rw [← e1] at hq₁ ⊢
  rw [x.linked.eq_of_isOppositeFactorPair c hq, x.linked.eq_of_isOppositeFactorPair 1 hq₁]
  simp only
  rw [x.linked.triple_eq c, x.linked.triple_eq 1, map_one, one_mul]
  group

end RootParametrization

end SplitPinning

end Langlands.GroupScheme
