import Langlands.GroupScheme.Reductive.LinkedRootRationalRelation
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.GroupScheme.Reductive.PinnedRootFixedness
import Langlands.GroupScheme.Rational.SteinbergCanonicalGaloisTransport
import Langlands.GroupScheme.Rational.SteinbergRootRepresentatives

/-! # The negative partner of a normalized simple-root parametrization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning.NormalizedRootParametrization

open LocalSplitCell

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {a : p.base.support}
  (x : p.NormalizedRootParametrization a)

/-- The root of a simple index is nonzero. -/
theorem root_ne_zero' : p.rootDatum.root a ≠ 0 :=
  (p.root_mem_relativeRoots a).1

/-- A linked parametrization of the roots `±a` whose positive map is exactly `x`. -/
theorem exists_linked :
    ∃ X : LinkedRootParametrization p.inclusion (p.rootDatum.root a) (p.rootDatum.coroot a),
      X.positive = x.hom := by
  obtain ⟨X⟩ := p.nonempty_linkedRootParametrization a.val
  obtain ⟨l, hl0, hl⟩ := exists_eq_scaleHom_comp p.isSplitTorus (p.root_mem_relativeRoots a).1
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
    have h' : RootCell.RelationOver p.inclusion (p.rootDatum.coroot a)
        (scaleHom l ≫ x.hom) (scaleHom 1 ≫ X.negative) Z := by
      rwa [scaleHom_one, Category.id_comp]
    have h'' := relationOver_scaleHom hl0 h'
    rwa [mul_one] at h''

/-- The chosen linked parametrization with positive map `x`. -/
def linked : LinkedRootParametrization p.inclusion (p.rootDatum.root a) (p.rootDatum.coroot a) :=
  x.exists_linked.choose

theorem linked_positive : x.linked.positive = x.hom := x.exists_linked.choose_spec

theorem pairing_root_coroot :
    latticePairing p.torus (p.rootDatum.root a) (p.rootDatum.coroot a) = 2 := by
  rw [← p.isRootDatum.1]
  exact p.rootDatum.root_coroot_two a

/-- The negative partner `y(c)` of `x` at a scalar `c`. -/
def negPoint (c : k) : rationalPoints G := x.linked.xmPoint c

theorem xpPoint_linked (c : k) : x.linked.xpPoint c = x.toRootParametrization.rationalPoint c := by
  rw [LinkedRootParametrization.xpPoint, x.linked_positive]
  rfl

local instance negativeRootPartnerMono : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

theorem rootPoint_linked_negative (c : k) :
    rootPoint x.linked.negative (𝟙_ (Over (Spec (CommRingCat.of k)))) (LinkedRootParametrization.secMap k c) =
      x.negPoint c := rfl

theorem rootPoint_linked_positive (c : k) :
    rootPoint x.linked.positive (𝟙_ (Over (Spec (CommRingCat.of k)))) (LinkedRootParametrization.secMap k c) =
      x.toRootParametrization.rationalPoint c := by
  rw [← x.xpPoint_linked]
  rfl

/-- `(y(-1), y(-1))` is the opposite pair of the unit point `x(1)`. -/
theorem isOppositeFactorPair_unitPoint :
    RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root a) x.unitPoint
      (x.negPoint (-1), x.negPoint (-1)) := by
  have e1 := x.rootPoint_linked_positive 1
  rw [map_one] at e1
  have e2 := x.rootPoint_linked_negative (-1)
  rw [map_neg, map_one] at e2
  have hx1 : rootPoint x.linked.positive (𝟙_ (Over (Spec (CommRingCat.of k)))) 1 ≠ 1 := by
    rw [e1]
    exact x.unitPoint_ne_one
  have h := isOppositeFactorPair_weylPoint p.isSplitTorus (p.root_mem_relativeRoots a).1
    x.linked.positive_represents x.linked.negative_represents x.linked.negative_equivariant
    (x.linked.relation _) (p.root_mem_relativeRoots a)
    (splitPinnedOppositeFactorPairs k G p) hx1
  rw [e1, e2] at h
  exact h

theorem negPoint_mem (c : k) :
    x.negPoint c ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root a)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [← x.linked.negative_represents.2]
  exact ⟨_, rfl⟩

/-- Cocharacter points centralize the torus, hence normalize it. -/
theorem cocharacterPoint_mem_normalizerPoints (ν : cocharacterLattice p.torus) (t : kˣ) :
    LinkedRootParametrization.cocharacterPoint p.inclusion ν t ∈ normalizerPoints p.inclusion := by
  apply centralizerPoints_le_normalizerPoints
  rw [← torusCentralizer_carrier_base]
  exact range_le_torusCentralizer p.inclusion _
    ⟨(Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
      (Units.map (LinkedRootParametrization.secMap k).toMonoidHom t) ≫
        (CommGroupScheme.groupHom ν).hom.hom, by
      change _ ≫ p.inclusion.hom.hom = _
      exact Category.assoc _ _ _⟩

/-- `(y(-c⁻¹), y(-c⁻¹))` is the opposite pair of `x(c)` for every unit `c`. -/
theorem isOppositeFactorPair_rationalPoint (c : kˣ) :
    RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root a)
      (x.toRootParametrization.rationalPoint c)
      (x.negPoint (-(c : k)⁻¹), x.negPoint (-(c : k)⁻¹)) := by
  refine ⟨x.negPoint_mem _, x.negPoint_mem _, ?_⟩
  set D := x.linked.rankOneData (pairing_root_coroot (a := a))
  have hw : x.negPoint (-(c : k)⁻¹) * x.toRootParametrization.rationalPoint c *
      x.negPoint (-(c : k)⁻¹) = D.w c := by
    rw [← x.xpPoint_linked]
    rfl
  have hw1 : D.w 1 = x.negPoint (-1) * x.unitPoint * x.negPoint (-1) := by
    show D.xm (-((1 : kˣ) : k)⁻¹) * D.xp ((1 : kˣ) : k) * D.xm (-((1 : kˣ) : k)⁻¹) = _
    rw [Units.val_one, inv_one]
    change x.negPoint (-1) * x.linked.xpPoint 1 * x.negPoint (-1) = _
    rw [x.xpPoint_linked]
    rfl
  rw [hw, D.w_eq_h_mul_w_one, hw1]
  exact (normalizerPoints p.inclusion).mul_mem
    (cocharacterPoint_mem_normalizerPoints (p := p) _ c) x.isOppositeFactorPair_unitPoint.2.2

theorem negPoint_zero : x.negPoint 0 = 1 :=
  (x.linked.rankOneData (pairing_root_coroot (a := a))).xm_zero

/-- Every opposite pair of `x(c)` is `(y(-c⁻¹), y(-c⁻¹))`. -/
theorem eq_negPoint_of_isOppositeFactorPair (c : kˣ) {q : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root a)
      (x.toRootParametrization.rationalPoint c) q) :
    q = (x.negPoint (-(c : k)⁻¹), x.negPoint (-(c : k)⁻¹)) :=
  hq.eq p.inclusion p.isSplitTorus (p.root_mem_relativeRoots a).1
    (x.toRootParametrization.rationalPoint_mem c)
    (x.toRootParametrization.rationalPoint_ne_one c.ne_zero)
    (x.isOppositeFactorPair_rationalPoint c)

end SplitPinning.NormalizedRootParametrization

end Langlands.GroupScheme
