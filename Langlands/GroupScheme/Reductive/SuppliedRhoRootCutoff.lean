import Langlands.GroupScheme.Reductive.SuppliedHighestWeightWordCoordinates
import Langlands.GroupScheme.Reductive.CanonicalRhoUnipotentRestriction

/-! # Simple-root degree cutoffs from supplied linked root coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.SplitPinning

open AffineCoordinates RankOneCovariantCutoff FrobeniusRootCurveCutoff

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (c : p.SimpleRootCoordinateFamily)

local instance suppliedRhoRootDegreeIsAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The polynomial of the supplied negative simple-root curve at an actual rational translate. -/
def suppliedNegativeSimpleCurvePolynomial (a : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    algebra G →ₐ[k] k[X] :=
  curvePolynomial G (negativeCurve G (c a).negative g)

variable [Fintype p.rootIndex] (hspan : p.rootDatum.corootSpan ℤ = ⊤)

/-- Actual membership in the full covariant space bounds the supplied simple-root curves. -/
theorem natDegree_suppliedNegativeSimpleCurvePolynomial_le [Infinite k]
    (m : ℕ) {f : algebra G} (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (a : p.base.support) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (p.suppliedNegativeSimpleCurvePolynomial c a g f).natDegree ≤ m := by
  apply RankOneCovariantCutoff.natDegree_negativeCurve_le G
    p.inclusion (p.rootDatum.coroot a) (c a).positive (c a).negative
    (c a).relation f m ?_ ?_ g
  · intro Z z h
    apply p.canonicalRhoCovariantSubspace_left_root hspan m hf a
      (p.base.isPos_of_mem_support a.property) Z _ h
    rw [← (c a).positive_represents.2]
    exact SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩
  · exact fun Z z h => p.canonicalRhoCovariantSubspace_left_simpleCoroot
      hspan m hf a Z z h

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₋" => CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion
local notation "U" => Dynamic.Affine.unipotentScheme λ₋
local notation "iU" => Dynamic.Affine.unipotentHom λ₋

local instance suppliedRhoRootCutoffUnipotentIsAffineHom : IsAffineHom (U).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋).isAffineHom

local instance suppliedRhoRootCutoffUnipotentIsAffine : IsAffine (U).X.left :=
  isAffine_of_isAffineHom (U).X.hom

/-- The full fixed negative simple-root map lies in the actual opposite
dynamic unipotent subgroup. -/
theorem suppliedNegativeSimple_range_le_oppositeRhoUnipotent (a : p.base.support) :
    SubgroupFunctor.range (c a).negative ≤
      Dynamic.unipotent λ₋ := by
  have hp : 0 < latticePairing p.torus (-p.rootDatum.root a) (-ν₀) := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    exact (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
      p.base hspan a).mpr (p.base.isPos_of_mem_support a.property)
  exact (c a).negative_represents.2.le.trans
    (RelativeRoot.subgroup_le_dynamicUnipotent p.inclusion (-ν₀) hp)

/-- The original linked negative simple-root map lifted into the actual
opposite unipotent group. -/
def suppliedNegativeSimpleUnipotentMap (a : p.base.support) : RootCell.Ga k ⟶ U :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE
    (F := Dynamic.unipotent λ₋) (i := iU)
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
    (c a).negative
    (p.suppliedNegativeSimple_range_le_oppositeRhoUnipotent c hspan a)

theorem suppliedNegativeSimpleUnipotentMap_comp (a : p.base.support) :
    p.suppliedNegativeSimpleUnipotentMap c hspan a ≫ iU =
      (c a).negative :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp
    (F := Dynamic.unipotent λ₋) (i := iU)
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
    (c a).negative
    (p.suppliedNegativeSimple_range_le_oppositeRhoUnipotent c hspan a)

/-- Restriction preserves the actual polynomial on each lifted negative
simple-root curve, including its original rational translate. -/
theorem curvePolynomial_suppliedRhoUnipotentRestriction
    (a : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (U).X) (f : algebra G) :
    curvePolynomial U
      (negativeCurve U (p.suppliedNegativeSimpleUnipotentMap c hspan a) g)
      (p.canonicalRhoUnipotentRestriction hspan f) =
        p.suppliedNegativeSimpleCurvePolynomial c a (g ≫ (iU).hom.hom) f := by
  rw [canonicalRhoUnipotentRestriction, curvePolynomial_schemePullback,
    negativeCurve_comp, suppliedNegativeSimpleUnipotentMap_comp]
  rfl

/-- Every member of the full canonical induced space retains its simple-root
degree bound after restriction to the actual opposite unipotent group. -/
theorem natDegree_suppliedRhoUnipotentRestriction_le [Infinite k]
    (m : ℕ) {f : algebra G} (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (a : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (U).X) :
    (curvePolynomial U
      (negativeCurve U (p.suppliedNegativeSimpleUnipotentMap c hspan a) g)
      (p.canonicalRhoUnipotentRestriction hspan f)).natDegree ≤ m := by
  rw [curvePolynomial_suppliedRhoUnipotentRestriction]
  exact p.natDegree_suppliedNegativeSimpleCurvePolynomial_le c hspan m hf a
    (g ≫ (iU).hom.hom)

variable [IsAlgClosed k]

/-- Below the characteristic-power degree bound, right Frobenius-origin
invariance of a restricted induced coordinate implies left invariance under
each original negative simple-root map on every relative test scheme. -/
theorem suppliedRhoUnipotentRestriction_leftInvariant_of_originInvariant
    (q : ℕ) [ExpChar k q] (r m : ℕ) (hm : m < q ^ r)
    {f : algebra G} (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (hfrob : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ (U).X),
      FrobeniusCovariantInvariants.IsOriginTestPoint U q r V h →
        pointAlgebraHom U V (g * h) (p.canonicalRhoUnipotentRestriction hspan f) =
          pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f))
    (a : p.base.support)
    (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ (RootCell.Ga k).X)
    (g : V ⟶ (U).X) :
    pointAlgebraHom U V
      ((s ≫ (p.suppliedNegativeSimpleUnipotentMap c hspan a).hom.hom) * g)
      (p.canonicalRhoUnipotentRestriction hspan f) =
        pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f) := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : Smooth (U).X.hom := (dynamicSmooth k G λ₋ U iU).2.2
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
  exact AffineCoordinateTranslation.leftInvariant_of_originInvariant_natDegree_lt
    U q r (p.suppliedNegativeSimpleUnipotentMap c hspan a)
    (p.canonicalRhoUnipotentRestriction hspan f) hfrob
    (fun g₀ => (p.natDegree_suppliedRhoUnipotentRestriction_le
      c hspan m hf a g₀).trans_lt hm) V s g

/-- In particular, exponent `q^r - 1` supplies the strict cutoff without a
separate degree premise. -/
theorem suppliedRhoUnipotentRestriction_steinberg_leftInvariant
    (q : ℕ) [ExpChar k q] (r : ℕ)
    {f : algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan (q ^ r - 1))
    (hfrob : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ (U).X),
      FrobeniusCovariantInvariants.IsOriginTestPoint U q r V h →
        pointAlgebraHom U V (g * h) (p.canonicalRhoUnipotentRestriction hspan f) =
          pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f))
    (a : p.base.support)
    (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ (RootCell.Ga k).X)
    (g : V ⟶ (U).X) :
    pointAlgebraHom U V
      ((s ≫ (p.suppliedNegativeSimpleUnipotentMap c hspan a).hom.hom) * g)
      (p.canonicalRhoUnipotentRestriction hspan f) =
        pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f) := by
  apply p.suppliedRhoUnipotentRestriction_leftInvariant_of_originInvariant
    c hspan q r (q ^ r - 1) _ hf hfrob a V s g
  exact Nat.sub_lt (expChar_pow_pos k q r) Nat.zero_lt_one

end Langlands.GroupScheme.SplitPinning
