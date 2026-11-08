import Langlands.GroupScheme.Reductive.CanonicalRhoRootDegree
import Langlands.GroupScheme.Reductive.AffineCoordinateTranslation
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # Canonical induced coordinates on the actual opposite unipotent group -/

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
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "λ₋" => CommGroupScheme.groupHom (-ν₀) ≫ p.inclusion
local notation "U" => Dynamic.Affine.unipotentScheme λ₋
local notation "iU" => Dynamic.Affine.unipotentHom λ₋

local instance canonicalRhoUnipotentRestrictionIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance : IsAffineHom (U).X.hom :=
  (Dynamic.Affine.isClosedSubgroup_unipotentHom λ₋).isAffineHom

local instance : IsAffine (U).X.left := isAffine_of_isAffineHom (U).X.hom

/-- Restriction of actual ambient coordinates to the existing opposite-rho
dynamic unipotent representative. -/
def canonicalRhoUnipotentRestriction : algebra G →ₐ[k] algebra U :=
  schemePullback G U (iU).hom.hom

/-- The restriction has the original coordinate value on every relative test. -/
theorem pointAlgebraHom_canonicalRhoUnipotentRestriction
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ (U).X) (f : algebra G) :
    pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f) =
      pointAlgebraHom G V (g ≫ (iU).hom.hom) f :=
  pointAlgebraHom_schemePullback G U (iU).hom.hom V g f

/-- The full fixed negative simple-root map lies in the actual opposite
dynamic unipotent subgroup. -/
theorem linkedNegativeSimple_range_le_oppositeRhoUnipotent (a : p.base.support) :
    SubgroupFunctor.range (p.linkedRootParametrization a).negative ≤
      Dynamic.unipotent λ₋ := by
  have hp : 0 < latticePairing p.torus (-p.rootDatum.root a) (-ν₀) := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    exact (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
      p.base hspan a).mpr (p.base.isPos_of_mem_support a.property)
  exact (p.linkedRootParametrization a).negative_represents.2.le.trans
    (RelativeRoot.subgroup_le_dynamicUnipotent p.inclusion (-ν₀) hp)

/-- The original linked negative simple-root map lifted into the actual
opposite unipotent group. -/
def linkedNegativeSimpleUnipotentMap (a : p.base.support) : RootCell.Ga k ⟶ U :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE
    (F := Dynamic.unipotent λ₋) (i := iU)
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
    (p.linkedRootParametrization a).negative
    (p.linkedNegativeSimple_range_le_oppositeRhoUnipotent hspan a)

theorem linkedNegativeSimpleUnipotentMap_comp (a : p.base.support) :
    p.linkedNegativeSimpleUnipotentMap hspan a ≫ iU =
      (p.linkedRootParametrization a).negative :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp
    (F := Dynamic.unipotent λ₋) (i := iU)
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
    (p.linkedRootParametrization a).negative
    (p.linkedNegativeSimple_range_le_oppositeRhoUnipotent hspan a)

/-- Restriction preserves the actual polynomial on each lifted negative
simple-root curve, including its original rational translate. -/
theorem curvePolynomial_canonicalRhoUnipotentRestriction
    (a : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (U).X) (f : algebra G) :
    curvePolynomial U
      (negativeCurve U (p.linkedNegativeSimpleUnipotentMap hspan a) g)
      (p.canonicalRhoUnipotentRestriction hspan f) =
        p.linkedNegativeSimpleCurvePolynomial a (g ≫ (iU).hom.hom) f := by
  rw [canonicalRhoUnipotentRestriction, curvePolynomial_schemePullback,
    negativeCurve_comp, linkedNegativeSimpleUnipotentMap_comp]
  rfl

/-- Every member of the full canonical induced space retains its simple-root
degree bound after restriction to the actual opposite unipotent group. -/
theorem natDegree_canonicalRhoUnipotentRestriction_le [Infinite k]
    (m : ℕ) {f : algebra G} (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (a : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (U).X) :
    (curvePolynomial U
      (negativeCurve U (p.linkedNegativeSimpleUnipotentMap hspan a) g)
      (p.canonicalRhoUnipotentRestriction hspan f)).natDegree ≤ m := by
  rw [curvePolynomial_canonicalRhoUnipotentRestriction]
  exact p.natDegree_linkedNegativeSimpleCurvePolynomial_le hspan m hf a
    (g ≫ (iU).hom.hom)

variable [IsAlgClosed k]

/-- Below the characteristic-power degree bound, right Frobenius-origin
invariance of a restricted induced coordinate implies left invariance under
each original negative simple-root map on every relative test scheme. -/
theorem canonicalRhoUnipotentRestriction_leftInvariant_of_originInvariant
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
      ((s ≫ (p.linkedNegativeSimpleUnipotentMap hspan a).hom.hom) * g)
      (p.canonicalRhoUnipotentRestriction hspan f) =
        pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f) := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let : Smooth (U).X.hom := (dynamicSmooth k G λ₋ U iU).2.2
    (Dynamic.Affine.isRepresentedBy_unipotentHom λ₋)
  exact AffineCoordinateTranslation.leftInvariant_of_originInvariant_natDegree_lt
    U q r (p.linkedNegativeSimpleUnipotentMap hspan a)
    (p.canonicalRhoUnipotentRestriction hspan f) hfrob
    (fun g₀ => (p.natDegree_canonicalRhoUnipotentRestriction_le
      hspan m hf a g₀).trans_lt hm) V s g

/-- In particular, exponent `q^r - 1` supplies the strict cutoff without a
separate degree premise. -/
theorem canonicalRhoUnipotentRestriction_steinberg_leftInvariant
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
      ((s ≫ (p.linkedNegativeSimpleUnipotentMap hspan a).hom.hom) * g)
      (p.canonicalRhoUnipotentRestriction hspan f) =
        pointAlgebraHom U V g (p.canonicalRhoUnipotentRestriction hspan f) := by
  apply p.canonicalRhoUnipotentRestriction_leftInvariant_of_originInvariant
    hspan q r (q ^ r - 1) _ hf hfrob a V s g
  exact Nat.sub_lt (expChar_pow_pos k q r) Nat.zero_lt_one

end Langlands.GroupScheme.SplitPinning
