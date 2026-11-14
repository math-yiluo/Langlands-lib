import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Rational.SteinbergRootRepresentatives
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Noncommutation of nontrivial points of adjacent simple root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

set_option autoImplicit false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

/-- Specified normalized points of adjacent simple root groups do not commute. -/
def AdjacentSimpleRootNoncommutationStatement : Prop :=
  ∀ (x : p.NormalizedSimpleRootParametrizations)
    (a b : p.base.support), a ≠ b → p.rootDatum.pairing a b = -1 →
    ∀ c₀ : k, c₀ ≠ 0 → 1 + c₀ ≠ 0 →
      ¬ Commute ((x a).toRootParametrization.rationalPoint 1)
        ((x b).toRootParametrization.rationalPoint 1)

/-- Points of distinct simple root groups commute with the opposite of the other root. -/
theorem commute_simple_neg_simple (a b : p.base.support) (hab : a ≠ b)
    {Z : Over (Spec (CommRingCat.of k))} {x y : Z ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root b)).carrier Z) :
    Commute x y := by
  apply p.commute_of_no_strict_root_combinations _ _
    (p.rootDatum.ne_zero a) (neg_ne_zero.mpr (p.rootDatum.ne_zero b)) _ hx hy
  intro n m hn hm
  simpa only [smul_neg, ← sub_eq_add_neg] using
    p.strict_mixed_simple_ne_zero_not_root a b hab n m hn hm

/-- Centralizing one nontrivial positive root point and the whole negative root group
forces centralization of the whole positive root group. -/
theorem commute_root_of_commute_point_and_opposite (r : p.rootIndex)
    {g y : rationalPoints G}
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 _))) (hy1 : y ≠ 1)
    (hgy : Commute g y)
    (hm : ∀ z : rationalPoints G,
      z ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) → Commute g z)
    {z : rationalPoints G}
    (hz : z ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
      (Over.mk (𝟙 _))) : Commute g z := by
  obtain ⟨q, hq⟩ := splitPinnedOppositeFactorPairs k G p (p.rootDatum.root r)
    (p.root_mem_relativeRoots r) y hy hy1
  let n : normalizerPoints p.inclusion := ⟨q.1 * y * q.2, hq.2.2⟩
  have hn : weylAction p.inclusion n = p.rootDatum.reflection r :=
    p.oppositeFactorPair_weylAction r hy hy1 hq
  have hgn : Commute g (n : rationalPoints G) :=
    ((hm _ hq.1).mul_right hgy).mul_right (hm _ hq.2.1)
  have hc := RelativeRoot.normalizer_conj_mem p.inclusion (p.rootDatum.root r) n hz
  simp only [GroupScheme.constantPoint_self, hn, RootPairing.reflection_apply_self] at hc
  have h := (hgn.inv_right.mul_right (hm _ hc)).mul_right hgn
  simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h

/-- A nontrivial simple root point cannot commute with a nontrivial point of a simple
root whose coroot has pairing `-1`, over a field with an element outside `{0,-1}`. -/
theorem rationalPoint_not_commute_of_pairing_neg_one
    (a b : p.base.support) (hab : a ≠ b)
    (hpair : p.rootDatum.pairing a b = -1)
    (c₀ : k) (hc₀ : c₀ ≠ 0) (hc₁ : 1 + c₀ ≠ 0)
    (xa : p.RootParametrization a) (s : k) (hs : s ≠ 0)
    {y : rationalPoints G}
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root b)).carrier
      (Over.mk (𝟙 _))) (hy1 : y ≠ 1) :
    ¬ Commute (xa.rationalPoint s) y := by
  intro hcomm
  let Z := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let x : Z ⟶ G.X := xa.rationalPoint s
  have hx : x ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier Z :=
    xa.rationalPoint_mem s
  have hm : ∀ z : Z ⟶ G.X,
      z ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root b)).carrier Z →
        Commute x z :=
    fun z hz => p.commute_simple_neg_simple a b hab hx hz
  have hp : ∀ z : Z ⟶ G.X,
      z ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root b)).carrier Z →
        Commute x z :=
    fun z hz => p.commute_root_of_commute_point_and_opposite b hy hy1 hcomm hm hz
  let X := p.linkedRootParametrization b.val
  let f : k →+* Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let c := f c₀
  have hc : c ≠ 0 := by
    intro he
    apply hc₀
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.injective (he.trans (map_zero f).symm)
  have hu : IsUnit (1 + c) := by
    have h := (isUnit_iff_ne_zero.mpr hc₁).map f
    simpa only [map_add, map_one] using h
  let v : Γ(Z.left, ⊤)ˣ := hu.unit
  have hv : (v : Γ(Z.left, ⊤)) = 1 + c := hu.unit_spec
  let t : Z ⟶ p.torus.X :=
    (Gm.pointsEquiv _ Z).symm v ≫
      (CommGroupScheme.groupHom (p.rootDatum.coroot b)).hom.hom
  let w : Γ(Z.left, ⊤) := ((v⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤))
  have hrel := X.relation Z (RootCell.pt 1) (RootCell.pt c) (RootCell.pt (w * 1))
    (RootCell.pt (w * c)) v
    (by rw [RootCell.crd_pt, RootCell.crd_pt, one_mul, hv])
    (by rw [RootCell.crd_pt, RootCell.crd_pt])
    (by rw [RootCell.crd_pt, RootCell.crd_pt])
  change _ = _ * (t ≫ p.inclusion.hom.hom) * _ at hrel
  have hpX (d : Γ(Z.left, ⊤)) :
      Commute x (RootCell.pt d ≫ X.positive.hom.hom) := by
    apply hp
    exact RootPairNoncommutation.mem_of_isRepresentedBy X.positive_represents _
  have hmX (d : Γ(Z.left, ⊤)) :
      Commute x (RootCell.pt d ≫ X.negative.hom.hom) := by
    apply hm
    exact RootPairNoncommutation.mem_of_isRepresentedBy X.negative_represents _
  have ht : Commute x (t ≫ p.inclusion.hom.hom) := by
    rw [RootPairNoncommutation.solve_middle hrel]
    exact (((hmX _).inv_right.mul_right ((hpX _).mul_right (hmX _))).mul_right
      (hpX _).inv_right)
  have heq := xa.torus_equivariant Z t (f s)
  have hval : VectorGroup.charValue (p.rootDatum.root a) Z t =
      ((v⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) := by
    rw [RankOneRootCellRelation.charValue_eq_cu, RootPairNoncommutation.cu_cocharacter,
      ← p.isRootDatum.1, p.rootDatum.root_coroot_eq_pairing, hpair, zpow_neg_one]
  change (t ≫ p.inclusion.hom.hom) * x * (t ≫ p.inclusion.hom.hom)⁻¹ = _ at heq
  have hfix : (t ≫ p.inclusion.hom.hom) * x * (t ≫ p.inclusion.hom.hom)⁻¹ = x := by
    rw [ht.eq.symm, mul_inv_cancel_right]
  rw [hfix, hval] at heq
  have hcoord : f s = (v⁻¹ : Γ(Z.left, ⊤)ˣ) * f s :=
    xa.point_injective Z heq
  have hs' : IsUnit (f s) := (isUnit_iff_ne_zero.mpr hs).map f
  have hv1 : v = 1 := by
    apply inv_eq_one.mp
    apply Units.val_eq_one.mp
    exact hs'.mul_right_cancel (hcoord.symm.trans (one_mul _).symm)
  apply hc
  have h := congrArg Units.val hv1
  rw [hv, Units.val_one] at h
  simpa using h

/-- Nonzero values in the two root coordinates do not commute. -/
theorem adjacent_rationalPoint_not_commute
    (a b : p.base.support) (hab : a ≠ b)
    (hpair : p.rootDatum.pairing a b = -1)
    (c₀ : k) (hc₀ : c₀ ≠ 0) (hc₁ : 1 + c₀ ≠ 0)
    (xa : p.RootParametrization a) (xb : p.RootParametrization b)
    (s t : k) (hs : s ≠ 0) (ht : t ≠ 0) :
    ¬ Commute (xa.rationalPoint s) (xb.rationalPoint t) :=
  p.rationalPoint_not_commute_of_pairing_neg_one a b hab hpair c₀ hc₀ hc₁ xa s hs
    (xb.rationalPoint_mem t) (xb.rationalPoint_ne_one ht)

/-- The normalized pinned simple-root points at parameter one do not commute. -/
theorem adjacent_unitPoint_not_commute
    (x : p.NormalizedSimpleRootParametrizations)
    (a b : p.base.support) (hab : a ≠ b)
    (hpair : p.rootDatum.pairing a b = -1)
    (c₀ : k) (hc₀ : c₀ ≠ 0) (hc₁ : 1 + c₀ ≠ 0) :
    ¬ Commute ((x a).toRootParametrization.rationalPoint 1)
      ((x b).toRootParametrization.rationalPoint 1) :=
  p.adjacent_rationalPoint_not_commute a b hab hpair c₀ hc₀ hc₁
    (x a).toRootParametrization (x b).toRootParametrization 1 1 one_ne_zero one_ne_zero

/-- The adjacent-simple-root noncommutation proposition for the supplied pinning. -/
theorem adjacentSimpleRootNoncommutation :
    p.AdjacentSimpleRootNoncommutationStatement := by
  intro x a b hab hpair c₀ hc₀ hc₁
  exact p.adjacent_unitPoint_not_commute x a b hab hpair c₀ hc₀ hc₁

end Langlands.GroupScheme.SplitPinning
