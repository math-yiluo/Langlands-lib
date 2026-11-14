import Langlands.Algebra.RankOneRelationIdentities
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Reductive.RankOneRootCellRelation

/-! # Rational points of linked root parametrizations satisfy the rank-one relation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LinkedRootParametrization

open RankOneRootCellRelation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {α : characterLattice T} {ν : cocharacterLattice T}

/-- The identification of `k` with the global sections of `Spec k`. -/
abbrev secMap (k : Type u) [Field k] : k →+* Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The rational point of a cocharacter at a unit, composed with `i`. -/
def cocharacterPoint (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) : kˣ →* rationalPoints G where
  toFun t := (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
      (Units.map (secMap k).toMonoidHom t) ≫ (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom
  map_one' := by
    simp only [map_one, MonObj.one_comp]
  map_mul' a b := by
    simp only [map_mul, MonObj.mul_comp]

variable (X : LinkedRootParametrization i α ν)

/-- `x₊(c)` as a rational point. -/
def xpPoint (c : k) : rationalPoints G :=
  gpt (Z := Over.mk (𝟙 (Spec (CommRingCat.of k)))) (secMap k c) ≫ X.positive.hom.hom

/-- `x₋(c)` as a rational point. -/
def xmPoint (c : k) : rationalPoints G :=
  gpt (Z := Over.mk (𝟙 (Spec (CommRingCat.of k)))) (secMap k c) ≫ X.negative.hom.hom

theorem xpPoint_add (a b : k) : X.xpPoint (a + b) = X.xpPoint a * X.xpPoint b := by
  rw [xpPoint, xpPoint, xpPoint, map_add, gpt_add, MonObj.mul_comp]

theorem xmPoint_add (a b : k) : X.xmPoint (a + b) = X.xmPoint a * X.xmPoint b := by
  rw [xmPoint, xmPoint, xmPoint, map_add, gpt_add, MonObj.mul_comp]

theorem relation_rational (a b : k) (u : kˣ) (hu : (u : k) = 1 + a * b) :
    X.xpPoint a * X.xmPoint b =
      X.xmPoint ((u : k)⁻¹ * b) * cocharacterPoint i ν u * X.xpPoint ((u : k)⁻¹ * a) := by
  have h := X.relation (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (gpt (secMap k a)) (gpt (secMap k b)) (gpt (secMap k ((u : k)⁻¹ * a)))
    (gpt (secMap k ((u : k)⁻¹ * b))) (Units.map (secMap k).toMonoidHom u)
    (by simp [hu]) (by simp) (by simp)
  exact h

/-- The character `α` takes the value `t ^ ⟨α, ν⟩` on the cocharacter point. -/
theorem cu_cocharacter (t : kˣ) :
    cu α ((Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
        (Units.map (secMap k).toMonoidHom t) ≫ (CommGroupScheme.groupHom ν).hom.hom) =
      Units.map (secMap k).toMonoidHom (t ^ latticePairing T α ν) := by
  rw [cu, ← comp_groupHom_comp, eq_gmEndEquiv_zsmul k (ν ≫ α), comp_groupHom_zsmul,
    ← latticePairing_apply]
  have hid : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (Gm (Spec (CommRingCat.of k))).X,
      x ≫ (CommGroupScheme.groupHom (𝟙 (Gm (Spec (CommRingCat.of k))))).hom.hom = x :=
    fun x => Category.comp_id x
  rw [hid, map_zpow, MulEquiv.apply_symm_apply, map_zpow]

/-- The cocharacter point scales `x₋` by `t⁻²` when `⟨α, ν⟩ = 2`. -/
theorem cocharacterPoint_conj_xmPoint (h2 : latticePairing T α ν = 2) (t : kˣ) (c : k) :
    cocharacterPoint i ν t * X.xmPoint c * (cocharacterPoint i ν t)⁻¹ =
      X.xmPoint ((t : k)⁻¹ ^ 2 * c) := by
  have h := X.negative_equivariant (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    ((Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
      (Units.map (secMap k).toMonoidHom t) ≫ (CommGroupScheme.groupHom ν).hom.hom)
    (secMap k c)
  rw [charValue_eq_cu, cu_neg, cu_cocharacter, h2] at h
  simp only [Category.assoc] at h
  convert h using 2
  all_goals try rfl
  · show gpt (Z := Over.mk (𝟙 (Spec (CommRingCat.of k)))) (secMap k ((t : k)⁻¹ ^ 2 * c)) ≫
      X.negative.hom.hom = _
    have hv : secMap k ((t : k)⁻¹ ^ 2 * c) =
        ((Units.map (secMap k).toMonoidHom (t ^ 2))⁻¹ : Γ(Spec (CommRingCat.of k), ⊤)ˣ) *
          secMap k c := by
      rw [map_mul]
      congr 1
      rw [← map_inv, Units.coe_map]
      change secMap k ((t : k)⁻¹ ^ 2) = secMap k (((t ^ 2)⁻¹ : kˣ) : k)
      congr 1
      simp [Units.val_inv_eq_inv_val]
    rw [hv]
    rfl

/-- The rational points of a linked root parametrization, with the cocharacter points,
satisfy the abstract rank-one relation, provided `⟨α, ν⟩ = 2`. -/
def rankOneData (h2 : latticePairing T α ν = 2) :
    Langlands.Algebra.RankOneRelation.Data k (rationalPoints G) where
  xp := X.xpPoint
  xm := X.xmPoint
  h := cocharacterPoint i ν
  xp_add := X.xpPoint_add
  xm_add := X.xmPoint_add
  h_xm := X.cocharacterPoint_conj_xmPoint h2
  relation := X.relation_rational

end LinkedRootParametrization

end Langlands.GroupScheme
