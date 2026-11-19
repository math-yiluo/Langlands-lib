import Langlands.GroupScheme.MultiplicativeLaurent
import Langlands.GroupScheme.Rational.PointTopology
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The continuous scalar-unit parametrization of multiplicative-group points -/

noncomputable section
universe u

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.GroupScheme.Gm
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]

private abbrev fieldBase := Spec (CommRingCat.of k)
private abbrev laurentFieldRing := CommRingCat.of (LaurentPolynomial k)

local instance : IsAffine (Gm (fieldBase (k := k))).X.left := by
  change IsAffine (Limits.pullback
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    (toSpecZ (fieldBase (k := k))))
  infer_instance

private def laurentFieldPoint (a : kˣ) : Over.mk (𝟙 (fieldBase (k := k))) ⟶
    relativeLaurent (CommRingCat.of k) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a))) (by
    change Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a)) ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C) = 𝟙 _
    have h : CommRingCat.ofHom LaurentPolynomial.C ≫
        CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a) =
        𝟙 (CommRingCat.of k) :=
      CommRingCat.hom_ext (RingHom.ext fun r => LaurentPolynomial.eval₂_C _ _ r)
    rw [← Spec.map_comp, h, Spec.map_id])

private theorem laurentFieldPoint_eval (a : kˣ) (r : Γ(Spec (laurentFieldRing (k := k)), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((laurentFieldPoint a).left.appTop r) =
      LaurentPolynomial.eval₂ (RingHom.id k) a
        ((Scheme.ΓSpecIso (laurentFieldRing (k := k))).hom r) := by
  change (((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) a))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom) r) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

private theorem affinePointsEquiv_symm_eq_laurent (a : kˣ) :
    (affinePointsEquiv (𝟙 (fieldBase (k := k)))).symm a =
      laurentFieldPoint a ≫ (relativeLaurentIso (CommRingCat.of k)).inv := by
  apply (affinePointsEquiv _).injective
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [← relativeLaurentIso_affinePointsEquiv_val (𝟙 _)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change a.val = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((laurentFieldPoint a).left.appTop
    ((Scheme.ΓSpecIso (laurentFieldRing (k := k))).inv (LaurentPolynomial.T 1)))
  rw [laurentFieldPoint_eval]
  change a.val = LaurentPolynomial.eval₂ (RingHom.id k) a
    (((Scheme.ΓSpecIso (laurentFieldRing (k := k))).inv ≫
      (Scheme.ΓSpecIso (laurentFieldRing (k := k))).hom) (LaurentPolynomial.T 1))
  rw [Iso.inv_hom_id, CommRingCat.id_apply, LaurentPolynomial.eval₂_T, zpow_one]

variable [TopologicalSpace k] [IsTopologicalRing k]

private theorem continuous_laurentFieldEval (r : LaurentPolynomial k) :
    Continuous fun a : kˣ => LaurentPolynomial.eval₂ (RingHom.id k) a r := by
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | C_mul_T n c =>
      simp only [LaurentPolynomial.eval₂_C_mul_T]
      exact continuous_const.mul (Units.continuous_val.comp (continuous_zpow n))

/-- The usual scalar units parametrize multiplicative-group rational points continuously
for the canonical evaluation topology. -/
theorem continuous_affinePointsEquiv_symm_rational :
    Continuous[inferInstance, rationalPointTopology k (Gm (fieldBase (k := k))).X]
      ((affinePointsEquiv (𝟙 (fieldBase (k := k)))).symm : kˣ →
        rationalPoints (Gm (fieldBase (k := k))).toGrp) := by
  let G : GroupScheme (fieldBase (k := k)) := (Gm (fieldBase (k := k))).toGrp
  let S := CommAlgCat.of (CommRingCat.of k) k
  let : TopologicalSpace S := inferInstanceAs (TopologicalSpace k)
  let : TopologicalSpace (G.affinePoints S) := G.affinePointsTopologicalSpace S
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  let e := rationalPointsAffineHomeomorph G
  let p : kˣ → rationalPoints G := (affinePointsEquiv (𝟙 (fieldBase (k := k)))).symm
  change Continuous p
  apply (e.isInducing.continuous_iff).mpr
  apply (G.continuous_affinePoints_iff S _).mpr
  intro r
  let q := (relativeLaurentIso (CommRingCat.of k)).inv.left.appTop r
  have heval : (fun a => G.affinePointEvaluation S (e (p a)) r) =
      (fun a => LaurentPolynomial.eval₂ (RingHom.id k) a
        ((Scheme.ΓSpecIso (laurentFieldRing (k := k))).hom q)) := by
    funext a
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((e (p a)).left.appTop r) = _
    rw [rationalPointsAffineHomeomorph_left]
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (((affinePointsEquiv (𝟙 (fieldBase (k := k)))).symm a).left.appTop r) = _
    rw [affinePointsEquiv_symm_eq_laurent, Over.comp_left, Scheme.Hom.comp_appTop]
    exact laurentFieldPoint_eval a q
  change Continuous (fun a => G.affinePointEvaluation S (e (p a)) r)
  rw [heval]
  exact continuous_laurentFieldEval _

/-- The canonical map from scalar units to rational points of the multiplicative group. -/
def rationalPointOfUnit :
    letI : TopologicalSpace (rationalPoints (Gm (fieldBase (k := k))).toGrp) :=
      rationalPointTopology k (Gm (fieldBase (k := k))).X
    kˣ →ₜ* rationalPoints (Gm (fieldBase (k := k))).toGrp := by
  letI : TopologicalSpace (rationalPoints (Gm (fieldBase (k := k))).toGrp) :=
    rationalPointTopology k (Gm (fieldBase (k := k))).X
  exact
    { toMonoidHom := (affinePointsEquiv (𝟙 (fieldBase (k := k)))).symm.toMonoidHom
      continuous_toFun := continuous_affinePointsEquiv_symm_rational }

end Langlands.GroupScheme.Gm
