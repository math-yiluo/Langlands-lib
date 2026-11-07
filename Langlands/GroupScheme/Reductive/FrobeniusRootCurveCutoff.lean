import Langlands.GroupScheme.Reductive.RankOneCovariantCutoff
import Langlands.GroupScheme.Reductive.FrobeniusPolynomialInvariants
import Mathlib.Algebra.Polynomial.Expand

/-! # Frobenius cutoff along actual root curves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.FrobeniusRootCurveCutoff

open AffineCoordinates RankOneCovariantCutoff FrobeniusCovariantInvariants

variable {k : Type u} [Field k]

local instance : IsAffine (RootCell.Ga k).X.left :=
  inferInstanceAs (IsAffine
    ((algSpec (CommRingCat.of k)).obj
      (op (VectorGroup.coordinateAlgebra (CommRingCat.of k) 1))).left)

local instance : IsAffineHom (RootCell.Ga k).X.hom :=
  isAffineHom_of_isAffine _

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

variable (G H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Pullback of actual coordinates along any relative scheme morphism. -/
def schemePullback (a : H.X ⟶ G.X) : algebra G →ₐ[k] algebra H :=
  (globalAlgEquiv H).symm.toAlgHom.comp (pointAlgebraHom G H.X a)

theorem pointAlgebraHom_schemePullback (a : H.X ⟶ G.X)
    (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X) (b : algebra G) :
    pointAlgebraHom H V h (schemePullback G H a b) =
      pointAlgebraHom G V (h ≫ a) b := by
  rw [pointAlgebraHom_apply_eq, schemePullback, AlgHom.comp_apply]
  change h.left.appTop (globalAlgEquiv H ((globalAlgEquiv H).symm _)) = _
  rw [AlgEquiv.apply_symm_apply, pointAlgebraHom_naturality]
  rfl

variable {G H}

/-- Every affine group homomorphism preserves the intrinsic Frobenius origin. -/
theorem isOriginTestPoint_map (p : ℕ) [ExpChar k p] (r : ℕ) (j : H ⟶ G)
    (V : Over (Spec (CommRingCat.of k))) (h : V ⟶ H.X)
    (hh : IsOriginTestPoint H p r V h) :
    IsOriginTestPoint G p r V (h ≫ j.hom.hom) := by
  apply (FrobeniusPointCongruence.isOriginTestPoint_iff_congruent_one G V _).mpr
  have hc := (FrobeniusPointCongruence.isOriginTestPoint_iff_congruent_one H V h).mp hh
  intro b
  rw [AffineHomImageHopfAdapter.pointAlgebraHom_pullback]
  have he := hc ((AffineHomImageHopfAdapter.pullback j).hom b)
  have hone : (1 : V ⟶ H.X) ≫ j.hom.hom = 1 := MonObj.one_comp _
  rw [← hone, AffineHomImageHopfAdapter.pointAlgebraHom_pullback]
  exact he

/-- Actual coordinates on the additive line, compared with its polynomial algebra. -/
def additiveCoordinateEquiv : algebra (RootCell.Ga k) ≃ₐ[k] MvPolynomial (Fin 1) k :=
  (globalAlgEquiv (RootCell.Ga k)).trans
    (specCounitEquiv (VectorGroup.coordinateAlgebra (CommRingCat.of k) 1)).symm

/-- A curve polynomial is the polynomial coordinate of its actual coordinate pullback. -/
theorem curvePolynomial_eq (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (a : (RootCell.Ga k).X ⟶ G.X) (b : algebra G) :
    curvePolynomial G a b = MvPolynomial.uniqueAlgEquiv k (Fin 1)
      ((additiveCoordinateEquiv (k := k)) (schemePullback G (RootCell.Ga k) a b)) := by
  simp only [curvePolynomial, affineValue, additiveCoordinateEquiv, schemePullback,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  rfl

/-- Actual curve polynomials commute with restriction of coordinates. -/
theorem curvePolynomial_schemePullback (a : (RootCell.Ga k).X ⟶ H.X)
    (j : H.X ⟶ G.X) (b : algebra G) :
    curvePolynomial H a (schemePullback G H j b) =
      curvePolynomial G (a ≫ j) b := by
  change (MvPolynomial.uniqueAlgEquiv k (Fin 1))
      ((specCounitEquiv (VectorGroup.coordinateAlgebra (CommRingCat.of k) 1)).symm
        (pointAlgebraHom H _ a (schemePullback G H j b))) = _
  rw [pointAlgebraHom_schemePullback]
  rfl

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Negative-root curves commute with an actual homomorphism. -/
theorem negativeCurve_comp (xm : RootCell.Ga k ⟶ H) (j : H ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    negativeCurve H xm g ≫ j.hom.hom =
      negativeCurve G (xm ≫ j) (g ≫ j.hom.hom) := by
  simp only [negativeCurve, MonObj.mul_comp, Grp.comp_hom_hom,
    GroupScheme.constantPoint, Category.assoc]

/-- Variable expansion commutes with the one-variable polynomial comparison. -/
theorem uniqueAlgEquiv_expand (q : ℕ) (F : MvPolynomial (Fin 1) k) :
    MvPolynomial.uniqueAlgEquiv k (Fin 1) (MvPolynomial.expand q F) =
      Polynomial.expand k q (MvPolynomial.uniqueAlgEquiv k (Fin 1) F) := by
  have he : (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom.comp (MvPolynomial.expand q) =
      (Polynomial.expand k q).comp (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    change (MvPolynomial.uniqueAlgEquiv k (Fin 1)) (MvPolynomial.expand q (MvPolynomial.X i)) =
      Polynomial.expand k q ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) (MvPolynomial.X i))
    simp only [MvPolynomial.expand_X, map_pow,
      MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X, Polynomial.expand_X]
  exact AlgHom.congr_fun he F

/-- A characteristic-power expansion of degree less than that power is constant. -/
theorem eq_C_of_expand_natDegree_lt {P Q : k[X]} {q : ℕ}
    (hP : P = Polynomial.expand k q Q) (hdeg : P.natDegree < q) :
    P = Polynomial.C (P.coeff 0) := by
  have hQ : Q.natDegree = 0 := by
    rw [hP, Polynomial.natDegree_expand] at hdeg
    by_contra hn
    have hpos : 1 ≤ Q.natDegree := by omega
    have hle := Nat.mul_le_mul_right q hpos
    simp only [one_mul] at hle
    omega
  rw [hP, Polynomial.eq_C_of_natDegree_eq_zero hQ, Polynomial.expand_C,
    Polynomial.coeff_C_zero]

variable (G) (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The pullback to an actual translated additive-group curve retains origin invariance. -/
theorem negativeCurve_originInvariant (xm : RootCell.Ga k ⟶ G) (b : algebra G)
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∀ (V : Over (Spec (CommRingCat.of k))) (s h : V ⟶ (RootCell.Ga k).X),
      IsOriginTestPoint (RootCell.Ga k) p r V h →
        pointAlgebraHom (RootCell.Ga k) V (s * h)
          (schemePullback G (RootCell.Ga k) (negativeCurve G xm g) b) =
        pointAlgebraHom (RootCell.Ga k) V s
          (schemePullback G (RootCell.Ga k) (negativeCurve G xm g) b) := by
  intro V s h hh
  rw [pointAlgebraHom_schemePullback, pointAlgebraHom_schemePullback]
  have hmap := isOriginTestPoint_map p r xm V h hh
  have hconj : IsOriginTestPoint G p r V
      ((G.constantPoint g V)⁻¹ * (h ≫ xm.hom.hom) * G.constantPoint g V) := by
    change ((G.constantPoint g V)⁻¹ * (h ≫ xm.hom.hom) * G.constantPoint g V) ∈
      FrobeniusPointCongruence.originTestSubgroup G p r V
    simpa only [inv_inv] using
      (FrobeniusPointCongruence.originTestSubgroup_normal G p r V).conj_mem
        (h ≫ xm.hom.hom) hmap (G.constantPoint g V)⁻¹
  have he := hb V ((s ≫ xm.hom.hom) * G.constantPoint g V)
    ((G.constantPoint g V)⁻¹ * (h ≫ xm.hom.hom) * G.constantPoint g V) hconj
  simpa only [negativeCurve, MonObj.comp_mul, G.constantPoint_naturality,
    MonObj.mul_comp, mul_assoc, mul_inv_cancel_left] using he

/-- The actual curve polynomial of an origin-invariant coordinate is expanded in p^r powers. -/
theorem negativeCurve_exists_expand (xm : RootCell.Ga k ⟶ G) (b : algebra G)
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ Q : k[X], curvePolynomial G (negativeCurve G xm g) b =
      Polynomial.expand k (p ^ r) Q := by
  obtain ⟨F, hF⟩ := FrobeniusPolynomialInvariants.exists_expand_of_originInvariant
    (RootCell.Ga k) p r (additiveCoordinateEquiv (k := k))
      (negativeCurve_originInvariant G p r xm b hb g)
  refine ⟨MvPolynomial.uniqueAlgEquiv k (Fin 1) F, ?_⟩
  rw [curvePolynomial_eq, hF, uniqueAlgEquiv_expand]

/-- Origin invariance and the strict characteristic-power degree bound force constancy. -/
theorem negativeCurve_eq_C (xm : RootCell.Ga k ⟶ G) (b : algebra G)
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hdeg : (curvePolynomial G (negativeCurve G xm g) b).natDegree < p ^ r) :
    curvePolynomial G (negativeCurve G xm g) b =
      Polynomial.C ((curvePolynomial G (negativeCurve G xm g) b).coeff 0) := by
  obtain ⟨Q, hQ⟩ := negativeCurve_exists_expand G p r xm b hb g
  exact eq_C_of_expand_natDegree_lt hQ hdeg

/-- A constant curve polynomial is constant in actual coordinates. -/
theorem schemePullback_eq_scalar_of_curvePolynomial_eq_C
    (a : (RootCell.Ga k).X ⟶ G.X) (b : algebra G) (c : k)
    (hc : curvePolynomial G a b = Polynomial.C c) :
    schemePullback G (RootCell.Ga k) a b = algebraMap k _ c := by
  apply (additiveCoordinateEquiv (k := k)).injective
  apply (MvPolynomial.uniqueAlgEquiv k (Fin 1)).injective
  rw [← curvePolynomial_eq]
  simpa only [AlgEquiv.commutes, Polynomial.algebraMap_eq] using hc

/-- The cutoff gives actual root invariance on all tests through any fixed rational point. -/
theorem pointAlgebraHom_negativeCurve_eq (xm : RootCell.Ga k ⟶ G) (b : algebra G)
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hdeg : (curvePolynomial G (negativeCurve G xm g) b).natDegree < p ^ r)
    (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ (RootCell.Ga k).X) :
    pointAlgebraHom G V ((s ≫ xm.hom.hom) * G.constantPoint g V) b =
      pointAlgebraHom G V (G.constantPoint g V) b := by
  have hc := negativeCurve_eq_C G p r xm b hb g hdeg
  have hp := schemePullback_eq_scalar_of_curvePolynomial_eq_C G _ b _ hc
  have he : pointAlgebraHom (RootCell.Ga k) V s
      (schemePullback G (RootCell.Ga k) (negativeCurve G xm g) b) =
      pointAlgebraHom (RootCell.Ga k) V 1
        (schemePullback G (RootCell.Ga k) (negativeCurve G xm g) b) := by
    rw [hp, AlgHom.commutes, AlgHom.commutes]
  rw [pointAlgebraHom_schemePullback, pointAlgebraHom_schemePullback] at he
  simpa only [negativeCurve, MonObj.comp_mul, G.constantPoint_naturality,
    MonObj.one_comp, one_mul] using he

end Langlands.GroupScheme.FrobeniusRootCurveCutoff
