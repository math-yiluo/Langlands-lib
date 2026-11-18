import Langlands.GroupScheme.Torus.EtaleMultiplicativeTypeOrderStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Mathlib.RingTheory.Etale.Field
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.CharP.Reduced

/-! # The order of an étale group of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.EtaleMultiplicativeTypeOrder

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

/-- The algebra of global sections of an affine étale scheme over a field is étale. -/
theorem coordinate_etale (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [Etale X.hom] :
    Algebra.Etale k (AffineCoordinateRing k X) := by
  rw [← RingHom.etale_algebraMap]
  apply (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)
    (φ := CommRingCat.ofHom (algebraMap k (AffineCoordinateRing k X)))).mp
  change Etale (Spec.algebraMap k (AffineCoordinateRing k X))
  rw [affineCoordinateSpecMap]
  infer_instance

/-- An affine étale scheme over a field is finite over that field. -/
theorem isFinite_of_affine_etale (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [Etale X.hom] :
    IsFinite X.hom := by
  have := coordinate_etale k X
  have := Algebra.FormallyUnramified.finite_of_free k (AffineCoordinateRing k X)
  have h : IsFinite (Spec.algebraMap k (AffineCoordinateRing k X)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  rw [affineCoordinateSpecMap] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite
    X.left.isoSpec.inv X.hom).mp h

/-- Every field-valued point set of an affine étale scheme over a field is finite. -/
theorem finite_points (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [Etale X.hom] :
    Finite ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k K)) ⟶ X) := by
  have := coordinate_etale k X
  have := Algebra.FormallyUnramified.finite_of_free k (AffineCoordinateRing k X)
  exact Finite.of_injective
    ((affineSchemePointEquiv k X K).trans AlgPoint.algHomEquiv)
    ((affineSchemePointEquiv k X K).trans AlgPoint.algHomEquiv).injective

/-- Points of a split diagonalizable group over a field have no nontrivial point
killed by the characteristic exponent. -/
theorem diagonalizable_points_pow_eq_one (K : Type u) [Field K]
    (p : ℕ) [ExpChar K p] (Λ : Type u) [AddCommGroup Λ]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).X)
    (hx : x ^ p = 1) : x = 1 := by
  let e := Diagonalizable.characterPointsEquiv (CommRingCat.of K) Λ
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  apply e.injective
  apply MonoidHom.ext
  intro l
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  apply (frobenius_inj K p)
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((e x l).val)) ^ p =
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((e 1 l).val)) ^ p
  have h : (e x l) ^ p = e 1 l := by
    rw [← MonoidHom.pow_apply, ← map_pow, hx]
  simpa only [map_one, MonoidHom.one_apply, Units.val_one, map_pow,
    Units.val_pow_eq_pow_val, one_pow]
    using congrArg (fun z : Γ(Spec (CommRingCat.of K), ⊤)ˣ =>
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom z.val) h

/-- Geometric points of a group of multiplicative type have no nontrivial point
killed by the characteristic exponent. -/
theorem points_pow_eq_one (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsMultiplicativeType G)
    (x : G.affinePoints (CommAlgCat.of k Ks)) (hx : x ^ p = 1) : x = 1 := by
  have : IsSepClosed Ks := IsSepClosure.sep_closed k
  have : ExpChar Ks p := expChar_of_injective_algebraMap (algebraMap k Ks).injective p
  let b := Spec.map (CommRingCat.ofHom (algebraMap k Ks))
  obtain ⟨Λ, hΛ, hfg, ⟨d⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _
      (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
        k Ks G hG)
  let e := (baseChangePointsEquiv b G
    (Over.mk (𝟙 (Spec (CommRingCat.of Ks))))).symm.trans
      (isoPointsEquiv d (Over.mk (𝟙 (Spec (CommRingCat.of Ks)))))
  apply e.injective
  exact (diagonalizable_points_pow_eq_one Ks p Λ (e x) (by rw [← map_pow, hx, map_one])).trans
    (map_one e).symm

/-- The geometric order of an affine étale group of multiplicative type is prime
to the characteristic exponent. -/
theorem forward (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
    (G : GroupScheme (Spec (CommRingCat.of k))) [Etale G.X.hom]
    [IsAffineHom G.X.hom] (hG : IsMultiplicativeType G) :
    IsCommMonObj G.X ∧ Nat.Coprime (Nat.card (G.affinePoints (CommAlgCat.of k Ks))) p := by
  refine ⟨hG.isCommMonObj, ?_⟩
  obtain hp | rfl := expChar_is_prime_or_one k p
  · have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have := finite_points k Ks G.X
    have : Fact p.Prime := ⟨hp⟩
    apply Nat.Coprime.symm
    apply (hp.coprime_iff_not_dvd).2
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := G.affinePoints (CommAlgCat.of k Ks)) p hdvd
    have hx1 : x = 1 := points_pow_eq_one k p Ks G hG x
      (hx ▸ pow_orderOf_eq_one x)
    rw [hx1, orderOf_one] at hx
    exact hp.ne_one hx.symm
  · exact Nat.coprime_one_right _

end Langlands.GroupScheme.EtaleMultiplicativeTypeOrder
