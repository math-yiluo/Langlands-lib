import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport
import Langlands.GroupScheme.Rational.ParabolicNormalizerProof
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.Representation.Exponents.MaximalLeviFixedDirectionNormalizer
import Mathlib.GroupTheory.DoubleCoset

/-! # Distinguishing actual parabolic conjugates by double-coset coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G Q R : GroupScheme (Spec (CommRingCat.of k))}

/-- Equal conjugated images make the original parabolics rationally conjugate. -/
theorem rationallyConjugate_of_conjugate_range_eq
    (q : Q ⟶ G) (r : R ⟶ G) (x y : rationalPoints G)
    (h : SubgroupFunctor.range (q ≫ (G.innerIso x).hom) =
      SubgroupFunctor.range (r ≫ (G.innerIso y).hom)) :
    (SubgroupFunctor.range q).IsRationallyConjugate (SubgroupFunctor.range r) := by
  rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_comp_iso] at h
  have hc := congrArg
    (fun F : SubgroupFunctor G => F.comap (G.innerIso x).hom) h
  rw [SubgroupFunctor.comap_iso_inv_hom, ← SubgroupFunctor.comap_comp,
    ← innerIso_inv_hom, ← innerIso_mul_hom] at hc
  exact ⟨y⁻¹ * x, hc⟩

/-- Self-normalization of an actual rational parabolic distinguishes the
conjugated parabolics attached to distinct actual double cosets. -/
theorem doubleCoset_eq_of_conjugate_parabolic_eq
    (hG : IsConnectedReductive G) (H : Subgroup (rationalPoints G))
    (q : Q ⟶ G) (hq : IsParabolicSubgroup q) (x y : rationalPoints G)
    (h : SubgroupFunctor.range (q ≫ (G.innerIso x).hom) =
      SubgroupFunctor.range (q ≫ (G.innerIso y).hom)) :
    DoubleCoset.mk H (pointImage q) x = DoubleCoset.mk H (pointImage q) y := by
  have hc := (SubgroupFunctor.range_comp_iso_eq_iff
    (q ≫ (G.innerIso y).hom) (q ≫ (G.innerIso x).hom) (G.innerIso x).symm).mpr h.symm
  have hc' : SubgroupFunctor.range (q ≫ (G.innerIso (x⁻¹ * y)).hom) =
      SubgroupFunctor.range q := by
    simpa only [Iso.symm_hom, innerIso_mul_hom, innerIso_inv_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc
  have hmem : x⁻¹ * y ∈ pointImage q :=
    mem_pointImage_of_range_comp_innerIso_eq hq.isClosedSubgroup
      (parabolicSelfNormalizer k G hG Q q hq) _ hc'.symm
  apply DoubleCoset.eq.mpr
  exact ⟨1, H.one_mem, x⁻¹ * y, hmem, by group⟩

end Langlands.Aubert.General.RepresentedParabolic
