import Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Absolute.ParabolicNormalizerPointsReduction
import Langlands.Representation.Exponents.LeviNormalizerBridge

/-! # Rational normalizers of a Levi and its split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Renard V.3.5.1: the rational normalizers of a rational Levi and its split
component agree, with the supplied inclusions unchanged. -/
theorem leviSplitComponentNormalizer : LeviSplitComponentNormalizerStatement.{u} := by
  intro k _ G hG P L j l hj hl A a ha
  let : IsAffineHom L.X.hom := hl.isConnectedReductive.isAffineHom
  have hc : torusCentralizer (a ≫ l ≫ j) = SubgroupFunctor.range (l ≫ j) :=
    ha.torusCentralizer_comp_eq_of_parabolicDynamic parabolicDynamic hG hj hl
  apply le_antisymm
  · intro n hn V b x hx
    rw [← hc] at hx ⊢
    have hnb := (torusNormalizer (a ≫ l ≫ j)).comp_mem b hn
    have hnorm := torusCentralizer_isNormalizedBy_torusNormalizer (a ≫ l ≫ j)
    refine ⟨hnorm V _ _ hnb hx, ?_⟩
    simpa only [inv_inv] using
      hnorm V _ _ (((torusNormalizer (a ≫ l ≫ j)).carrier V).inv_mem hnb) hx
  · intro n hn
    let := (hl.isClosedSubgroup.comp hj.isClosedSubgroup).mono
    have : Mono (l ≫ j).hom.hom := Over.mono_of_mono_left _
    let φ := SubgroupFunctor.normalizerRestrictionIso hn
    have hφ : φ.hom ≫ (l ≫ j) = (l ≫ j) ≫ (G.innerIso n).hom :=
      SubgroupFunctor.normalizerRestrictionIso_hom_comp hn
    apply normalizerPoints_le_torusNormalizer (a ≫ l ≫ j)
    exact ⟨ha.automorphismRestrictionIso φ, ha.isNormalizingPoint_of_normalizes hφ⟩

end Langlands.GroupScheme
