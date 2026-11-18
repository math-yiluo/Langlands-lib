import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.LeviCentralCompatibilityStatements
import Langlands.GroupScheme.Rational.LeviRadicalIntersectionCenter
import Langlands.GroupScheme.Rational.LeviSplitComponentCentralizerProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Inclusion of split components of nested rational Levis -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The split component of a rational Levi factors through the split component
of a rational Levi contained in it. -/
theorem leviSplitComponentInclusion : LeviSplitComponentInclusionStatement.{u} := by
  intro k _ G hG P Q M L p q lM lL m hp hq hlM hlL hm AL AM aL aM haL haM
  have hM : IsClosedSubgroup (lM ≫ p) := hlM.isClosedSubgroup.comp hp.isClosedSubgroup
  have hL : IsClosedSubgroup (lL ≫ q) := hlL.isClosedSubgroup.comp hq.isClosedSubgroup
  have hZ : (torusCentralizer (aM ≫ lM ≫ p)).IsRepresentedBy (lM ≫ p) :=
    ⟨hM.mono_overHom, (leviSplitComponentCentralizer k G hG P M p lM hp hlM AM aM haM).symm⟩
  have haLCentral := haL.isCentralSplitTorus.isCentral
  have haMInL : (aM ≫ m) ≫ lL ≫ q = aM ≫ lM ≫ p := by
    rw [Category.assoc, hm]
  have hRange : SubgroupFunctor.range (aL ≫ lL ≫ q) ≤ torusCentralizer (aM ≫ lM ≫ p) :=
    haLCentral.range_comp_le_torusCentralizer_of_factor (lL ≫ q) _ (aM ≫ m) haMInL
  let g := hZ.factorHom (aL ≫ lL ≫ q) hRange
  have hgG : g ≫ lM ≫ p = aL ≫ lL ≫ q := hZ.factorHom_comp _ _
  have hLRep : (SubgroupFunctor.range (lL ≫ q)).IsRepresentedBy (lL ≫ q) :=
    ⟨hL.mono_overHom, rfl⟩
  have hg : g ≫ m = aL := by
    apply hLRep.hom_ext
    rw [Category.assoc, hm, hgG]
  have hmClosed : IsClosedSubgroup m := IsClosedSubgroup.of_comp hL (by
    rw [hm]
    exact hM)
  have hgCentral : IsCentral g := by
    apply IsCentral.of_comp hmClosed.mono_overHom
    rwa [hg]
  have : IsAffineHom M.X.hom := hlM.isConnectedReductive.isAffineHom
  obtain ⟨f, hf⟩ := haM.exists_factor haL.isCentralSplitTorus.isSplitSubtorus.1 hgCentral
  refine ⟨Additive.ofMul f, ?_⟩
  change f ≫ aM ≫ m = aL
  rw [← Category.assoc, hf, hg]

end Langlands.GroupScheme
