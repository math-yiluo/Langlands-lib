import Langlands.Representation.Exponents.RepresentedParabolicRemarksStatements
import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.GroupScheme.Rational.ParabolicLeviStandardConjugation
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Supercuspidality tested on the proper standard parabolics

Renard VI.2.1, first block of Remarks, Remark 1. Rational conjugation carries
an arbitrary parabolic and its specified Levi into the fixed standard family;
translation of coinvariants then transfers Jacquet-module vanishing.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.2.1, Remark 1: the proper standard parabolics suffice to test
supercuspidality, with the structural inputs supplied by published proofs. -/
theorem supercuspidalStandardParabolicCriterion :
    SupercuspidalStandardParabolicCriterionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ T i hi ν hν A
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have := hi.isSplitSubtorus.mono
  constructor
  · intro hA P M U p l r hp hl hr hmul J _ _ _ hproper
    exact hA P M U p l r hp hl hr hmul hproper
  · intro hstd P M U p l r hp hl hr hmul hproper
    let g := parabolicLeviStandardConjugatingPoint parabolicDynamic
      dynamicGeometricUnipotentRadical smoothMaximalSplitTorusConjugacy hG hi
      (relativeRootSystem k G hG T i hi) hν p l hp hl
    obtain ⟨J, ζ, hζ, hP, hL, -, -⟩ := g.property
    have hp' := hp.comp_iso (G.innerIso g.val)
    have hproper' : ¬ IsIso (p ≫ (G.innerIso g.val).hom) := by
      intro hiso
      apply hproper
      have heq : p = (p ≫ (G.innerIso g.val).hom) ≫ (G.innerIso g.val).inv := by simp
      rw [heq]
      infer_instance
    have hvanish := hstd P M U (p ≫ (G.innerIso g.val).hom) l r hp' hl hr hmul J hζ.1 hP hL
      hproper'
    change Subsingleton (Jacquet.Localization.Coinvariants A.representation
      (pointImage (r ≫ p ≫ (G.innerIso g.val).hom)) 1) at hvanish
    change Subsingleton (Jacquet.Localization.Coinvariants A.representation
      (pointImage (r ≫ p)) 1)
    have hconjU : ∀ x : rationalPoints G,
        x ∈ pointImage (r ≫ p ≫ (G.innerIso g.val).hom) ↔
          g.val⁻¹ * x * g.val ∈ pointImage (r ≫ p) := by
      intro x
      simpa only [Category.assoc] using mem_pointImage_comp_innerIso (r ≫ p) g.val x
    exact (coinvariantsTranslateEquiv g.val hconjU A.representation).injective.subsingleton

end Langlands.Aubert.General.RepresentedParabolic
