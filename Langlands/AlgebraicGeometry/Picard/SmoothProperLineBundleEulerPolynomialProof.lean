import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialStatement
import Langlands.AlgebraicGeometry.Modules.AmpleCoherentEulerCoefficientProof
import Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedFiniteFlatGeometryProof

/-! # Assembly of the actual smooth proper Euler polynomial theorem -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Actual tensor-power Euler characteristics are polynomial, with exact degree
and positive leading coefficient for an ample line bundle. -/
theorem smoothProperLineBundleEulerPolynomial :
    SmoothProperLineBundleEulerPolynomialStatement.{u} := by
  intro K _ X g hs hp hgc L
  let : IsProper X.hom := hp
  let : GeometricallyConnected X.hom := hgc
  let : SmoothOfRelativeDimension g X.hom := hs
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  let : IsNoetherian X.left := ⟨⟩
  let : X.left.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := X.hom)).mp inferInstance
  let : (structureModule X.left).IsQuasicoherent :=
    (LineBundle.trivial X.left).property.isQuasicoherent
  have hgeom := smoothProperConnectedFiniteFlatGeometry K X g hs hp hgc (𝟙 X)
    (by change IsFinite (𝟙 X.left); infer_instance)
    (by change Flat (𝟙 X.left); infer_instance)
  have hdim : topologicalKrullDim X.left = (g : WithBot ℕ∞) := hgeom.2.1
  refine ⟨lineBundleTensorPow_hasFiniteCohomology X.hom L,
    lineBundleEulerPolynomial X.hom L g, ?_,
    lineBundleEulerPolynomial_natDegree_le X.hom L g, ?_⟩
  · intro n
    exact lineBundleEulerPolynomial_eval X.hom L g hdim.le n _
  · intro hL
    have hcrit := ampleCoherentEulerCoefficientReduction coherentIntegralIdealFiltration
      g K X.left X.hom
      (structureModule X.left) (hasFiniteAffineSections_structureSheaf X.left) L hL
      (HasSupportDimensionLT.of_topologicalKrullDim_le hdim.le _)
    have hnot : ¬ HasSupportDimensionLT (structureModule X.left) g := by
      intro h
      have hlt := (hasSupportDimensionLT_iff_supportDimension _ g).mp h
      rw [supportDimension_structureModule, hdim] at hlt
      exact lt_irrefl _ hlt
    have hpos : 0 < (lineBundleEulerPolynomial X.hom L g).coeff g :=
      hcrit.2.mpr hnot
    have hdegree : (lineBundleEulerPolynomial X.hom L g).natDegree = g :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
        (lineBundleEulerPolynomial_natDegree_le X.hom L g) (ne_of_gt hpos)
    exact ⟨hdegree, by simpa only [Polynomial.leadingCoeff, hdegree] using hpos⟩

end Langlands.AlgebraicGeometry.Picard
