import Langlands.GroupScheme.Rational.AnisotropicQuadraticTypeAScalarPresentation
import Langlands.GroupScheme.Rational.NumberFieldHermitianMatrixIsotropy
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.TypeE6QuadraticSplitTypeA2

/-! # Isotropy of type E6 split by a quadratic extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- A simply connected E6 group split over a quadratic extension of a
    totally complex number field is isotropic. -/
theorem TitsIndexData.not_isAnisotropic_of_typeE6_quadraticSplit
    {F K : Type u} [Field F] [NumberField F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hF : IsTotallyComplex F) (hsc : IsSimplyConnected G)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hK : Module.finrank F K = 2)
    (hsplit : HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F K)).obj G)) :
    ¬ IsAnisotropic G := by
  intro hG
  obtain ⟨D, j, hj, hscD, q, f, hA⟩ :=
    hG.exists_quadraticSplit_typeA2_subgroup d e hsc hE hK hsplit
  let : Algebra.IsQuadraticExtension F K := ⟨hK⟩
  let : IsAffineHom D.X.hom := hj.isAffineHom
  let : LocallyOfFiniteType D.X.hom := hj.locallyOfFiniteType
  have hD : IsAnisotropic D := by
    change splitRank D = 0
    exact nonpos_iff_eq_zero.mp ((splitRank_le_of_isClosedSubgroup j hj).trans hG.le)
  obtain ⟨J, ⟨p⟩⟩ := hD.exists_quadratic_typeA_hermitian_presentation hscD q (by decide) f hA
  exact (p.not_isAnisotropic_of_totallyComplex hF (by decide)) hD

/-- Quadratically split type E6 forms over totally complex number fields
    have positive split rank over the ground field. -/
def NumberFieldTotallyComplexTypeE6QuadraticSplitIsotropyStatement : Prop :=
  ∀ (F K : Type u) [Field F] [NumberField F] [Field K] [Algebra F K]
      [FiniteDimensional F K] [IsGalois F K], IsTotallyComplex F → Module.finrank F K = 2 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
        IsSimplyConnected G → (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
        HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) →
        ¬ IsAnisotropic G

theorem numberFieldTotallyComplexTypeE6QuadraticSplitIsotropy :
    NumberFieldTotallyComplexTypeE6QuadraticSplitIsotropyStatement.{u} := by
  intro F K _ _ _ _ _ _ hF hK G _ _ d e hsc hE hsplit
  exact d.not_isAnisotropic_of_typeE6_quadraticSplit e hF hsc hE hK hsplit

end Langlands.GroupScheme
