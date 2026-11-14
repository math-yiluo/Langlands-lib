import Langlands.GroupScheme.RelativeLevi.SelfNormalizerStatement
import Langlands.GroupScheme.RelativeLevi.FieldNormalizer
import Langlands.GroupScheme.RelativeLevi.GeometricNormalizerReduction

/-! # Relative Levi subgroups are self-normalizing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A relative Levi subgroup of a parabolic subgroup of a reductive group scheme
is its own normalizer, on all schemes over the base. -/
theorem relativeLeviSelfNormalizer : RelativeLeviSelfNormalizerStatement.{u} := by
  intro S G P L i l hG hi hl
  let : IsAffineHom P.X.hom := hi.isAffineHom
  apply RelativeLevi.normalizer_eq_of_geometricFiber l hl.isClosedSubgroup hi.smooth hl.smooth
  intro s
  let d := RelativeLevi.geometricComplement hG hi hl s
  let : IsIso (subgroupMultiplication (RelativeLevi.geometricFiberHom l s) d.radicalHom) :=
    d.multiplication
  exact RelativeLevi.normalizer_eq_of_field_radical (RelativeLevi.geometricFiberHom i s)
    (RelativeLevi.geometricFiberHom l s) d.radicalHom d.ambientReductive d.parabolic
    d.unipotentRadical

end Langlands.GroupScheme
