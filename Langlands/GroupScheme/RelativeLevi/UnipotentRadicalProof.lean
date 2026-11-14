import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalStatement
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalExistence
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.DynamicProof

/-! # Existence and uniqueness of relative unipotent radicals -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every relative parabolic has a relative unipotent radical, unique as a
subgroup functor on all test schemes. -/
theorem relativeUnipotentRadical : RelativeUnipotentRadicalStatement.{u} := by
  intro S G P i hG hP
  let : IsAffineHom P.X.hom := hP.isAffineHom
  obtain ⟨cover, hcover⟩ := relativeParabolicEtaleLocalDynamic S G P i hG hP
  let R := RelativeLevi.radicalOfEtaleDynamicCover dynamicRelativeLevi hG i cover hcover
  refine ⟨R.1, R.2.val, R.2.property, ?_⟩
  intro U' r' hr'
  exact RelativeLevi.radical_range_eq_of_etale_dynamicCover dynamicRelativeLevi hG i cover hcover
    r' R.2.val hr' R.2.property

end Langlands.GroupScheme
