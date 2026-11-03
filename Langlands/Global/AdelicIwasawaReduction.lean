import Langlands.Global.AdelicIwasawaAssembly
import Langlands.Global.InfinitePlaceIwasawaStatement
import Langlands.Global.FinitePlaceIwasawaStatement

/-! # Reduction of adelic Iwasawa existence to local and integral existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

/-- Conditional reduction of the exact adelic proposition to the archimedean
proposition, actual finite-completion existence, and the integral-family
proposition. Affineness follows from the original algebraic hypotheses. -/
theorem parabolicIwasawaStatement_of_archimedean_finite_integral
    (harch : InfinitePlaceGroupPoints.ParabolicIwasawaStatement.{u})
    (hfinite : FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u})
    (hintegral : IntegralIwasawaFamily.ExistenceStatement.{u}) :
    ParabolicIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffine P.X.left := isAffine_of_isAffineHom p.hom.hom.left
  obtain ⟨K, hK⟩ := hintegral F G hG P p hp
  apply exists_parabolicIwasawaCompact_of_local_integral F G P p ?_ K hK
  rintro (w | v)
  · obtain ⟨L, hcompact, hmaximal, hcover⟩ := harch F G hG P p hp w
    exact ⟨L, ⟨hcompact, hmaximal⟩, hcover⟩
  · exact hfinite F G hG P p hp v

end Langlands.Global.AdelicGroupPoints
