import Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement
import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FiniteFieldCharts
import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.RingPointCharts

/-!
# The algebraic-space form of Conrad's Lemma 4.6 from the scheme estimates in families

The base `B` has finitely many affine scheme charts, locally of finite type over `ℤ`, through
which every point of `B` with values in a finite field factors
(`SpaceFamily.FiniteFieldCharts.exists_finiteField_charts`). Over each chart the family
estimates give one constant (`SpaceFamily.spaceUniformLangWeil_of_charts`).
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

open SpaceFamily

/-- The uniform Lang–Weil estimate in families of schemes and the uniform point-count upper bound
in families imply the algebraic-space form of Conrad's Lemma 4.6. -/
theorem spaceUniformLangWeilOfFamily : SpaceUniformLangWeilOfFamilyStatement.{u} := by
  intro hFLW hFPU B Y f d hqs hft ⟨U, V, a, b, φ, hae, has, hbe, hφ, hsq⟩ hsep hqc hsurj hconn
  obtain ⟨n, M, t, hM, hMft, -, hpts⟩ :=
    FiniteFieldCharts.exists_finiteField_charts B hqs hft
  exact spaceUniformLangWeil_of_charts hFLW hFPU f d a b φ hae has hbe hφ hsq hsep hqc hsurj
    hconn M t hM hMft hpts

end Langlands.AlgebraicGeometry.LangWeil
