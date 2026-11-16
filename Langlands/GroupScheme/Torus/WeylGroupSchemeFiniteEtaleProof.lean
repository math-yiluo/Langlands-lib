import Langlands.GroupScheme.Torus.WeylGroupSchemeFiniteEtaleStatement
import Langlands.GroupScheme.Torus.SmoothAffineWeylQuotientProof
import Langlands.GroupScheme.Torus.WeylQuotientFinitenessReduction
import Langlands.AlgebraicGeometry.EtaleLocalCardinalityFinitenessProof

/-! # The Weyl group scheme of a maximal torus is finite étale -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The actual normalizer/centralizer quotient of a maximal relative torus in
a reductive group scheme is finite étale over every base scheme. -/
theorem weylGroupSchemeFiniteEtale : WeylGroupSchemeFiniteEtaleStatement.{u} := by
  intro S G hG T t hT ht hmax
  obtain ⟨N, n, Z, z, W, q, hnclosed, hn, hzclosed, hz, hsep, hqc, het,
    hqflat, hqsurj, hqfp, hker⟩ :=
    smoothAffineTorusWeylQuotient S G hG.smooth hG.isAffineHom T t hT ht
  have hfinite : IsFinite W.X.hom :=
    weylQuotientFinitenessReduction
      Langlands.AlgebraicGeometry.etaleLocalCardinalityFiniteness
      S G hG T t hT ht hmax N n W q hnclosed hn hqc hsep het hqsurj hker
  exact ⟨N, n, Z, z, W, q, hnclosed, hn, hzclosed, hz, hfinite, het,
    hqflat, hqsurj, hqfp, hker⟩

end Langlands.GroupScheme
