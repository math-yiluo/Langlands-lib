import Langlands.Representation.Exponents.ProductLeviCuspidalLocalizationConditional
import Langlands.Representation.Geometric.ProductLeviGeometricLemmaProof

/-!
# Product-Levi cuspidal localization

The published product-Levi geometric lemma discharges the hypothesis of the
conditional derivation, which proves
`GLProductLeviCuspidalLocalizationStatement`.
-/

namespace Langlands.ProductLeviCuspidalLocalization

universe uF uV uM

/-- A Levi-cuspidal irreducible subquotient of a flattened inner opposite
Jacquet module of a parabolically induced representation inside `B.Levi` is a
subquotient of the transport, by a minimal representative in `blockWeyl B`, of
an inner opposite Jacquet module of the middle representation. -/
theorem glProductLeviCuspidalLocalization :
    GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM} :=
  productLeviCuspidalLocalization_of_geometricLemma
    Geometric.padicProductLeviGeometricLemma.{uF, uM}

end Langlands.ProductLeviCuspidalLocalization
