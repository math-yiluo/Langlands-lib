import Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityProof

/-! # Proof: point surjectivity for z-extensions -/

universe u

namespace Langlands.GroupScheme

/-- **Point surjectivity for z-extensions.** For every field `k`, every field extension `K/k`
and every z-extension `1 → Z → H → G → 1` over `k`, the map `H(K) → G(K)` is surjective.
This is the general induced-torus quotient theorem `inducedTorusQuotientPointSurjectivity`,
specialized by `zExtensionPointSurjectivity_of_inducedTorusQuotient`. -/
theorem zExtensionPointSurjectivity : ZExtensionPointSurjectivityStatement.{u} :=
  zExtensionPointSurjectivity_of_inducedTorusQuotient inducedTorusQuotientPointSurjectivity

end Langlands.GroupScheme
