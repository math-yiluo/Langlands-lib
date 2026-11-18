import Langlands.GroupScheme.Reductive.SmoothAntiAffineRadicalExtension
import Langlands.GroupScheme.AntiAffineQuotientExistenceProof

/-! # Represented radicals under algebraically closed field extension -/

universe u

namespace Langlands.GroupScheme

/-- An arbitrary algebraically closed field extension preserves every supplied
represented unipotent radical of a smooth ambient group scheme. -/
theorem smoothAlgebraicallyClosedUnipotentRadicalExtension :
    SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement.{u} :=
  smoothAlgebraicallyClosedUnipotentRadicalExtension_of_antiAffineQuotientExistence
    antiAffineQuotientExistence

end Langlands.GroupScheme
