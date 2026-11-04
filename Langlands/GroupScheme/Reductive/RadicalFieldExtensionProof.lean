import Langlands.GroupScheme.Reductive.RadicalFieldExtension.KSide
import Langlands.GroupScheme.Reductive.RadicalFieldExtension.RationalSide

/-! # Trivial unipotent radical under extension of algebraically closed fields: proof -/

universe u

namespace Langlands.GroupScheme

/-- Base change along an extension of algebraically closed fields preserves the triviality of
the unipotent radical of a smooth connected affine group scheme. -/
theorem algebraicallyClosedRadicalFieldExtensionStatement :
    AlgebraicallyClosedRadicalFieldExtensionStatement.{u} :=
  RadicalFieldExtension.algebraicallyClosedRadicalFieldExtensionStatement_of_rationalSide
    RadicalFieldExtension.rationalSide

end Langlands.GroupScheme
