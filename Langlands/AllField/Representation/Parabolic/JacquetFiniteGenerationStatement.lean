import Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement
import Langlands.AllField.Representation.Jacquet.Parabolic
/-!
# Finite generation of normalized standard Jacquet modules

The finite-generation assertion of Casselman (1995), Theorem 3.3.1,
specialized to actual local-field general linear groups and the normalized action.
This module states the assertion as a proposition; it does not prove it.
-/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetFiniteGenerationStatement
open Langlands.AllField.Parabolic

universe uF uV

/-- A smooth representation of `GL_n(F)` that is finitely generated over its
complex group algebra has a finitely generated normalized standard Jacquet
module over the complex group algebra of the actual block Levi. -/
def NormalizedJacquetFiniteGenerationStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V),
      IsSmooth ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F)) ρ.asModule →
      Module.Finite (MonoidAlgebra ℂ (B.Levi F))
        (T.normalizedJacquet B ρ).asModule

end Langlands.AllField.Parabolic
