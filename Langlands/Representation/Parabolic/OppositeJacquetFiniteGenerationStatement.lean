import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite generation of normalized opposite Jacquet modules

Casselman (1995), Theorem 3.3.1, specialized to the actual opposite block
parabolic of a p-adic general linear group and its normalized Jacquet action.
This module defines the proposition and supplies no proof.
-/

namespace Langlands.Parabolic

universe uF uV

/-- The actual normalized opposite Jacquet module of a smooth, finitely
generated complex representation of `GL_n(F)` is finitely generated over
the complex group algebra of its actual block Levi. -/
def OppositeJacquetFiniteGenerationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      IsSmooth A.ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule →
      Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
        (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ.asModule

end Langlands.Parabolic
