import Langlands.LocalField.RelativeIntegers
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions

/-! # The NYLL unramified class for supplied local-field data -/

namespace Langlands.LocalClassField.NYLL

universe u v

open scoped ValuativeRel

/-- For supplied realizations and any compatibility of their valuations, the
extension valuation ring is finite over the base valuation ring for Mathlib's
integer algebra. For every such finiteness instance, NYLL's unramified class
holds exactly when the supplied relative ramification index, computed with the
explicit supplied integer scalars, is one. -/
def SuppliedUnramifiedValuedExtensionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    letI := TF.topology
    letI := TF.valuativeRel
    letI := TF.localField
    letI := TE.topology
    letI := TE.valuativeRel
    letI := TE.localField
    ∀ [Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
        (ValuativeRel.valuation E.Carrier)],
      Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier] ∧
        ∀ [Module.Finite 𝒪[F.Carrier] 𝒪[E.Carrier]],
          Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
              F.Carrier E.Carrier ↔
            (letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TE
             (IsLocalRing.maximalIdeal TE.Integers).ramificationIdx TF.Integers = 1)

end Langlands.LocalClassField.NYLL
