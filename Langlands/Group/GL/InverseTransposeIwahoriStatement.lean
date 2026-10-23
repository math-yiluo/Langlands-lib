import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Group.GL.Maps

/-!
# Inverse-transpose transport of block Iwahori data

Proposition definitions stating how the published inverse transpose
`g ↦ (g⁻¹)ᵀ` acts on the actual block radicals, the common Levi, block scalars,
compact open subgroups and the published weak-chamber block Iwahori
factorization. They contain no proofs of these assertions.
-/

namespace Langlands.GeneralLinear.BlockShape

universe uF u

section Ring

variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

/-- Inverse transpose maps the actual upper radical onto the actual opposite radical. -/
def InverseTransposeUnipotentClause : Prop :=
  (B.unipotentSubgroup R).map (inverseTranspose n R).toMonoidHom =
    B.oppositeUnipotentSubgroup R

/-- Inverse transpose maps the actual opposite radical onto the actual upper radical. -/
def InverseTransposeOppositeUnipotentClause : Prop :=
  (B.oppositeUnipotentSubgroup R).map (inverseTranspose n R).toMonoidHom =
    B.unipotentSubgroup R

/-- Inverse transpose maps the embedded common Levi onto itself. -/
def InverseTransposeLeviClause : Prop :=
  (B.leviSubgroup R).map (inverseTranspose n R).toMonoidHom = B.leviSubgroup R

/-- Inverse transpose sends every block-scalar matrix to its inverse. -/
def InverseTransposeBlockScalarClause : Prop :=
  ∀ a : Fin B.length → Rˣ,
    inverseTranspose n R (B.blockScalar R a) = (B.blockScalar R a)⁻¹

end Ring

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The open comap of a compact open subgroup by the supplied continuous inverse
transpose is compact. -/
def InverseTransposeCompactComapClause (n : ℕ) : Prop :=
  letI := T.topology
  ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
    IsCompact (K : Set (GeneralLinear n F.Carrier)) →
      IsCompact ((K.comap (T.generalLinearInverseTranspose n).toMonoidHom
          (T.generalLinearInverseTranspose n).continuous :
        OpenSubgroup (GeneralLinear n F.Carrier)) : Set (GeneralLinear n F.Carrier))

/-- The published weak-chamber block Iwahori factorization, for the same shape,
passes from an open subgroup to its comap by the supplied continuous inverse
transpose. -/
def InverseTransposeIwahoriFactorizationClause {n : ℕ}
    (B : GeneralLinear.BlockShape n) : Prop :=
  letI := T.topology
  ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
    B.HasBlockIwahoriFactorization T K →
      B.HasBlockIwahoriFactorization T
        (K.comap (T.generalLinearInverseTranspose n).toMonoidHom
          (T.generalLinearInverseTranspose n).continuous)

end Padic

/-- Inverse-transpose transport of the actual block Iwahori data, for every
supplied p-adic realization, every rank and every block shape. -/
def InverseTransposeIwahoriStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n),
    B.InverseTransposeUnipotentClause F.Carrier ∧
    B.InverseTransposeOppositeUnipotentClause F.Carrier ∧
    B.InverseTransposeLeviClause F.Carrier ∧
    B.InverseTransposeBlockScalarClause F.Carrier ∧
    InverseTransposeCompactComapClause T n ∧
    B.InverseTransposeIwahoriFactorizationClause T

end Langlands.GeneralLinear.BlockShape
