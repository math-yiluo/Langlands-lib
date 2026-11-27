import Langlands.JacquetLanglands.Relation
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Existence of the inverse Jacquet–Langlands transfer for unitary central characters

The proposition `UnitaryDivisionTransferExistenceStatement`, not proved here: over a
nonarchimedean local field of characteristic zero, every irreducible admissible representation
of `Dˣ` whose central character is unitary has a Jacquet–Langlands partner on `GL_n(F)`, for
every central division algebra `D` of dimension `n^2` over `F`. This is the existence of the
image of every class of `E²(Dˣ)` under the bijection of the Théorème principal of
Deligne–Kazhdan–Vignéras.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW

open Langlands.Classification

/-- Existence of the inverse Jacquet–Langlands transfer for representations of `Dˣ` with unitary
central character (Deligne–Kazhdan–Vignéras, characteristic zero): for every nonarchimedean local
field `F` of characteristic zero, every finite-dimensional central division algebra `D` over `F`
with its module topology and every `n` with `Module.finrank F D = n ^ 2`, every irreducible
admissible smooth representation `B` of `Dˣ` (carrier in `Type uW`) on which the centre `Fˣ`,
embedded by `Units.map (algebraMap F D)`, acts through a character `ω` of absolute value one has a
smooth representation `A` of `GL_n(F)` (carrier in `Type uV`) with
`IsJacquetLanglandsSmoothPair F D n A B`. -/
def UnitaryDivisionTransferExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
      ∀ B : SmoothRep.{0, u, uW} ℂ Dˣ, B.representation.IsIrreducible →
        IsAdmissible B.representation →
        (∃ ω : Fˣ →* ℂˣ,
          HasScalarCharacter B.representation (Units.map (algebraMap F D : F →* D)) ω ∧
            ∀ z : Fˣ, ‖(ω z : ℂ)‖ = 1) →
          ∃ A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F), IsJacquetLanglandsSmoothPair F D n A B

end Langlands.JacquetLanglands
