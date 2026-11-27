import Langlands.JacquetLanglands.Relation

/-!
# Existence of the Jacquet–Langlands transfer of a square-integrable representation

The proposition `SquareIntegrableTransferExistenceStatement`, not proved here: over a
nonarchimedean local field of characteristic zero, every irreducible representation of `GL_n(F)`
that is square-integrable modulo the centre, with unitary central character, has a
Jacquet–Langlands partner on `Dˣ`, for every central division algebra `D` of dimension `n^2` over
`F`. This is the surjectivity of the bijection `E²(Dˣ) → E²(GL_n(F))` of the Théorème principal of
Deligne–Kazhdan–Vignéras, restricted to inputs with unitary central character: DKV's `E²` also
contains representations with non-unitary central character.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW

/-- Existence of the Jacquet–Langlands transfer of a square-integrable representation
(Deligne–Kazhdan–Vignéras, characteristic zero): for every nonarchimedean local field `F` of
characteristic zero, every finite-dimensional central division algebra `D` over `F` with its
module topology and every `n` with `Module.finrank F D = n ^ 2`, every irreducible smooth
representation `A` of `GL_n(F)` (carrier in `Type uV`) that is square-integrable modulo the
centre (`IsSquareIntegrable`, which includes a unitary central character) has a smooth
representation `B` of `Dˣ` (carrier in `Type uW`) with `IsJacquetLanglandsSmoothPair F D n A B`. -/
def SquareIntegrableTransferExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
      ∀ A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F), A.representation.IsIrreducible →
        IsSquareIntegrable A.representation →
          ∃ B : SmoothRep.{0, u, uW} ℂ Dˣ, IsJacquetLanglandsSmoothPair F D n A B

end Langlands.JacquetLanglands
