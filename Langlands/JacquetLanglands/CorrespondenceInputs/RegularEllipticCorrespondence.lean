import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Regular elliptic elements of `GL_n(F)` correspond to units of `D`

The proposition `RegularEllipticCorrespondenceStatement`, not proved here: for a nonarchimedean
local field `F` and a central division algebra `D` of dimension `n^2` over `F`, every regular
elliptic element of `GL_n(F)` corresponds to a unit of `D`, that is, its characteristic
polynomial is the reduced characteristic polynomial of a regular unit of `D`. This is the
surjectivity of the bijection between regular elliptic conjugacy classes of `Dˣ` and of
`GL_n(F)` recalled by Deligne–Kazhdan–Vignéras.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u

/-- Every regular elliptic element of `GL_n(F)` corresponds to a unit of a central division
algebra `D` of dimension `n^2` over a nonarchimedean local field `F`: for every regular elliptic
`g : GeneralLinear n F` there is `g' : Dˣ` with `Corresponds F D g g'`, so `g'` is regular and the
characteristic polynomial of `g` is the reduced characteristic polynomial of `g'`. No topology on
`D` is involved. -/
def RegularEllipticCorrespondenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    (n : ℕ), Module.finrank F D = n ^ 2 →
      ∀ g : GeneralLinear n F, IsRegularElliptic g → ∃ g' : Dˣ, Corresponds F D g g'

end Langlands.JacquetLanglands
