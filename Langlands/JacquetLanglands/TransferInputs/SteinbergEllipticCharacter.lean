import Langlands.JacquetLanglands.Relation

/-!
# The Steinberg character on the regular elliptic set

The proposition `SteinbergEllipticCharacterStatement`, not proved here: for every
nonarchimedean local field `F` of characteristic zero and every `n ≥ 1`, some irreducible
square-integrable representation of `GL_n(F)` (the Steinberg representation) has the constant
character value `(-1)^(n-1)` at every regular elliptic element. Deligne–Kazhdan–Vignéras use
this value to fix the sign of the Jacquet–Langlands correspondence (§B.1.h).
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV

/-- The Steinberg character on the regular elliptic set (characteristic zero): for every
nonarchimedean local field `F` of characteristic zero and every `n > 0` there is an irreducible
smooth representation `St` of `GL_n(F)` (carrier in `Type uV`) that is square-integrable modulo
the centre and whose character has the value `(-1)^(n-1)` at every regular elliptic element of
`GL_n(F)`. -/
def SteinbergEllipticCharacterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ), 0 < n →
    haveI := generalLinear_t2Space F n
    haveI := generalLinear_locallyCompactSpace F n
    haveI := generalLinear_totallyDisconnectedSpace F n
    ∃ (St : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F))
      (hSt : IsSquareIntegrable St.representation),
      St.representation.IsIrreducible ∧
        ∀ g : GeneralLinear n F, IsRegularElliptic g →
          HasCharacterValue St.representation hSt.isAdmissible g ((-1) ^ (n - 1))

end Langlands.JacquetLanglands
