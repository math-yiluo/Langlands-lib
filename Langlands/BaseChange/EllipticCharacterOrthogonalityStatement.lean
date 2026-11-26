import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.RepresentationTheory.Irreducible

/-! # Elliptic character orthogonality for `GL_n` -/

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

/-- Clozel's elliptic orthogonality relations (Theorem 3) for `GL_n(F)`, in common-measure
form: one measure on the central quotient realizes the elliptic pairing of every two
irreducible square-integrable representations with the same unitary central character.
The product of the two character functions, conjugate linear in the second argument, is
extended by zero away from the regular elliptic set and then descends to the quotient.
The integral is `1` for equivalent representations and `0` for inequivalent
representations. -/
def EllipticCharacterOrthogonalityStatement.{u, uV} : Prop := by
  classical
  exact ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    let G := GeneralLinear n F
    let Z := Subgroup.center G
    letI := centralQuotientMeasurableSpace F n
    ∃ ν : Measure (G ⧸ Z),
      ∀ {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
        (ρ : Representation ℂ G V) (π : Representation ℂ G W)
        (hρ : IsSquareIntegrable ρ) (hπ : IsSquareIntegrable π),
        ρ.IsIrreducible → π.IsIrreducible →
        ∀ (cρ : UnitaryCentralCharacter ρ) (cπ : UnitaryCentralCharacter π),
          cρ.character = cπ.character →
          ∀ (Θρ Θπ : {g : G // IsRegularElliptic g} → ℂ),
            (∀ g, HasCharacterValue ρ hρ.isAdmissible g.val (Θρ g)) →
            (∀ g, HasCharacterValue π hπ.isAdmissible g.val (Θπ g)) →
            ∃ p : G ⧸ Z → ℂ,
              (∀ g : G, p (QuotientGroup.mk g) =
                if h : IsRegularElliptic g
                then Θρ ⟨g, h⟩ * star (Θπ ⟨g, h⟩)
                else 0) ∧
              Integrable p ν ∧
              (∫ q, p q ∂ν) = if Nonempty (ρ.Equiv π) then 1 else 0

end Langlands.BaseChange
