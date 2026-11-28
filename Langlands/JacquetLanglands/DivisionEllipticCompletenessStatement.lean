import Langlands.JacquetLanglands.Relation
import Langlands.Representation.Classification.ConstituentRelations
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Statement: completeness of the characters of `Dˣ` against square-integrable characters

For a nonarchimedean local field `F` of characteristic zero, a central division algebra `D` of
dimension `n^2` over `F` and an irreducible square-integrable representation `ρ` of `GL_n(F)` on
which the scalar matrices act through the character `ω` of `Fˣ`: some irreducible admissible
representation `B` of `Dˣ` on which `Fˣ` acts through `ω` has a character that is not orthogonal,
on the compact quotient `Dˣ / Fˣ`, to the character of `ρ` transferred to the regular units of `D`.
This is the completeness of the characters of the group `Dˣ`, compact modulo its centre
(Deligne–Kazhdan–Vignéras 1984, B.1.g, printed pp. 81–82; Badulescu 2002, §6 (Annexe), printed
p. 745), applied to the transferred character of `ρ`, which is nonzero by Clozel's orthogonality
relations. The statement is not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory
open Langlands.Classification (HasScalarCharacter)

universe u uV uW

/-- Completeness of the characters of `Dˣ`, tested on the transferred character of a
square-integrable representation of `GL_n(F)` (DKV, B.1.g; Badulescu 2002, §6): let `F` be a
nonarchimedean local field of characteristic zero, `D` a central division algebra over `F` of
dimension `n^2` with its module topology, and `ν` a Haar measure on `Dˣ ⧸ Z(Dˣ)` (Borel
σ-algebra). Let `ρ` be an irreducible square-integrable representation of `GL_n(F)` (carrier in
`Type uV`) on which the scalar matrices act through `ω : Fˣ →* ℂˣ`, and let `Θρ` give its
character values at the regular elliptic elements. Then there are a smooth representation `B` of
`Dˣ` (carrier in `Type uW`), admissible and irreducible, on which `Fˣ ⊆ Dˣ` acts through `ω`, a
function `ΘB` giving the character values of `B` at every unit, and a `ν`-integrable function `p`
on `Dˣ ⧸ Z(Dˣ)` with `p (g' Z) = Θρ g * conj (ΘB g')` whenever `g` corresponds to `g'`,
`p (g' Z) = 0` at the units `g'` that are not regular, and `∫ p dν ≠ 0`. -/
def DivisionEllipticCompletenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    haveI := generalLinear_t2Space F n
    haveI := generalLinear_locallyCompactSpace F n
    haveI := generalLinear_totallyDisconnectedSpace F n
    haveI := units_isTopologicalGroup F D
    haveI := units_t2Space F D
    haveI := units_locallyCompactSpace F D
    haveI := units_totallyDisconnectedSpace F D
    letI : MeasurableSpace (Dˣ ⧸ Subgroup.center Dˣ) := borel _
    ∀ (ν : Measure (Dˣ ⧸ Subgroup.center Dˣ)) [ν.IsHaarMeasure]
      {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GeneralLinear n F) V)
      (hρ : IsSquareIntegrable ρ), ρ.IsIrreducible →
      ∀ ω : Fˣ →* ℂˣ, HasScalarCharacter ρ GeneralLinear.scalar ω →
      ∀ Θρ : {g : GeneralLinear n F // IsRegularElliptic g} → ℂ,
        (∀ g, HasCharacterValue ρ hρ.isAdmissible g.val (Θρ g)) →
        ∃ (B : SmoothRep.{0, u, uW} ℂ Dˣ) (hB : IsAdmissible B.representation),
          B.representation.IsIrreducible ∧
          HasScalarCharacter B.representation (Units.map (algebraMap F D : F →* D)) ω ∧
          ∃ ΘB : Dˣ → ℂ, (∀ g' : Dˣ, HasCharacterValue B.representation hB g' (ΘB g')) ∧
            ∃ p : Dˣ ⧸ Subgroup.center Dˣ → ℂ,
              (∀ (g : GeneralLinear n F) (g' : Dˣ) (h : Corresponds F D g g'),
                p (QuotientGroup.mk g') = Θρ ⟨g, h.1⟩ * star (ΘB g')) ∧
              (∀ g' : Dˣ, ¬ IsRegular F D g' → p (QuotientGroup.mk g') = 0) ∧
              Integrable p ν ∧ (∫ q, p q ∂ν) ≠ 0

end Langlands.JacquetLanglands
