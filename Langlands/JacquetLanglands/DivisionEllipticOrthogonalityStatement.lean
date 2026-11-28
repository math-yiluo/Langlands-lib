import Langlands.JacquetLanglands.Relation
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Statement: elliptic orthogonality of square-integrable characters, read on `Dˣ / Fˣ`

For a nonarchimedean local field `F` of characteristic zero and a central division algebra `D`
of dimension `n^2` over `F`: the characters of two irreducible square-integrable representations
`ρ`, `π` of `GL_n(F)` with the same unitary central character, transferred to the regular units
of `D` through the correspondence of regular elliptic elements, have the pairing
`∫_{Dˣ/Fˣ} θ_ρ · conj θ_π dν = ν(Dˣ/Fˣ)` if `ρ ≅ π` and `0` otherwise, for every Haar measure
`ν` on the compact quotient of `Dˣ` by its centre. This is Clozel's orthogonality relation
(Clozel 1991, Theorem 3, printed p. 110) transported to `Dˣ` by the isometry of Badulescu 2002,
§6 (Annexe), printed pp. 745–746, and the Weyl integration formula on `Dˣ`. The statement is not
proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory

universe u uV

/-- Elliptic orthogonality of square-integrable characters of `GL_n(F)`, read on the compact
quotient of `Dˣ` by its centre (Clozel 1991, Theorem 3, transported to `Dˣ` as in Badulescu 2002,
§6): let `F` be a nonarchimedean local field of characteristic zero, `D` a central division
algebra over `F` of dimension `n^2` with its module topology, and `ν` a Haar measure on
`Dˣ ⧸ Z(Dˣ)` (Borel σ-algebra). Let `ρ`, `π` be irreducible square-integrable representations of
`GL_n(F)` (carriers in `Type uV`) whose unitary central characters `cρ`, `cπ` are equal, and let
`Θρ`, `Θπ` give their character values at the regular elliptic elements. Then the function `p`
on `Dˣ ⧸ Z(Dˣ)` with `p (g' Z) = Θρ g * conj (Θπ g)` whenever `g` corresponds to `g'`, and
`p (g' Z) = 0` at the units `g'` that are not regular, exists, is `ν`-integrable, and
`∫ p dν` is `(ν univ).toReal` if `ρ ≅ π` and `0` otherwise. -/
def DivisionEllipticOrthogonalityStatement : Prop := by
  classical
  exact ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    haveI := generalLinear_t2Space F n
    haveI := generalLinear_locallyCompactSpace F n
    haveI := generalLinear_totallyDisconnectedSpace F n
    haveI := units_isTopologicalGroup F D
    letI : MeasurableSpace (Dˣ ⧸ Subgroup.center Dˣ) := borel _
    ∀ (ν : Measure (Dˣ ⧸ Subgroup.center Dˣ)) [ν.IsHaarMeasure]
      {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n F) V) (π : Representation ℂ (GeneralLinear n F) W)
      (hρ : IsSquareIntegrable ρ) (hπ : IsSquareIntegrable π),
      ρ.IsIrreducible → π.IsIrreducible →
      ∀ (cρ : UnitaryCentralCharacter ρ) (cπ : UnitaryCentralCharacter π),
        cρ.character = cπ.character →
        ∀ (Θρ Θπ : {g : GeneralLinear n F // IsRegularElliptic g} → ℂ),
          (∀ g, HasCharacterValue ρ hρ.isAdmissible g.val (Θρ g)) →
          (∀ g, HasCharacterValue π hπ.isAdmissible g.val (Θπ g)) →
          ∃ p : Dˣ ⧸ Subgroup.center Dˣ → ℂ,
            (∀ (g : GeneralLinear n F) (g' : Dˣ) (h : Corresponds F D g g'),
              p (QuotientGroup.mk g') = Θρ ⟨g, h.1⟩ * star (Θπ ⟨g, h.1⟩)) ∧
            (∀ g' : Dˣ, ¬ IsRegular F D g' → p (QuotientGroup.mk g') = 0) ∧
            Integrable p ν ∧
            (∫ q, p q ∂ν) = if Nonempty (ρ.Equiv π) then (ν Set.univ).toReal else 0

end Langlands.JacquetLanglands
