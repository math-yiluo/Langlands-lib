import Langlands.JacquetLanglands.Relation

/-!
# Analytic input for the Jacquet–Langlands character identity

Two propositions, not proved here, that the sources use when they evaluate characters at
points: Harish-Chandra's theorem that the character of an irreducible admissible representation
of `GL_n(F)` has a value at every regular semisimple element, and the finite-dimensionality of
irreducible smooth representations of `Dˣ`. Under them, the Jacquet–Langlands relation is
shown to be the source's identity `χ_π(g) = (-1)^(n-1) χ_π'(g')`, with `χ_π'(g') = trace π'(g')`.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW

section Statements

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Harish-Chandra's regularity theorem, in the form used here: the character of every
irreducible admissible representation of `GL_n(F)` (carrier in `Type uV`) has a value at every
regular semisimple element. -/
def HasRegularSemisimpleCharacterValues (n : ℕ) : Prop :=
  haveI := generalLinear_t2Space F n
  haveI := generalLinear_locallyCompactSpace F n
  haveI := generalLinear_totallyDisconnectedSpace F n
  ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GeneralLinear n F) V)
    (hρ : IsAdmissible ρ), ρ.IsIrreducible →
    ∀ g : GeneralLinear n F, IsRegularSemisimple g → ∃ c : ℂ, HasCharacterValue ρ hρ g c

end Statements

/-- Every irreducible smooth representation of `Dˣ` (carrier in `Type uW`) is
finite-dimensional, for a central division algebra `D` of finite dimension over `F` with its
module topology. The conclusion does not mention `F`; the hypotheses on `D` do. -/
def IrreducibleDivisionUnitsFiniteDimensional (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (D : Type u) [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] [TopologicalSpace D]
    [IsModuleTopology F D] : Prop :=
  ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Dˣ W),
    IsSmooth ρ' → ρ'.IsIrreducible → FiniteDimensional ℂ W

section Consequences

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {D : Type u} [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] {n : ℕ}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GeneralLinear n F) V} {ρ' : Representation ℂ Dˣ W}

attribute [local instance] generalLinear_t2Space generalLinear_locallyCompactSpace
  generalLinear_totallyDisconnectedSpace

/-- Irreducible smooth representations of `Dˣ` are admissible, given finite-dimensionality. -/
theorem IrreducibleDivisionUnitsFiniteDimensional.isAdmissible
    (hD : IrreducibleDivisionUnitsFiniteDimensional.{u, uW} F D) (hs : IsSmooth ρ')
    (hirr : ρ'.IsIrreducible) : IsAdmissible ρ' :=
  haveI := hD ρ' hs hirr
  isAdmissible_of_finiteDimensional hs

/-- Given finite-dimensionality of irreducible smooth representations of `Dˣ`, the
Jacquet–Langlands relation says that the character of `ρ` has the value
`(-1)^(n-1) trace ρ'(g')` at every regular elliptic `g` corresponding to `g'`. -/
theorem isJacquetLanglandsPair_iff_trace
    (hD : IrreducibleDivisionUnitsFiniteDimensional.{u, uW} F D) :
    IsJacquetLanglandsPair F D n ρ ρ' ↔
      Module.finrank F D = n ^ 2 ∧ ρ.IsIrreducible ∧ IsEssentiallySquareIntegrable ρ ∧
        ρ'.IsIrreducible ∧ IsSmooth ρ' ∧
        ∃ hρ : IsAdmissible ρ, ∀ (g : GeneralLinear n F) (g' : Dˣ), Corresponds F D g g' →
          HasCharacterValue ρ hρ g ((-1) ^ (n - 1) * LinearMap.trace ℂ W (ρ' g')) := by
  have := units_isTopologicalGroup F D
  have := units_t2Space F D
  have := units_locallyCompactSpace F D
  have := units_totallyDisconnectedSpace F D
  constructor
  · rintro ⟨hdim, hirr, hess, hirr', hρ, hρ', hc⟩
    have := hD ρ' hρ'.1 hirr'
    refine ⟨hdim, hirr, hess, hirr', hρ'.1, hρ, fun g g' hg => ?_⟩
    obtain ⟨c, hcg, hcg'⟩ := hc g g' hg
    rwa [(hasCharacterValue_trace ρ' hρ' g').unique hcg']
  · rintro ⟨hdim, hirr, hess, hirr', hs, hρ, hc⟩
    have := hD ρ' hs hirr'
    exact ⟨hdim, hirr, hess, hirr', hρ, isAdmissible_of_finiteDimensional hs,
      fun g g' hg => ⟨_, hc g g' hg, hasCharacterValue_trace ρ' _ g'⟩⟩

/-- Given Harish-Chandra's regularity theorem and finite-dimensionality of irreducible smooth
representations of `Dˣ`, the Jacquet–Langlands relation is the source's character identity:
the value `χ_ρ(g)` of the character of `ρ` at every regular elliptic `g` corresponding to `g'`
equals `(-1)^(n-1) trace ρ'(g')`. -/
theorem isJacquetLanglandsPair_iff_of_regularity
    (hHC : HasRegularSemisimpleCharacterValues.{u, uV} F n)
    (hD : IrreducibleDivisionUnitsFiniteDimensional.{u, uW} F D) :
    IsJacquetLanglandsPair F D n ρ ρ' ↔
      Module.finrank F D = n ^ 2 ∧ ρ.IsIrreducible ∧ IsEssentiallySquareIntegrable ρ ∧
        ρ'.IsIrreducible ∧ IsSmooth ρ' ∧
        ∀ (hρ : IsAdmissible ρ) (g : GeneralLinear n F) (g' : Dˣ), Corresponds F D g g' →
          ∀ a : ℂ, HasCharacterValue ρ hρ g a →
            a = (-1) ^ (n - 1) * LinearMap.trace ℂ W (ρ' g') := by
  rw [isJacquetLanglandsPair_iff_trace hD]
  constructor
  · rintro ⟨hdim, hirr, hess, hirr', hs, hρ, hc⟩
    exact ⟨hdim, hirr, hess, hirr', hs, fun _ g g' hg a ha => ha.unique (hc g g' hg)⟩
  · rintro ⟨hdim, hirr, hess, hirr', hs, hc⟩
    have hρ := hess.isAdmissible
    refine ⟨hdim, hirr, hess, hirr', hs, hρ, fun g g' hg => ?_⟩
    obtain ⟨a, ha⟩ := hHC ρ hρ hirr g hg.1.isRegularSemisimple
    rwa [← hc hρ g g' hg a ha]

end Consequences

end Langlands.JacquetLanglands
