import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Mathlib.RepresentationTheory.Irreducible

/-!
# Descent of σ-discrete series on regular test functions

The ordinary and twisted simple trace formulas yield a local trace identity on concordant
test functions supported in the regular sets, with ordinary support restricted to matrices
whose determinant is a norm. See Henniart–Lemaire (2011), II.6.13 and II.6.16–II.6.17,
printed pp. 129–132, and Arthur–Clozel (1989), Chapter 1, §6.3, printed pp. 54–57.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Langlands.JacquetLanglands

section RegularLift

universe uF uE uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type uE} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ}
  [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [TotallyDisconnectedSpace (GeneralLinear n F)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The distributional identity of `IsSigmaLift` restricted to concordant test functions
`φ` and `f` supported in the σ-regular and regular semisimple sets respectively, with the
determinant of each point in the support of `f` in the image of the norm on units. The
constant `c` is nonzero and works for every Haar pair.

See Henniart–Lemaire I.2.5, II.2.7 and II.6.13, and Arthur–Clozel I §6.3, printed p. 57. -/
def IsRegularSigmaLift (σ : E ≃ₐ[F] E) (l : ℕ) (π : Representation ℂ (GeneralLinear n F) V)
    (hπ : IsAdmissible π) (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ)
    (A : SigmaIntertwiner σ n τ) (c : ℂ) : Prop :=
  c ≠ 0 ∧
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
      AreConcordant σ l μF μE φ f → IsSigmaRegularSupported σ l φ → IsRegularSupported f →
      (∀ g : GeneralLinear n F, f g ≠ 0 →
        GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : E →* F)).range) →
        twistedDistribution μE τ hτ A.toLinearMap φ = c * Character.distribution μF π hπ f

end RegularLift

/-- For a cyclic field extension `E/F` of any degree over a nonarchimedean local field `F`
of characteristic zero, every σ-discrete series `ρ` of `GL_n(E)` and every σ-intertwiner `A`
admit an irreducible admissible square-integrable `π` of `GL_n(F)` on a space in `Type uV`
and a constant `c` satisfying `IsRegularSigmaLift σ l π hπ ρ hρ A c`.

See Henniart–Lemaire II.6.16–II.6.17, printed pp. 131–132, and Arthur–Clozel I, Theorem 6.2 (b)
and §6.3. -/
def SigmaDiscreteRegularDescentStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l),
    haveI : Module.Finite F E := hσ.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n E) W) (hρ : IsAdmissible ρ),
      IsSigmaDiscreteSeries σ n ρ → ∀ A : SigmaIntertwiner σ n ρ,
      ∃ (V : Type uV) (_ : AddCommGroup V) (_ : Module ℂ V)
        (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π) (c : ℂ),
        π.IsIrreducible ∧ JacquetLanglands.IsSquareIntegrable π ∧
          IsRegularSigmaLift σ l π hπ ρ hρ A c

end Langlands.BaseChange
