import Langlands.JacquetLanglands.DivisionMatching
import Langlands.JacquetLanglands.DivisionUnits
import Langlands.JacquetLanglands.Relation
import Langlands.Representation.Character.Basic
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: the Jacquet–Langlands trace identity for matching test functions

For a nonarchimedean local field `F` of characteristic zero, a central division algebra `D` of
dimension `n^2` over `F` and a Jacquet–Langlands pair `(ρ, ρ')`: if `f` on `GL_n(F)` is
supported in the regular elliptic set, `f'` on `Dˣ` is supported in the regular set and `f`
and `f'` match, then `trace ρ(f) = (-1)^(n-1) trace ρ'(f')` (Deligne–Kazhdan–Vignéras 1984,
B.2.a, printed p. 83, for `m = 1`). The statement is not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory
open HarmonicAnalysis (SchwartzBruhat)
open Langlands.BaseChange (IsEllipticSupported)

universe u uV uW

/-- The Jacquet–Langlands trace identity (DKV, B.2.a, for `m = 1`; the introduction, printed
p. 34): let `F` be a nonarchimedean local field of characteristic zero and `D` a central
division algebra over `F` of dimension `n^2`, with its module topology; give `GL_n(F)` and `Dˣ`
their Borel σ-algebras. For every Jacquet–Langlands pair `h : IsJacquetLanglandsPair F D n ρ ρ'`,
all Haar measures `μ` on `GL_n(F)` and `μ'` on `Dˣ`, and all `f ∈ C^∞_c(GL_n(F))` supported in
the regular elliptic set and `f' ∈ C^∞_c(Dˣ)` supported in the regular set such that `f` and
`f'` match for `μ` and `μ'`, the distribution characters satisfy
`Θ_ρ(f) = (-1)^(n-1) Θ_ρ'(f')`, computed with `μ` and `μ'`. -/
def JacquetLanglandsMatchingTraceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace Dˣ := borel _
    haveI : BorelSpace Dˣ := ⟨rfl⟩
    haveI := Langlands.JacquetLanglands.isTopologicalRing F D
    haveI := generalLinear_t2Space F n
    haveI := generalLinear_locallyCompactSpace F n
    haveI := generalLinear_totallyDisconnectedSpace F n
    haveI := units_t2Space F D
    haveI := units_locallyCompactSpace F D
    haveI := units_totallyDisconnectedSpace F D
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n F) V) (ρ' : Representation ℂ Dˣ W)
      (h : IsJacquetLanglandsPair F D n ρ ρ')
      (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure] (μ' : Measure Dˣ) [μ'.IsHaarMeasure]
      (f : SchwartzBruhat (GeneralLinear n F)) (f' : SchwartzBruhat Dˣ),
      IsEllipticSupported (f : GeneralLinear n F → ℂ) →
      IsDivisionRegularSupported F D (f' : Dˣ → ℂ) →
      AreMatching μ μ' (f : GeneralLinear n F → ℂ) (f' : Dˣ → ℂ) →
      Character.distribution μ ρ h.isAdmissible f =
        (-1) ^ (n - 1) * Character.distribution μ' ρ' h.isAdmissible_right f'

end Langlands.JacquetLanglands
