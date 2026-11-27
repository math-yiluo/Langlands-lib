import Langlands.JacquetLanglands.DivisionMatching
import Langlands.JacquetLanglands.DivisionUnits
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: regular transfer from the units of a `p`-adic division algebra to `GL_n(F)`

For a nonarchimedean local field `F` of characteristic zero and a central division algebra `D`
of dimension `n^2` over `F`: every Schwartz–Bruhat function on `Dˣ` supported in the regular
set matches a Schwartz–Bruhat function on `GL_n(F)` supported in the regular elliptic set
(Deligne–Kazhdan–Vignéras 1984, B.2.c 1), printed p. 83, for `m = 1`; Badulescu 2002, §5,
printed p. 733). The statement is not proved here. See the paired Markdown.
-/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory
open HarmonicAnalysis (SchwartzBruhat)
open Langlands.BaseChange (IsEllipticSupported)

universe u

/-- Regular transfer (DKV, B.2.c 1), for `m = 1`; Badulescu 2002, §5): let `F` be a
nonarchimedean local field of characteristic zero and `D` a central division algebra over `F`
of dimension `n^2`, with its module topology; give `GL_n(F)` and `Dˣ` their Borel σ-algebras.
For all Haar measures `μ` on `GL_n(F)` and `μ'` on `Dˣ`, every `f' ∈ C^∞_c(Dˣ)` supported in
the regular set matches some `f ∈ C^∞_c(GL_n(F))` supported in the regular elliptic set. -/
def DivisionRegularTransferStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace Dˣ := borel _
    haveI : BorelSpace Dˣ := ⟨rfl⟩
    haveI := Langlands.JacquetLanglands.isTopologicalRing F D
    ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure] (μ' : Measure Dˣ) [μ'.IsHaarMeasure]
      (f' : SchwartzBruhat Dˣ), IsDivisionRegularSupported F D (f' : Dˣ → ℂ) →
      ∃ f : SchwartzBruhat (GeneralLinear n F),
        IsEllipticSupported (f : GeneralLinear n F → ℂ) ∧
          AreMatching μ μ' (f : GeneralLinear n F → ℂ) (f' : Dˣ → ℂ)

end Langlands.JacquetLanglands
