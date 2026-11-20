import Langlands.BaseChange.TwistedCharacter
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Measure

/-!
# The regular semisimple and σ-regular sets are open and of full Haar measure

Two statements, not proved here. Over a nonarchimedean local field `F` (any characteristic), the
set of regular semisimple elements of `GL_n(F)` is open and its complement is null for every
Haar measure. For a cyclic `F`-algebra `E` of group `⟨σ⟩` of order `l`, the same holds for the
set of σ-regular elements of `GL_n(E)`. They allow the integrals of character functions over
`GL_n` to be read as Henniart–Lemaire's integrals over the regular set (Henniart–Lemaire 2011,
I.5.1, printed p. 29, and II.1.3, printed p. 57).
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands

/-- For every nonarchimedean local field `F` and every `n`: the set of regular semisimple
elements of `GL_n(F)` is open, and its complement has measure zero for every Haar measure on
`GL_n(F)` (Borel σ-algebra) (Harish-Chandra 1999, Introduction, printed p. 1). -/
def RegularSemisimpleOpenConullStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℕ),
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    IsOpen {g : GeneralLinear n F | IsRegularSemisimple g} ∧
      letI : MeasurableSpace (GeneralLinear n F) := borel _
      haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
        μ {g | ¬ IsRegularSemisimple g} = 0

/-- For every nonarchimedean local field `F`, every cyclic `F`-algebra `E` of group `⟨σ⟩` of
order `l` with its module topology, and every `n`: the set of σ-regular elements of `GL_n(E)`
is open, and its complement has measure zero for every Haar measure on `GL_n(E)` (Borel
σ-algebra); used implicitly by Henniart–Lemaire 2011, I.5.1 and II.1.3. -/
def SigmaRegularOpenConullStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    IsOpen {δ : GeneralLinear n E | IsSigmaRegular σ l δ} ∧
      letI : MeasurableSpace (GeneralLinear n E) := borel _
      haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
      ∀ (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        μ {δ | ¬ IsSigmaRegular σ l δ} = 0

end Langlands.BaseChange
