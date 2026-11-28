import Langlands.BaseChange.OrbitalIntegral
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Character.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Norm.Basic

/-!
# Characters are detected by regularly supported functions near the norms

The statement that the distribution character `f ↦ tr π(f)` of an irreducible admissible
representation `π` of `GL_n(F)`, for a nonarchimedean local field `F` of characteristic zero,
is nonzero on some Schwartz–Bruhat function `f` that is supported in the regular semisimple
set, has vanishing orbital integrals at regular semisimple elements that are not norms from a
given cyclic `F`-algebra `E`, and is supported on matrices whose determinant is a norm from
`Eˣ`. It is a consequence of the local integrability of the character (Harish-Chandra) and
of the fact that the norms contain a neighbourhood of `1`: the character is a locally
integrable function, locally constant on the regular set, and its integral over a small
compact open subgroup `J` is a nonzero multiple of `dim V^J`. Statement only; not proved
here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` of
group `⟨σ⟩` of order `l` with its module topology, and `0 < n`: for every irreducible
admissible representation `π` of `GL_n(F)` on a complex vector space `V : Type uV` and every
Haar measure `μ` on `GL_n(F)` (Borel σ-algebra), some Schwartz–Bruhat function `f` on
`GL_n(F)` is supported in the regular semisimple set, has orbital integrals (for `μ`) vanishing
at the regular semisimple non-norms, is supported on matrices `g` with `det g` in the image
of the norm `Eˣ → Fˣ`, and has `tr π(f) ≠ 0`. -/
def RegularNormTraceNonvanishingStatement.{u, v, uV} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    IsCyclicAlgebra σ l → 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π), π.IsIrreducible →
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
        ∃ f : SchwartzBruhat (GeneralLinear n F),
          IsRegularSupported (f : GeneralLinear n F → ℂ) ∧
          VanishesOffNorms σ l μ (f : GeneralLinear n F → ℂ) ∧
          (∀ g : GeneralLinear n F, f g ≠ 0 →
            GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : E →* F)).range) ∧
          Character.distribution μ π hπ f ≠ 0

end Langlands.BaseChange
