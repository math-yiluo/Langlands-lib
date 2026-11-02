import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.Global.Arithmetic.CMAntisymmetrization

/-!
# Unramified realization of CM infinity types

Realize an anticyclotomic integral infinity type after one positive common scaling.
The base-character construction removes the unit and finite-class obstructions;
antisymmetrization gives conjugate self-duality while preserving finite unramifiedness.
-/

noncomputable section

universe u

namespace Langlands.Global

open NumberField
open Langlands.ClassField.Global

namespace CMUnramifiedInfinity

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

/-- The base character is trivial on integral ideles with trivial infinite part. -/
theorem exists_base_character_trivial (a : InfinityType K)
    (ha : a.IsAnticyclotomic) :
    ∃ (n : ℕ) (ψ : HeckeCharacter K), 0 < n ∧
      ψ.HasPrescribedInfinityComponent
        (InfinityType.toCharacter (fun σ ↦ (n : ℤ) * a σ)) ∧
      ∀ x : Ideles K, x ∈ integralIdeles K →
        (x : Adeles K).1 = 1 → ψ (ideleClassMap K x) = 1 := by
  obtain ⟨n, ψ, hn, hψ, hint⟩ := exists_base_character a ha
  refine ⟨n, ψ, hn, hψ, ?_⟩
  intro x hx harch
  have hproj : infinityProjection x = 1 := Units.ext harch
  simpa only [hproj, map_one] using hint ⟨x, hx⟩

end CMUnramifiedInfinity

/-- Every anticyclotomic integral infinity type of a CM number field has an everywhere
unramified, conjugate-self-dual Hecke-character realization after positive common scaling. -/
theorem cmUnramifiedInfinityRealization : CMUnramifiedInfinityRealizationStatement.{u} := by
  intro K _ _ _ a ha
  obtain ⟨n, ψ, hn, hψinf, hψ⟩ :=
    CMUnramifiedInfinity.exists_base_character_trivial a ha
  exact CMUnramifiedInfinity.realization_of_base ha hn hψinf hψ

end Langlands.Global
