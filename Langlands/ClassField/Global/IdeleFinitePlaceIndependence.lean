import Langlands.ClassField.Global.IdeleFinitePlaceIndependenceStatement
import Langlands.ClassField.Global.FinitePlaceConjugacy
import Langlands.ClassFieldTheory.Local.SameBaseConjugacy

/-! # Independence of finite idele invariants from the upper place -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)

include hInf in
/-- Inflation-compatible local invariants agree at all places above a fixed finite place. -/
theorem finiteIdeleInvariantPlaceIndependent_of_inflationCompatibility :
    FiniteIdeleInvariantPlaceIndependent I := by
  intro F E _ _ _ _ _ _ v w z _ _ c
  obtain ⟨g, rfl⟩ := exists_finitePlaceEquiv_eq v w z
  have := liesOver_finitePlaceEquiv v w g
  have := isGalois_adicCompletion v w
  have := isGalois_adicCompletion v (finitePlaceEquiv g.toRingEquiv w)
  have := FiniteExtension.local_finite v w
  have := FiniteExtension.local_finite v (finitePlaceEquiv g.toRingEquiv w)
  have h := (I (residuePrime v)).relative_relativeConjugacy_refl_of_inflationCompatibility
    (hInf _) (padicField v) (finiteCompletionAlgEquiv v w g)
    (finiteCompletionCompatible v w g)
    (ideleLocalMap v (finitePlaceEquiv g.toRingEquiv w) 2 c)
  rw [ideleLocalMap_finiteCompletionConjugacy_apply] at h
  exact h

/-- The finite-place independence target follows from local inflation compatibility. -/
theorem finiteIdeleInvariantPlaceIndependenceStatement :
    FiniteIdeleInvariantPlaceIndependenceStatement.{u} :=
  fun I hInf => finiteIdeleInvariantPlaceIndependent_of_inflationCompatibility I hInf

variable (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)

include hInf in
/-- The total family agrees with every choice of upper places using local inflation alone. -/
theorem totalIdeleInvariantMaps_eq_of_inflationCompatibility
    {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E]
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    totalIdeleInvariantMaps I hI F E = totalIdeleInvariant I hI wf wi :=
  totalIdeleInvariantMaps_eq_of_placeIndependent I hI
    (finiteIdeleInvariantPlaceIndependent_of_inflationCompatibility I hInf) wf wi

include hInf in
/-- The actual total idele invariant family satisfies inflation from the local inflation law. -/
theorem totalIdeleInvariantMaps_inflation_of_inflationCompatibility :
    (totalIdeleInvariantMaps I hI).InflationCompatible :=
  totalIdeleInvariantMaps_inflation I hI
    (finiteIdeleInvariantPlaceIndependent_of_inflationCompatibility I hInf) hInf

end Langlands.ClassField.Global
