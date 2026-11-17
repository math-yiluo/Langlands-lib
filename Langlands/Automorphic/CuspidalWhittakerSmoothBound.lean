import Langlands.Automorphic.CuspidalWhittakerBandBound
import Langlands.Global.ArchimedeanRealWordSmoothBounds

/-! # Actual Whittaker bounds in supplied orbit-derivative seminorms -/

noncomputable section

universe u w u𝔤 uH uG

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  ContinuousRationalFunctions MeasureTheory

local instance smoothBoundRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance smoothBoundContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance smoothBoundFiniteSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance smoothBoundFormGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance smoothBoundStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance smoothBoundSpaceGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)
  (hL2 : ∀ x : T.Space,
    MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))))
  (ψ : AddChar (Adeles F) ℂ)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  (π : G →* (E →L[ℂ] E)) (j : T.Space →ₗ[ℂ] E)
  (ζ : ArchimedeanGL.RealLieAlgebra F (r + 1) → 𝔤)

set_option maxHeartbeats 1600000 in
/-- The actual band bound gives a compact Whittaker bound in supplied orbit
seminorms, assuming equality of norms and compatibility of real generators.
This is a bound on original vectors at a fixed finite level. -/
theorem cuspWhittaker_smoothBound_of_bandBound
    (hbound : CuspidalWhittakerBandBound F T hL2 ψ)
    (hnorm : ∀ v : T.Space,
      ‖OperatorDeterminantSlice.toL2 F (r + 1) T.realization
        (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2 v‖ = ‖j v‖)
    (hgen : ∀ (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (v : T.Space),
      j (T.realization.envelopingAction
        (ArchimedeanGL.envelopingGenerator F (r + 1)
          (ArchimedeanGL.complexify F (r + 1) X)) v) =
        Langlands.Archimedean.lieDerivative I π (ζ X) (j v)) :
    ∀ J : Subgroup (FiniteAdelicGL F (r + 1)),
      IsOpen (J : Set (FiniteAdelicGL F (r + 1))) →
      IsCompact (J : Set (FiniteAdelicGL F (r + 1))) →
      ∀ Q : Set (Points F (r + 1)), IsCompact Q →
        ∃ (S : Finset (List 𝔤)) (C : ℝ), 0 ≤ C ∧ ∀ v : T.Space,
          (∀ k : J, T.realization.finiteRepresentation
            (k : FiniteAdelicGL F (r + 1)) v = v) →
          ∀ g ∈ Q, ‖cuspWhittaker F T ψ v g‖ ≤
            C * ∑ xs ∈ S, ‖Langlands.Archimedean.iteratedLieDerivative I π xs (j v)‖ := by
  intro J hJo hJc Q hQ
  obtain ⟨D, C, hC, hc⟩ := hbound J hJo hJc Q hQ
  obtain ⟨S, B, hB, hb⟩ :=
    ArchimedeanGL.sum_norm_enveloping_le_iteratedLieDerivatives F (r + 1)
      I π T.realization.envelopingAction j ζ hgen D
  refine ⟨S, C * B, mul_nonneg hC hB, ?_⟩
  intro v hv g hg
  have he : (∑ d ∈ D,
      ‖OperatorDeterminantSlice.toL2 F (r + 1) T.realization
        (OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)) hL2
        (T.realization.envelopingAction d v)‖) =
      ∑ d ∈ D, ‖j (T.realization.envelopingAction d v)‖ := by
    exact Finset.sum_congr rfl (fun _ _ => hnorm _)
  exact (hc v hv g hg).trans ((mul_le_mul_of_nonneg_left
    (he.trans_le (hb v)) hC).trans_eq (mul_assoc C B _).symm)

end Langlands.Automorphic
