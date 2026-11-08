import Langlands.Automorphic.OperatorDeterminantSliceHaar
import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Automorphic.AssociatedFactorStatement

/-! # Compact invariance of the determinant-band form -/

noncomputable section
universe uF
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj InnerProductSpace NNReal

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions NumberField

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance compactFormIsAffine : IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance compactFormSmooth : Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance unitaryCompactFormGroup1 : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance unitaryCompactFormGroup2 : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance unitaryCompactFormGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance unitaryCompactFormGroup4 : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance unitaryCompactFormGroup5 : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance unitaryCompactFormGroup6 : AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 500000 in
/-- The original compact action is the same positive right translation. -/
theorem toQuotient_compact (k : standardInfiniteCompact F n) (f : S.Space) (q : Quotient F n) :
    toQuotient F n S (S.compactRepresentation k f) q =
      toQuotient F n S f (translate F n (AdelicGL.ofInfinite F n k.val) q) := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  simp only [translate_point, toQuotient_point,
    OperatorRealization.evaluate_compactRepresentation]

set_option maxHeartbeats 1500000 in
/-- Normalized right translation proves invariance for the original compact action. -/
theorem inner_toL2_compact (hn : n ≠ 0) (measure : Measure (Quotient F n))
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ)
    (hL2 : ∀ f : S.Space, MemLp (toQuotient F n S f) 2 (measure.restrict (band F n)))
    (hmeasure : ∀ g : AdelicGL F n,
      AdelicBlockDeterminantCharacter.determinantNorm F n g = 1 →
        MeasurePreserving (translate F n g) measure measure)
    (k : standardInfiniteCompact F n) (f g : S.Space) :
    inner ℂ (toL2 F n S measure hL2 (S.compactRepresentation k f))
      (toL2 F n S measure hL2 (S.compactRepresentation k g)) =
        inner ℂ (toL2 F n S measure hL2 f) (toL2 F n S measure hL2 g) := by
  obtain ⟨z, hz⟩ := exists_normalized_rightTranslate F n hn (AdelicGL.ofInfinite F n k.val)
  let a := AdelicGL.scalar F n z * AdelicGL.ofInfinite F n k.val
  have ha := measurePreserving_translate_band F n measure a hz (hmeasure a hz)
  rw [inner_toL2, inner_toL2]
  calc
    _ = ∫ q, inner ℂ (toQuotient F n S f (translate F n a q))
        (toQuotient F n S g (translate F n a q)) ∂measure.restrict (band F n) := by
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [a]
      rw [toQuotient_compact, toQuotient_compact,
        toQuotient_central F n S χ hS, toQuotient_central F n S χ hS]
      exact (inner_phase _ _ _ (hχ _)).symm
    _ = _ := ha.integral_comp
      (translate F n a).toMeasurableEquiv.measurableEmbedding
      (fun q => inner ℂ (toQuotient F n S f q) (toQuotient F n S g q))

end Langlands.Automorphic.OperatorDeterminantSlice

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory

local instance unitaryCompactFormGroup7 (F : Type uF) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance unitaryCompactFormGroup8 (F : Type uF) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance unitaryCompactFormGroup9 (F : Type uF) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance unitaryCompactFormGroup10 (F : Type uF) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance unitaryCompactFormGroup11 (F : Type uF) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance unitaryCompactFormGroup12 (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- A cuspidal realization with unitary central character carries a positive definite
Hermitian form on its original carrier, invariant under both the finite adelic and the
standard infinite compact actions. -/
theorem CuspidalOperatorRealization.exists_compactInvariantForm
    {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (T : CuspidalOperatorRealization F r)
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T) :
    ∃ b : Langlands.InvariantPositiveForm T.realization.finiteRepresentation,
      ∀ (k : standardInfiniteCompact F (r + 1)) (f g : T.Space),
        b.inner (T.realization.compactRepresentation k f)
          (T.realization.compactRepresentation k g) = b.inner f g := by
  obtain ⟨χ, hχ, hTχ⟩ := hT
  let : MeasurableSpace (AdelicGL F (r + 1)) := borel _
  have : BorelSpace (AdelicGL F (r + 1)) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfinite⟩ :=
    T.realization.exists_band_cover T.cuspidal (lo := 1) (hi := 2) one_pos
  have hL2 := fun f => OperatorDeterminantSlice.memLp_band_of_cover F (r + 1) T.realization
    t ht (fun x hx => hcover x hx.1 hx.2) f (hfinite _ f)
  refine ⟨OperatorDeterminantSlice.finiteInvariantPositiveFormOfHaar F (r + 1) T.realization
    (Nat.succ_ne_zero r) χ hχ hTχ hL2, ?_⟩
  intro k f g
  exact OperatorDeterminantSlice.inner_toL2_compact F (r + 1) T.realization
    (Nat.succ_ne_zero r) _ χ hχ hTχ hL2
    (fun g _ => OperatorDeterminantSlice.measurePreserving_translate F (r + 1) g) k f g

end Langlands.Automorphic
