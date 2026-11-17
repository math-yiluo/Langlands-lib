import Langlands.Automorphic.CuspidalUnitaryForm

/-! # Square integrability of actual translated cusp functions on the band -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance translatedRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance translatedStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance translatedSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

local instance translatedBandIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance translatedBandSmooth :
    _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable [CompactSpace (AdeleQuotient F)] (S : OperatorRealization F n)

/-- Every fixed actual adelic translate of a cusp function remains square
integrable on the original band. No unitary central character is needed. -/
theorem memLp_translate_of_cuspidal (hS : S.IsCuspidal) (a : AdelicGL F n) (f : S.Space) :
    MemLp (fun q => toQuotient F n S f (translate F n a q)) 2
      ((quotientHaarMeasure F n).restrict (band F n)) := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  let : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  have hc : Continuous (fun q => toQuotient F n S f (translate F n a q)) :=
    (toQuotient F n S f).continuous.comp (translate F n a).continuous
  refine Exists.elim (S.exists_band_cover_uniform hS
    (lo := 1) (hi := 2) one_pos {a} isCompact_singleton) fun t ht => ?_
  apply (memLp_norm_iff hc.aestronglyMeasurable).mp
  refine memLp_band_of_continuous F n _ hc.norm t ht.1
    (fun x hx => ht.2.1 x hx.1 hx.2) ?_
  apply ht.2.2 (matrixHaarMeasure F n) f
  intro x
  refine ⟨a, rfl, ?_⟩
  simp only [translate_point, toQuotient_point, enorm_norm, le_refl]

/-- Pairing a translated cusp function against any actual band `L²` vector
defines an integrable scalar coefficient. -/
theorem integrable_inner_translate_of_cuspidal (hS : S.IsCuspidal)
    (a : AdelicGL F n) (f : S.Space)
    (w : Lp ℂ 2 ((quotientHaarMeasure F n).restrict (band F n))) :
    Integrable (fun q => Inner.inner ℂ (w q)
      (toQuotient F n S f (translate F n a q)))
      ((quotientHaarMeasure F n).restrict (band F n)) := by
  have hf := memLp_translate_of_cuspidal S hS a f
  have hc : Continuous (fun q => toQuotient F n S f (translate F n a q)) :=
    (toQuotient F n S f).continuous.comp (translate F n a).continuous
  exact Integrable.mono' ((Lp.memLp w).norm.integrable_mul hf.norm)
    ((Lp.aestronglyMeasurable w).inner hc.aestronglyMeasurable)
    (ae_of_all _ fun _ => norm_inner_le_norm _ _)

end OperatorDeterminantSlice

/-- Actual fixed translates and their Hilbert scalar coefficients are integrable
on the unchanged canonical determinant band. -/
def CuspidalTranslatedBandIntegrabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (n : ℕ) (S : OperatorRealization F n), S.IsCuspidal →
    ∀ (a : AdelicGL F n) (f : S.Space),
      MemLp (fun q => OperatorDeterminantSlice.toQuotient F n S f
        (OperatorDeterminantSlice.translate F n a q)) 2
        ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
          (OperatorDeterminantSlice.band F n)) ∧
      ∀ w : Lp ℂ 2 ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
          (OperatorDeterminantSlice.band F n)),
        Integrable (fun q => Inner.inner ℂ (w q)
          (OperatorDeterminantSlice.toQuotient F n S f
            (OperatorDeterminantSlice.translate F n a q)))
          ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
            (OperatorDeterminantSlice.band F n))

/-- Translated-band integrability for every actual cuspidal operator realization. -/
theorem cuspidalTranslatedBandIntegrability :
    CuspidalTranslatedBandIntegrabilityStatement.{u} := by
  intro F _ _ _ n S hS a f
  exact ⟨OperatorDeterminantSlice.memLp_translate_of_cuspidal S hS a f,
    OperatorDeterminantSlice.integrable_inner_translate_of_cuspidal S hS a f⟩

end Langlands.Automorphic
