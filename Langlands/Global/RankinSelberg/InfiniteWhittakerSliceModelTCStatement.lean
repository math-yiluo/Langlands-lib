import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction

/-! # The actual archimedean Whittaker slice comparison over totally complex fields

The fieldwise body of `InfiniteWhittakerSliceModelStatement` and its closure
restricted to totally complex fields. The underlying comparison data are unchanged.
-/

noncomputable section
open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct
set_option autoImplicit false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic InfiniteWhittakerSlice Langlands.LocalFactor.Archimedean
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.ClassField.Global.RelativeWeilGroup

local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance (F : Type u) [Field F] (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The local model and slice comparison for one actual cuspidal spectral presentation,
at the given field `F`. -/
def InfiniteWhittakerSliceModelAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hI : HasIrreducibleAdmissibleComponents P)
    (χ : AddChar (Adeles F) ℂ),
    IsStandardAdditiveCharacter F χ →
  ∀ (dR : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
  ∀ (dC : {w : InfinitePlace F // w.IsComplex} → List ComplexCharacterData),
    (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    Nonempty (ModelData P hI χ)

/-- The actual archimedean Whittaker slice comparison for each totally complex field.
There are no real places, but the same `ModelData` is used. -/
def InfiniteWhittakerSliceModelTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    InfiniteWhittakerSliceModelAt.{u, uQ} F

end Langlands.Global.RankinSelbergGlobal
