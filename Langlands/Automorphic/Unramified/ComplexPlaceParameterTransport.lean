import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.LocalFactor.ArchimedeanPairFactor

/-! # Complex-place parameter lists in the selected coordinates

Internal vocabulary for transporting lists of complex character blocks between a complex
place and an actual place above it, and concatenating such lists over an explicit enumeration
of all places above the base place. No automorphic compatibility is asserted.
-/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open NumberField Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open scoped NumberField.LiesOver

/-- An actual place above a complex place, packaged for `HasComplexPlaceParameter`. -/
def complexPlaceAbove
    {F : Type uF} {E : Type uE} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E]
    (v : {v : InfinitePlace F // v.IsComplex}) (w : InfinitePlacesAbove E v.1) :
    {w : InfinitePlace E // w.IsComplex} :=
  ⟨w.1, InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 v.2⟩

/-- Read the blocks in the selected coordinates at the other place: from `v` to `w`,
or from `w` to `v`. Conjugation changes each weight's sign and retains its exponent. -/
def complexPlaceParameterTransport
    {F : Type uF} {E : Type uE} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E]
    (v : {v : InfinitePlace F // v.IsComplex}) (w : InfinitePlacesAbove E v.1)
    (ds : List ComplexCharacterData) : List ComplexCharacterData :=
  open Classical in
  if w.1.embedding.comp (algebraMap F E) = v.1.embedding then ds
  else ds.map ComplexCharacterData.conj

/-- Concatenate all lists above `v`, transported to the selected coordinates at `v`,
in the order of the supplied enumeration `e` of the actual places above `v`. -/
def complexPlaceLanglandsSum
    {F : Type uF} {E : Type uE} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E]
    (v : {v : InfinitePlace F // v.IsComplex}) {d : ℕ}
    (e : Fin d ≃ InfinitePlacesAbove E v.1)
    (ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData) :
    List ComplexCharacterData :=
  (List.ofFn (fun i : Fin d => complexPlaceParameterTransport v (e i) (ds (e i)))).flatten

end Langlands.Automorphic.Unramified
