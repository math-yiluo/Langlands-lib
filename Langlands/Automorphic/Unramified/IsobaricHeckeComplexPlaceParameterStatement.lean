import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.HeckeFamilyEndpoint

/-! # Complex-place parameters at a Hecke-family Euler endpoint, conditional on C2

An internal comparison target for the B6 endpoint of the operator plan, as used by the
exact-stabilizer branches. Given the published Euler-polynomial constituent recovery
(`CuspidalEulerConstituentRecoveryStatement`, the C2 input), actual isobaric constituent data
whose attached Euler polynomials agree at almost all finite places with the product of the
rank-one Euler polynomials of a finite family of actual Hecke characters have, at every complex
place, exactly the complex-place parameter lists of that family. Nothing is proved here.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global

/-- Conditional on C2, the finite Hecke-family Euler endpoint `IsobaricData.HasHeckeFamily`
determines the complex-place parameters: for every actual complex place `v` and every list
`ds`, the isobaric data `D` have the parameter `ds` at `v` (complete constituent enumeration,
block multiplicities, permutation closure) exactly when the actual Hecke characters `μ` have
it through the selected completion coordinate (permutation closure). No unitarity,
total-complexness, base-change, Galois, place-uniqueness or positive-rank premise is made;
the empty family and the zero datum are included. -/
def IsobaricHeckeComplexPlaceParameterStatement : Prop :=
  CuspidalEulerConstituentRecoveryStatement.{uF, uV} →
    ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (n : ℕ) (D : IsobaricData F) (μ : Fin n → HeckeCharacter F),
      IsobaricData.HasHeckeFamily.{uF, uV} D μ →
        ∀ (v : {v : NumberField.InfinitePlace F //
                  NumberField.InfinitePlace.IsComplex v})
          (ds : List Langlands.LocalFactor.Archimedean.ComplexCharacterData),
          D.HasComplexPlaceParameter v ds ↔
            Langlands.Global.HeckeCharacter.FamilyHasComplexPlaceParameter μ v ds

end Langlands.Automorphic.Unramified
