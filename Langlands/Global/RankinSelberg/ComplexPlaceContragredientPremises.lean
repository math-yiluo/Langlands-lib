import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-! # Premises for the contragredient-parameter reduction

`ComplexPlaceContragredientParameterStatement` says: if `Td` is contragredient to the actual
cuspidal realization `T` and `d`, `dd` are parameters of `T`, `Td` at the complex place `w`,
then `dd` is a permutation of the inverse characters of `d`. This module states two premises
from which it follows, and the reduction statement itself; none of them is proved here:

* `ComplexPlaceParameterIrreducibleStatement` (global): the `U(n)`-finite complex standard
  module of a parameter of an actual cuspidal realization at a complex place is an irreducible
  `(𝔤, K)`-module;
* `ComplexStandardPairingParameterStatement` (local): if the `U(n)`-finite complex standard
  modules of the lists `d`, `dd` of `n` characters are irreducible and carry a nonzero
  `(𝔤, K)`-invariant bilinear pairing, then `dd` is a permutation of the inverse characters
  of `d`.

`ComplexPlaceContragredientParameterReductionStatement` says that the two premises imply
`ComplexPlaceContragredientParameterStatement`; it is proved in
`Langlands.Global.RankinSelberg.ComplexPlaceContragredientReduction`. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField
open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean
open Langlands.Global.ArchimedeanGL

/-! ### Local objects -/

/-- Right translation by `k ∈ U(n)` on the `U(n)`-finite functions of the complex standard
module of `ds`. -/
def complexStandardTranslate (n : ℕ) (ds : List ComplexCharacterData)
    (k : unitaryCompact ℂ n) (f : complexStandardKFinite n ds) :
    complexStandardKFinite n ds :=
  ⟨Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
      (f : Langlands.GeneralLinear n ℂ → ℂ),
    rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 k.2⟩

/-- The right derivative along a real direction `X ∈ 𝔤𝔩_n(ℂ)` on the `U(n)`-finite
functions of the complex standard module of `ds`. -/
def complexStandardDerivative (n : ℕ) (ds : List ComplexCharacterData)
    (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds) :
    complexStandardKFinite n ds :=
  ⟨rightDerivative (matrixModel ℂ n) X (f : Langlands.GeneralLinear n ℂ → ℂ),
    rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X⟩

/-- The `U(n)`-finite complex standard module of `ds` is an irreducible `(𝔤, K)`-module: it is
nonzero, and every subspace stable under right translation by `U(n)` and under the right
derivatives along `𝔤𝔩_n(ℂ)` is `0` or everything. -/
def IsComplexStandardIrreducible (n : ℕ) (ds : List ComplexCharacterData) : Prop :=
  Nontrivial (complexStandardKFinite n ds) ∧
    ∀ W : Submodule ℂ (complexStandardKFinite n ds),
      (∀ (k : unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
        f ∈ W → complexStandardTranslate n ds k f ∈ W) →
      (∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
        f ∈ W → complexStandardDerivative n ds X f ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- `P` is a `(𝔤, K)`-invariant bilinear pairing of the `U(n)`-finite complex standard modules
of `d` and `dd`: `P(k f, k f') = P(f, f')` for `k ∈ U(n)`, and
`P(X f, f') + P(f, X f') = 0` for the right derivatives along `X ∈ 𝔤𝔩_n(ℂ)`. -/
def IsComplexStandardInvariantPairing (n : ℕ) (d dd : List ComplexCharacterData)
    (P : complexStandardKFinite n d →ₗ[ℂ] complexStandardKFinite n dd →ₗ[ℂ] ℂ) : Prop :=
  (∀ (k : unitaryCompact ℂ n) (f : complexStandardKFinite n d)
      (f' : complexStandardKFinite n dd),
      P (complexStandardTranslate n d k f) (complexStandardTranslate n dd k f') = P f f') ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n d)
      (f' : complexStandardKFinite n dd),
      P (complexStandardDerivative n d X f) f' + P f (complexStandardDerivative n dd X f') = 0

/-! ### The premises -/

/-- **Irreducibility premise.** If an actual cuspidal realization `T` of `GL_(r+1)` over a
number field has the parameter `d` at the complex place `w`, then the `U(r+1)`-finite complex
standard module of `d` is an irreducible `(𝔤, K)`-module. -/
def ComplexPlaceParameterIrreducibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (d : List ComplexCharacterData),
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization w d →
    IsComplexStandardIrreducible (r + 1) d

/-- **Local pairing premise.** If `d` and `dd` are lists of `n` complex characters whose
`U(n)`-finite complex standard modules are irreducible `(𝔤, K)`-modules and carry a nonzero
invariant bilinear pairing, then `dd` is a permutation of the list of inverse characters of
`d`. -/
def ComplexStandardPairingParameterStatement : Prop :=
  ∀ (n : ℕ) (d dd : List ComplexCharacterData), d.length = n → dd.length = n →
    IsComplexStandardIrreducible n d → IsComplexStandardIrreducible n dd →
    ∀ P : complexStandardKFinite n d →ₗ[ℂ] complexStandardKFinite n dd →ₗ[ℂ] ℂ,
      IsComplexStandardInvariantPairing n d dd P → P ≠ 0 →
      dd.Perm (d.map ComplexCharacterData.inv)

/-- **The reduction.** The contragredient-parameter premise follows from the irreducibility
premise and the local pairing premise. -/
def ComplexPlaceContragredientParameterReductionStatement : Prop :=
  ComplexPlaceParameterIrreducibleStatement.{u} → ComplexStandardPairingParameterStatement →
    ComplexPlaceContragredientParameterStatement.{u}

end Langlands.Global.RankinSelbergGlobal
