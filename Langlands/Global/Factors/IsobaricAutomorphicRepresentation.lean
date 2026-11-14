import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Correspondence.UnramifiedNormalization
import Langlands.Automorphic.IrreducibleOperatorSubquotient
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.OperatorSubquotientPlaceAction
import Langlands.Automorphic.OperatorSubquotientLieAction
import Langlands.Representation.Classification.IsobaricSum

/-!
# Isobaric automorphic representations of `GL_n` over a number field

Getz–Hahn (2024), Definition 10.7.6, for irreducible automorphic operator
subquotients of `GL_(r+1)` over a number field, at every place. An irreducible
automorphic subquotient `Q` is the isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` of actual cuspidal
realizations `π_i` of `GL_(m_i+1)` with `∑ (m_i + 1) = r + 1` when
- at every finite place `v`, the restriction of `Q` to `GL_(r+1)(F_v)` contains the
  local isobaric sum `π_(1,v) ⊞ ⋯ ⊞ π_(k,v)`;
- at every real or complex place `v`, the archimedean standard-module parameters of
  the `π_i` at `v`, put together and ordered by the real parts of their exponents
  (Getz–Hahn (10.30)), have a standard module whose `(𝔤_v, K_v)`-map into `Q` has a
  nonzero irreducible image, that is, `Q` contains the Langlands quotient of that
  standard module.

`Q` is isobaric when it is such an isobaric sum for some cuspidal realizations. See
the paired Markdown for the sources, the conventions and the scope.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Manifold ContDiff Matrix.Norms.Operator

universe u uQ

namespace Langlands.LocalFactor.Archimedean

/-- The exponent `t` of a real block: the block `sgn^ε ⊗ |·|^t` of `GL_1(ℝ)` for a
real character, and the block of `GL_2(ℝ)` with central character `|·|^(2t)` times a
sign for the real induction of a complex character `(z/|z|)^m |z|^(2t)`. -/
def RealBlock.exponent : RealBlock → ℂ
  | .character d => d.exponent
  | .induced d => d.exponent

/-- A list of real blocks is in Langlands order when the real parts of the exponents
weakly decrease along the list (Getz–Hahn (10.30)). -/
def IsRealLanglandsOrdered (ds : List RealBlock) : Prop :=
  ds.Pairwise fun a b => b.exponent.re ≤ a.exponent.re

/-- A list of complex characters `(z/|z|)^m |z|^(2t)` is in Langlands order when the
real parts of the exponents `t` weakly decrease along the list (Getz–Hahn (10.30),
Knapp (4.3)). -/
def IsComplexLanglandsOrdered (ds : List ComplexCharacterData) : Prop :=
  ds.Pairwise fun a b => b.exponent.re ≤ a.exponent.re

end Langlands.LocalFactor.Archimedean

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance isobaricRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance isobaricContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance isobaricSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance isobaricFormGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance isobaricStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance isobaricRealizationGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance isobaricGeneralLinearTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

namespace OperatorSubquotient

variable {n : ℕ} (Q : OperatorSubquotient F n)

/-- At the real place `v`, `Q` contains the Langlands quotient of the standard module
of the real blocks `ds`: the blocks have total rank `n` and are in Langlands order, and
there is a linear map `A` from the `O(n)`-finite functions of their standard module
into `Q` that carries right translation by `k ∈ O(n)` to the compact action of `k` at
`v` and the right derivative along `X ∈ 𝔤𝔩_n(ℝ)` to the Lie action of `X` at `v`, whose
image is nonzero and has no subspaces stable under these actions other than `0` and
itself. -/
def HasRealPlaceLanglandsQuotient (v : RP) (ds : List RealBlock) : Prop :=
  realRank ds = n ∧ IsRealLanglandsOrdered ds ∧
    ∃ A : realStandardKFinite n ds →ₗ[ℂ] Q.Space,
      (∀ (k : Archimedean.unitaryCompact ℝ n) (f : realStandardKFinite n ds),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
            (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
              realStandardKFinite n ds,
          A ⟨_, hf⟩ = Q.realPlaceCompactRepresentation v
            ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A f)) ∧
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℝ n) X
            (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ realStandardKFinite n ds,
          A ⟨_, hf⟩ = Q.realPlaceLieAction v (1 ⊗ₜ X) (A f)) ∧
      LinearMap.range A ≠ ⊥ ∧
      ∀ W : Submodule ℂ Q.Space, W ≤ LinearMap.range A →
        (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (w : Q.Space), w ∈ W →
          Q.realPlaceCompactRepresentation v k w ∈ W) →
        (∀ (X : Matrix (Fin n) (Fin n) ℝ) (w : Q.Space), w ∈ W →
          Q.realPlaceLieAction v (1 ⊗ₜ X) w ∈ W) →
        W = ⊥ ∨ W = LinearMap.range A

/-- At the complex place `v`, with `F_v` identified with `ℂ` as in the published place
actions, `Q` contains the Langlands quotient of the standard module of the complex
characters `ds`: there are `n` characters in Langlands order, and there is a linear map
`A` from the `U(n)`-finite functions of their standard module into `Q` that carries
right translation by `k ∈ U(n)` to the compact action of `k` at `v` and the right
derivative along a real direction `X ∈ 𝔤𝔩_n(ℂ)` to the Lie action of `X` at `v`, whose
image is nonzero and has no subspaces stable under these actions other than `0` and
itself. -/
def HasComplexPlaceLanglandsQuotient (v : CP) (ds : List ComplexCharacterData) : Prop :=
  ds.length = n ∧ IsComplexLanglandsOrdered ds ∧
    ∃ A : complexStandardKFinite n ds →ₗ[ℂ] Q.Space,
      (∀ (k : Archimedean.unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
            (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
              complexStandardKFinite n ds,
          A ⟨_, hf⟩ = Q.complexPlaceCompactRepresentation v
            ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f)) ∧
      (∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
            (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ complexStandardKFinite n ds,
          A ⟨_, hf⟩ = Q.complexPlaceLieAction v (1 ⊗ₜ X) (A f)) ∧
      LinearMap.range A ≠ ⊥ ∧
      ∀ W : Submodule ℂ Q.Space, W ≤ LinearMap.range A →
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (w : Q.Space), w ∈ W →
          Q.complexPlaceCompactRepresentation v k w ∈ W) →
        (∀ (X : Matrix (Fin n) (Fin n) ℂ) (w : Q.Space), w ∈ W →
          Q.complexPlaceLieAction v (1 ⊗ₜ X) w ∈ W) →
        W = ⊥ ∨ W = LinearMap.range A

end OperatorSubquotient

namespace IrreducibleOperatorSubquotient

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- `Q` is the isobaric sum of the actual cuspidal realizations `T i` of `GL_(m i + 1)`,
read through spectral presentations `P i` with irreducible admissible finite local
components:
- at every finite place `v`, some irreducible admissible representation of
  `GL_(r+1)(F_v)` that is an isobaric sum of the local components of the `P i` at `v`
  embeds into the restriction of `Q` to `GL_(r+1)(F_v)`;
- at every real place `v`, the `T i` have standard-module parameters `ds i` at `v`, and
  `Q` contains at `v` the Langlands quotient of a reordering of the concatenation of the
  `ds i`;
- at every complex place `v`, likewise with complex parameters. -/
def IsCuspidalIsobaricSum (Q : IrreducibleOperatorSubquotient F r) {k : ℕ} {m : Fin k → ℕ}
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)) : Prop :=
  (∀ v : FinitePlace F, ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
        (fun i => (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj)
        A.obj ∧
      ∃ f : A.obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap) ∧
    (∀ v : RP, ∃ ds : Fin k → List RealBlock,
      (∀ i, (T i).realization.HasRealPlaceParameter v (ds i)) ∧
      ∃ ds' : List RealBlock, ds'.Perm (List.ofFn ds).flatten ∧
        Q.subquotient.HasRealPlaceLanglandsQuotient v ds') ∧
    ∀ v : CP, ∃ ds : Fin k → List ComplexCharacterData,
      (∀ i, (T i).realization.HasComplexPlaceParameter v (ds i)) ∧
      ∃ ds' : List ComplexCharacterData, ds'.Perm (List.ofFn ds).flatten ∧
        Q.subquotient.HasComplexPlaceLanglandsQuotient v ds'

/-- **Isobaric automorphic representations** (Getz–Hahn 2024, Definition 10.7.6). An
irreducible automorphic operator subquotient `Q` of `GL_(r+1)` is isobaric when there
are actual cuspidal realizations `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1`,
and spectral presentations of them with irreducible admissible finite local components,
such that `Q` is the isobaric sum of the `T i` at every place. -/
def IsIsobaric (Q : IrreducibleOperatorSubquotient F r) : Prop :=
  ∃ (k : ℕ) (m : Fin k → ℕ) (_ : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
    Q.IsCuspidalIsobaricSum T P h

end IrreducibleOperatorSubquotient

end Langlands.Automorphic
