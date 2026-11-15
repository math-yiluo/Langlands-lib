import Langlands.Global.Factors.CuspidalSupportStatement
import Langlands.Global.Factors.IsobaricAutomorphicRepresentation
import Langlands.Automorphic.IsobaricData

/-!
# Cuspidal support of automorphic representations of `GL_n`, at every place

Langlands' theorem that every automorphic representation of `GL_(r+1)` over a number
field is a constituent of a representation induced from cuspidal data (Langlands 1979,
Proposition 2; Getz–Hahn 2024, Theorem 10.7.1 with the remark after it), now read at
every place, together with the cuspidal-support map to isobaric data (Getz–Hahn 2024,
Corollary 10.7.3 and the sentence after it) and the fact that an isobaric sum is a
constituent of the representation induced from its own summands (Getz–Hahn 2024,
Theorem 10.7.5).

At a real or complex place `v` the cuspidal realizations `T i` are read through
standard-module parameters `ds i` at `v`. The representation induced from the `T i` at
`v` is then the standard module of the concatenation of the `ds i`, and `Q` is a
constituent at `v` when an irreducible subquotient of that standard module embeds into
the `(𝔤_v, K_v)`-module of `Q`. See the paired Markdown for the sources and scope.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Manifold ContDiff Matrix.Norms.Operator

universe u uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance supportRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance supportContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance supportSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance supportFormGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance supportStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance supportRealizationGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable {n : ℕ} (Q : OperatorSubquotient F n)

/-- At the real place `v`, `Q` contains an irreducible subquotient of the standard module
of the real blocks `ds`, in the given order: the blocks have total rank `n`, and there are
a subspace `W` of the `O(n)`-finite functions of their standard module and a linear map
`A` from `W` into `Q`, such that right translation by `k ∈ O(n)` preserves `W` and is
carried by `A` to the compact action of `k` at `v`, the right derivative along
`X ∈ 𝔤𝔩_n(ℝ)` preserves `W` and is carried by `A` to the Lie action of `X` at `v`, and the
image of `A` is nonzero and has no subspaces stable under these actions other than `0`
and itself. The image is then the irreducible subquotient `W / ker A`. -/
def HasRealPlaceStandardConstituent (v : RP) (ds : List RealBlock) : Prop :=
  realRank ds = n ∧
    ∃ W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ), W ≤ realStandardKFinite n ds ∧
    ∃ A : W →ₗ[ℂ] Q.Space,
      (∀ (k : Archimedean.unitaryCompact ℝ n) (f : W),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
            (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ W,
          A ⟨_, hf⟩ = Q.realPlaceCompactRepresentation v
            ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A f)) ∧
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : W),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℝ n) X
            (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ W,
          A ⟨_, hf⟩ = Q.realPlaceLieAction v (1 ⊗ₜ X) (A f)) ∧
      LinearMap.range A ≠ ⊥ ∧
      ∀ U : Submodule ℂ Q.Space, U ≤ LinearMap.range A →
        (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (w : Q.Space), w ∈ U →
          Q.realPlaceCompactRepresentation v k w ∈ U) →
        (∀ (X : Matrix (Fin n) (Fin n) ℝ) (w : Q.Space), w ∈ U →
          Q.realPlaceLieAction v (1 ⊗ₜ X) w ∈ U) →
        U = ⊥ ∨ U = LinearMap.range A

/-- At the complex place `v`, with `F_v` identified with `ℂ` as in the published place
actions, `Q` contains an irreducible subquotient of the standard module of the complex
characters `ds`, in the given order: there are `n` characters, and there are a subspace
`W` of the `U(n)`-finite functions of their standard module and a linear map `A` from `W`
into `Q`, such that right translation by `k ∈ U(n)` preserves `W` and is carried by `A` to
the compact action of `k` at `v`, the right derivative along a real direction
`X ∈ 𝔤𝔩_n(ℂ)` preserves `W` and is carried by `A` to the Lie action of `X` at `v`, and the
image of `A` is nonzero and has no subspaces stable under these actions other than `0`
and itself. -/
def HasComplexPlaceStandardConstituent (v : CP) (ds : List ComplexCharacterData) : Prop :=
  ds.length = n ∧
    ∃ W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ), W ≤ complexStandardKFinite n ds ∧
    ∃ A : W →ₗ[ℂ] Q.Space,
      (∀ (k : Archimedean.unitaryCompact ℂ n) (f : W),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
            (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ W,
          A ⟨_, hf⟩ = Q.complexPlaceCompactRepresentation v
            ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f)) ∧
      (∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : W),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
            (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ W,
          A ⟨_, hf⟩ = Q.complexPlaceLieAction v (1 ⊗ₜ X) (A f)) ∧
      LinearMap.range A ≠ ⊥ ∧
      ∀ U : Submodule ℂ Q.Space, U ≤ LinearMap.range A →
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (w : Q.Space), w ∈ U →
          Q.complexPlaceCompactRepresentation v k w ∈ U) →
        (∀ (X : Matrix (Fin n) (Fin n) ℂ) (w : Q.Space), w ∈ U →
          Q.complexPlaceLieAction v (1 ⊗ₜ X) w ∈ U) →
        U = ⊥ ∨ U = LinearMap.range A

end OperatorSubquotient

end Langlands.Automorphic

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient PositiveRankCuspidalClass IsobaricData)
open LocalFactor.Archimedean (RealBlock ComplexCharacterData)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

/-- **Constituent of a cuspidally induced representation, at every place.** Let `T i`
(`i < k`) be actual cuspidal realizations of `GL_(m i + 1)` over a number field `F`, with
`∑ (m i + 1) = r + 1`, and `P i` spectral presentations of them whose finite local
components are irreducible and admissible. An irreducible automorphic operator
subquotient `Q` of `GL_(r+1)` is an *induced constituent* of these data when
* it is a finite induced constituent of them (`IsFiniteInducedConstituent`);
* at every real place `v`, the `T i` have standard-module parameters `ds i` at `v` such
  that `Q` contains at `v` an irreducible subquotient of the standard module of the
  concatenation `ds 0 ++ ⋯ ++ ds (k-1)`, in this order;
* at every complex place `v`, likewise with complex parameters. -/
def IsInducedConstituent {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r k : ℕ} {m : Fin k → ℕ}
    (hm : ∑ i, (m i + 1) = r + 1) {T : ∀ i, CuspidalOperatorRealization F (m i)}
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (Q : IrreducibleOperatorSubquotient F r) : Prop :=
  IsFiniteInducedConstituent hm P h Q ∧
    (∀ v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v},
      ∃ ds : Fin k → List RealBlock,
        (∀ i, (T i).realization.HasRealPlaceParameter v (ds i)) ∧
        Q.subquotient.HasRealPlaceStandardConstituent v (List.ofFn ds).flatten) ∧
    ∀ v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v},
      ∃ ds : Fin k → List ComplexCharacterData,
        (∀ i, (T i).realization.HasComplexPlaceParameter v (ds i)) ∧
        Q.subquotient.HasComplexPlaceStandardConstituent v (List.ofFn ds).flatten

end Langlands.Global

namespace Langlands.Automorphic.IrreducibleOperatorSubquotient

open Langlands.Global
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- `Q` has cuspidal support `D`: `Q` is an induced constituent, at every place, of actual
cuspidal realizations `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1`, read through
spectral presentations with irreducible admissible finite local components, whose
positive-rank cuspidal classes `⟨m i, [T i]⟩`, counted with multiplicity, form the
isobaric data `D`. -/
def HasCuspidalSupport (Q : IrreducibleOperatorSubquotient F r) (D : IsobaricData F) :
    Prop :=
  ∃ (k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
    IsInducedConstituent hm P h Q ∧
      Finset.univ.val.map
          (fun i => (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F)) = D

end Langlands.Automorphic.IrreducibleOperatorSubquotient

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient IsobaricData)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

/-- **Every automorphic representation has a cuspidal support, at every place**
(Langlands 1979, Proposition 2, "only if"; Getz–Hahn 2024, Theorem 10.7.1, second half,
with the remark after it on Langlands' Lemma 1). For every irreducible automorphic
operator subquotient `Q` of `GL_(r+1)` over a number field `F` there are `k`, ranks
`m i + 1` with `∑ (m i + 1) = r + 1`, actual cuspidal realizations `T i` of
`GL_(m i + 1)` and spectral presentations `P i` of them, with factors in the form-space
universe and irreducible admissible finite local components, such that `Q` is an induced
constituent of these data at every place. -/
def CuspidalSupportEveryPlaceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (Q : IrreducibleOperatorSubquotient F r),
    ∃ (k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
      (T : ∀ i, CuspidalOperatorRealization F (m i))
      (P : ∀ i, CuspidalSpectralPresentation.{u, u} (T i))
      (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
      IsInducedConstituent hm P h Q

/-- **The cuspidal support is well defined** (Getz–Hahn 2024, Theorem 10.7.1 and
Corollary 10.7.3, with the sentence after it). Every irreducible automorphic operator
subquotient `Q` of `GL_(r+1)` over a number field has exactly one cuspidal support: there
is a unique multiset `D` of positive-rank cuspidal classes such that `Q` is an induced
constituent, at every place, of cuspidal realizations whose classes form `D`. -/
def CuspidalSupportDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (Q : IrreducibleOperatorSubquotient F r),
    ∃! D : IsobaricData F, Q.HasCuspidalSupport.{u, u} D

/-- **Reduction of the cuspidal-support map to existence and uniqueness.** Existence of
cuspidal supports at every place, together with the uniqueness of finite cuspidal
supports (`CuspidalSupportUniquenessStatement`, Getz–Hahn 2024, Corollary 10.7.3), gives
a unique cuspidal support for every automorphic representation. -/
def CuspidalSupportDataReductionStatement : Prop :=
  CuspidalSupportEveryPlaceStatement.{u} →
    CuspidalSupportUniquenessStatement.{u, u} → CuspidalSupportDataStatement.{u}

/-- **An isobaric sum is a constituent of the representation induced from its summands**
(Getz–Hahn 2024, Theorem 10.7.5). Let `T i` (`i < k`) be actual cuspidal realizations of
`GL_(m i + 1)` over a number field `F`, with `∑ (m i + 1) = r + 1`, and spectral
presentations of them with irreducible admissible finite local components. If an
irreducible automorphic operator subquotient `Q` of `GL_(r+1)` is the isobaric sum of the
`T i` at every place, then `Q` is an induced constituent of the same data at every place.
By the definition of `HasCuspidalSupport`, such a `Q` then has as cuspidal support the
multiset of the classes of the `T i`. -/
def CuspidalIsobaricSupportStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (Q : IrreducibleOperatorSubquotient F r),
    Q.IsCuspidalIsobaricSum T P h → IsInducedConstituent hm P h Q

end Langlands.Global
