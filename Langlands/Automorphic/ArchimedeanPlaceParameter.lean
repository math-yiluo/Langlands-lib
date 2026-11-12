import Langlands.Automorphic.PlaceCompactAction
import Langlands.Automorphic.PlaceLieAction
import Langlands.Automorphic.CuspidalOperatorRealization
import Langlands.Representation.Archimedean.StandardModule

/-! # Archimedean Langlands parameters of actual automorphic realizations

At an infinite place `v` of `F`, an actual automorphic operator realization carries the
`(𝔤_v, K_v)`-module structure of its published place actions. It has the standard-module
parameter of a list of archimedean Weil blocks at `v` when the `K`-finite functions of the
standard module of the blocks map injectively and `(𝔤, K)`-equivariantly into the
realization. The property is invariant under equivalence and descends to isomorphism classes,
in particular to actual cuspidal classes. No parameter is constructed or asserted to exist.
-/

noncomputable section

universe u

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance placeParameterRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeParameterContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeParameterSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeParameterFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeParameterStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (n) in
/-- The `(𝔤, K)`-module of the real standard module of the blocks `ds`: its `O(n)`-finite
functions. -/
abbrev realStandardKFinite (ds : List RealBlock) :
    Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
  Archimedean.kFiniteFunctions (Archimedean.realStandardModule n ds)
    (Archimedean.unitaryCompact ℝ n)

variable (n) in
/-- The `(𝔤, K)`-module of the complex standard module of the blocks `ds`: its
`U(n)`-finite functions. -/
abbrev complexStandardKFinite (ds : List ComplexCharacterData) :
    Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  Archimedean.kFiniteFunctions (Archimedean.complexStandardModule n ds)
    (Archimedean.unitaryCompact ℂ n)

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance placeParameterSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance placeParameterTargetAddCommGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- `S` has the standard-module parameter of the real blocks `ds` at the real place `v`: the
blocks have total rank `n`, and there is an injective linear map from the `O(n)`-finite
functions of their standard module into `S` carrying right translation by `k ∈ O(n)` to the
compact action of `k` at `v`, and the right derivative along `X ∈ 𝔤𝔩_n(ℝ)` to the Lie action
of `X` at `v`. -/
def HasRealPlaceParameter (v : RP) (ds : List RealBlock) : Prop :=
  realRank ds = n ∧
    ∃ A : realStandardKFinite n ds →ₗ[ℂ] S.Space, Function.Injective A ∧
      (∀ (k : Archimedean.unitaryCompact ℝ n) (f : realStandardKFinite n ds),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
            (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
              realStandardKFinite n ds,
          A ⟨_, hf⟩ = S.realPlaceCompactRepresentation v
            ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A f)) ∧
      ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℝ n) X
            (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ realStandardKFinite n ds,
          A ⟨_, hf⟩ = S.realPlaceLieAction v (1 ⊗ₜ X) (A f)

/-- `S` has the standard-module parameter of the complex blocks `ds` at the complex place `v`,
with `F_v` identified with `ℂ` as in the published place actions: there are `n` blocks, and
there is an injective linear map from the `U(n)`-finite functions of their standard module into
`S` carrying right translation by `k ∈ U(n)` to the compact action of `k` at `v`, and the right
derivative along a real direction `X ∈ 𝔤𝔩_n(ℂ)` to the Lie action of `X` at `v`. -/
def HasComplexPlaceParameter (v : CP) (ds : List ComplexCharacterData) : Prop :=
  ds.length = n ∧
    ∃ A : complexStandardKFinite n ds →ₗ[ℂ] S.Space, Function.Injective A ∧
      (∀ (k : Archimedean.unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
            (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
              complexStandardKFinite n ds,
          A ⟨_, hf⟩ = S.complexPlaceCompactRepresentation v
            ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f)) ∧
      ∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
            (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ complexStandardKFinite n ds,
          A ⟨_, hf⟩ = S.complexPlaceLieAction v (1 ⊗ₜ X) (A f)

variable {S T}

/-- A full equivalence carries the compact action at a real place. -/
theorem equivalence_realPlaceCompact (e : S.Equivalence T) (v : RP)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (x : S.Space) :
    e.toLinearEquiv (S.realPlaceCompactRepresentation v k x) =
      T.realPlaceCompactRepresentation v k (e.toLinearEquiv x) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (Intertwiner.realPlaceCompactRestriction e.toIntertwiningMap v) k x

/-- A full equivalence carries the compact action at a complex place. -/
theorem equivalence_complexPlaceCompact (e : S.Equivalence T) (v : CP)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (x : S.Space) :
    e.toLinearEquiv (S.complexPlaceCompactRepresentation v k x) =
      T.complexPlaceCompactRepresentation v k (e.toLinearEquiv x) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (Intertwiner.complexPlaceCompactRestriction e.toIntertwiningMap v) k x

/-- A full equivalence carries the Lie action at a real place. -/
theorem equivalence_realPlaceLie (e : S.Equivalence T) (v : RP)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (x : S.Space) :
    e.toLinearEquiv (S.realPlaceLieAction v X x) =
      T.realPlaceLieAction v X (e.toLinearEquiv x) :=
  Intertwiner.realPlaceLieAction e.toIntertwiningMap v X x

/-- A full equivalence carries the Lie action at a complex place. -/
theorem equivalence_complexPlaceLie (e : S.Equivalence T) (v : CP)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (x : S.Space) :
    e.toLinearEquiv (S.complexPlaceLieAction v X x) =
      T.complexPlaceLieAction v X (e.toLinearEquiv x) :=
  Intertwiner.complexPlaceLieAction e.toIntertwiningMap v X x

/-- The real place parameter is transported along a full equivalence. -/
theorem HasRealPlaceParameter.of_equiv (e : S.Equivalence T) {v : RP} {ds : List RealBlock}
    (h : S.HasRealPlaceParameter v ds) : T.HasRealPlaceParameter v ds := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  exact ⟨hr, e.toLinearEquiv.toLinearMap ∘ₗ A, e.toLinearEquiv.injective.comp hA,
    fun k f => ⟨(hK k f).1,
      (congrArg e.toLinearEquiv (hK k f).2).trans (equivalence_realPlaceCompact e v _ _)⟩,
    fun X f => ⟨(hL X f).1,
      (congrArg e.toLinearEquiv (hL X f).2).trans (equivalence_realPlaceLie e v _ _)⟩⟩

/-- The complex place parameter is transported along a full equivalence. -/
theorem HasComplexPlaceParameter.of_equiv (e : S.Equivalence T) {v : CP}
    {ds : List ComplexCharacterData} (h : S.HasComplexPlaceParameter v ds) :
    T.HasComplexPlaceParameter v ds := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  exact ⟨hr, e.toLinearEquiv.toLinearMap ∘ₗ A, e.toLinearEquiv.injective.comp hA,
    fun k f => ⟨(hK k f).1,
      (congrArg e.toLinearEquiv (hK k f).2).trans (equivalence_complexPlaceCompact e v _ _)⟩,
    fun X f => ⟨(hL X f).1,
      (congrArg e.toLinearEquiv (hL X f).2).trans (equivalence_complexPlaceLie e v _ _)⟩⟩

/-- The real place parameter is a property of the isomorphism class. -/
def IsoClass.HasRealPlaceParameter (c : IsoClass F n) (v : RP) (ds : List RealBlock) :
    Prop :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun S : OperatorRealization F n => S.HasRealPlaceParameter v ds)
    (fun S T (h : Nonempty (S.Equivalence T)) =>
      h.elim fun e => propext ⟨fun hS => hS.of_equiv e, fun hT => hT.of_equiv e.symm⟩) c

/-- The complex place parameter is a property of the isomorphism class. -/
def IsoClass.HasComplexPlaceParameter (c : IsoClass F n) (v : CP)
    (ds : List ComplexCharacterData) : Prop :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun S : OperatorRealization F n => S.HasComplexPlaceParameter v ds)
    (fun S T (h : Nonempty (S.Equivalence T)) =>
      h.elim fun e => propext ⟨fun hS => hS.of_equiv e, fun hT => hT.of_equiv e.symm⟩) c

variable (S)

@[simp]
theorem isoClass_hasRealPlaceParameter (v : RP) (ds : List RealBlock) :
    S.isoClass.HasRealPlaceParameter v ds ↔ S.HasRealPlaceParameter v ds :=
  Iff.rfl

@[simp]
theorem isoClass_hasComplexPlaceParameter (v : CP) (ds : List ComplexCharacterData) :
    S.isoClass.HasComplexPlaceParameter v ds ↔ S.HasComplexPlaceParameter v ds :=
  Iff.rfl

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The real place parameter of an actual cuspidal class of `GL_{r+1}`. -/
def IsoClass.HasRealPlaceParameter (c : IsoClass F r) (v : RP) (ds : List RealBlock) : Prop :=
  c.toOperatorClass.HasRealPlaceParameter v ds

/-- The complex place parameter of an actual cuspidal class of `GL_{r+1}`. -/
def IsoClass.HasComplexPlaceParameter (c : IsoClass F r) (v : CP)
    (ds : List ComplexCharacterData) : Prop :=
  c.toOperatorClass.HasComplexPlaceParameter v ds

@[simp]
theorem isoClass_hasRealPlaceParameter (S : CuspidalOperatorRealization F r) (v : RP)
    (ds : List RealBlock) :
    S.isoClass.HasRealPlaceParameter v ds ↔ S.realization.HasRealPlaceParameter v ds :=
  Iff.rfl

@[simp]
theorem isoClass_hasComplexPlaceParameter (S : CuspidalOperatorRealization F r) (v : CP)
    (ds : List ComplexCharacterData) :
    S.isoClass.HasComplexPlaceParameter v ds ↔ S.realization.HasComplexPlaceParameter v ds :=
  Iff.rfl

end CuspidalOperatorRealization

end Langlands.Automorphic
