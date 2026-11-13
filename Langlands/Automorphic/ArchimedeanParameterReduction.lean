import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction
import Langlands.Representation.Archimedean.GKModule

/-! # Reduction of the archimedean parameters of cuspidal realizations to local statements

`Langlands.Global.CuspidalArchimedeanParameterExistenceStatement` asks for a standard-module
parameter of every actual cuspidal realization at every infinite place. This file splits it
into two local statements and one global statement:

* `Archimedean.RealGenericStandardParameterStatement` and
  `Archimedean.ComplexGenericStandardParameterStatement`: every irreducible admissible generic
  `(𝔤, K)`-module of `GL_n(ℝ)`, resp. `GL_n(ℂ)`, has a standard-module parameter;
* `CuspidalArchimedeanGenericComponentStatement`: at every infinite place `v`, every actual
  cuspidal realization contains an irreducible admissible generic `(𝔤_v, K_v)`-module, given
  by an injective linear map intertwining its actions with the place actions at `v`.

`CuspidalArchimedeanParameterReductionStatement` says that the three imply the target and
`cuspidalArchimedeanParameterReduction` proves it by composing the two injective maps.
-/

noncomputable section

universe u

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- At the real place `v`, `S` contains an irreducible admissible generic
`(𝔤𝔩_n(ℝ), O(n))`-module: there are a complex vector space `V`, a
`(𝔤𝔩_n(ℝ), O(n))`-module structure `(ρ, π)` on `V` that is irreducible, admissible and
generic, and an injective linear map `ι : V → S` carrying `ρ(k)` to the compact action of
`k` at `v` and `π(X)` to the Lie action of `X` at `v`. -/
def HasRealPlaceGenericComponent (S : OperatorRealization F n) (v : RP) : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ι : V →ₗ[ℂ] S.Space),
    Function.Injective ι ∧
    (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (x : V),
      ι (ρ k x) = S.realPlaceCompactRepresentation v k (ι x)) ∧
    (∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (x : V),
      ι (π X x) = S.realPlaceLieAction v X (ι x)) ∧
    Archimedean.IsRealGKModule n ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
    Archimedean.IsAdmissibleGKModule ρ ∧ Archimedean.IsRealGenericGKModule n π

/-- At the complex place `v`, `S` contains an irreducible admissible generic
`(𝔤𝔩_n(ℂ), U(n))`-module, with `F_v` identified with `ℂ` as in the place actions: there are
a complex vector space `V`, an irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module
structure `(ρ, π)` on `V`, and an injective linear map `ι : V → S` carrying `ρ(k)` to the
compact action of `k` at `v` and `π(X)` to the Lie action of `X` at `v`. -/
def HasComplexPlaceGenericComponent (S : OperatorRealization F n) (v : CP) : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ι : V →ₗ[ℂ] S.Space),
    Function.Injective ι ∧
    (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x : V),
      ι (ρ k x) = S.complexPlaceCompactRepresentation v k (ι x)) ∧
    (∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (x : V),
      ι (π X x) = S.complexPlaceLieAction v X (ι x)) ∧
    Archimedean.IsComplexGKModule n ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
    Archimedean.IsAdmissibleGKModule ρ ∧ Archimedean.IsComplexGenericGKModule n π

/-- A generic component at a real place with a standard-module parameter gives the real
place parameter of `S`. -/
theorem hasRealPlaceParameter_of_component {S : OperatorRealization F n} {v : RP}
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {ι : V →ₗ[ℂ] S.Space} (hι : Function.Injective ι)
    (hρ : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (x : V),
      ι (ρ k x) = S.realPlaceCompactRepresentation v k (ι x))
    (hπ : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (x : V),
      ι (π X x) = S.realPlaceLieAction v X (ι x))
    {ds : List RealBlock} (h : Archimedean.HasRealStandardParameter n ρ π ds) :
    S.HasRealPlaceParameter v ds := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  exact ⟨hr, ι ∘ₗ A, hι.comp hA,
    fun k f => ⟨(hK k f).1, (congrArg ι (hK k f).2).trans (hρ _ _)⟩,
    fun X f => ⟨(hL X f).1, (congrArg ι (hL X f).2).trans (hπ _ _)⟩⟩

/-- A generic component at a complex place with a standard-module parameter gives the
complex place parameter of `S`. -/
theorem hasComplexPlaceParameter_of_component {S : OperatorRealization F n} {v : CP}
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {ι : V →ₗ[ℂ] S.Space} (hι : Function.Injective ι)
    (hρ : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x : V),
      ι (ρ k x) = S.complexPlaceCompactRepresentation v k (ι x))
    (hπ : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (x : V),
      ι (π X x) = S.complexPlaceLieAction v X (ι x))
    {ds : List ComplexCharacterData} (h : Archimedean.HasComplexStandardParameter n ρ π ds) :
    S.HasComplexPlaceParameter v ds := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  exact ⟨hr, ι ∘ₗ A, hι.comp hA,
    fun k f => ⟨(hK k f).1, (congrArg ι (hK k f).2).trans (hρ _ _)⟩,
    fun X f => ⟨(hL X f).1, (congrArg ι (hL X f).2).trans (hπ _ _)⟩⟩

end OperatorRealization

/-- Every actual cuspidal realization of `GL_{r+1}` over `F` contains, at every real place,
an irreducible admissible generic `(𝔤𝔩_{r+1}(ℝ), O(r+1))`-module and, at every complex
place, an irreducible admissible generic `(𝔤𝔩_{r+1}(ℂ), U(r+1))`-module, compatibly with
its place actions. -/
def CuspidalArchimedeanGenericComponentStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      OperatorRealization.HasRealPlaceGenericComponent T.realization v) ∧
    ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      OperatorRealization.HasComplexPlaceGenericComponent T.realization v

/-- The two local statements and the global statement imply the existence of archimedean
standard-module parameters of actual cuspidal realizations. -/
def CuspidalArchimedeanParameterReductionStatement : Prop :=
  Archimedean.RealGenericStandardParameterStatement.{u} →
    Archimedean.ComplexGenericStandardParameterStatement.{u} →
      CuspidalArchimedeanGenericComponentStatement.{u} →
        CuspidalArchimedeanParameterExistenceStatement.{u}

/-- The reduction: compose the injective map of the standard module into the generic
component with the injective map of the component into the realization. -/
theorem cuspidalArchimedeanParameterReduction :
    CuspidalArchimedeanParameterReductionStatement.{u} := by
  intro hR hC hG F _ _ _ r T
  refine ⟨fun v => ?_, fun v => ?_⟩
  · obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ := (hG F r T).1 v
    obtain ⟨ds, hds⟩ := hR (r + 1) V ρ π hgk hirr hadm hgen
    exact ⟨ds, OperatorRealization.hasRealPlaceParameter_of_component hι hρ hπ hds⟩
  · obtain ⟨V, _, _, ρ, π, ι, hι, hρ, hπ, hgk, hirr, hadm, hgen⟩ := (hG F r T).2 v
    obtain ⟨ds, hds⟩ := hC (r + 1) V ρ π hgk hirr hadm hgen
    exact ⟨ds, OperatorRealization.hasComplexPlaceParameter_of_component hι hρ hπ hds⟩

end Langlands.Automorphic
