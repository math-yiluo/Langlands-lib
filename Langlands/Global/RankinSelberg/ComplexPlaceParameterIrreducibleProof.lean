import Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises
import Langlands.Global.RankinSelberg.ComplexPlaceStableOperator
import Langlands.Automorphic.PlaceComponentExistence
import Langlands.Automorphic.ComplexPlaceStandardIrreducible

/-! # The irreducibility premise at a complex place

This module proves `ComplexPlaceParameterIrreducibleStatement`: if an actual cuspidal
realization `T` of `GL_(r+1)` has the parameter `d` at a complex place `w`, the
`U(r+1)`-finite complex standard module `X(d)` is irreducible.

At `w`, the realization is a semisimple module, isotypic of the type of an irreducible place
component (`isSemisimple_isotypic_of_commutant`). The parameter embeds `X(d)` into it, so
`X(d)` is semisimple and isotypic too. A scalar vector of `X(d)` (`exists_isScalarVector`)
forces it to be simple (`isSimpleModule_of_scalar`). See the paired Markdown.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean
open Langlands.Automorphic.PlaceIsotypic

open Langlands.Global in
local instance complexIrreducibleRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
open Langlands.Global in
local instance complexIrreducibleContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
open Langlands.Global in
local instance complexIrreducibleSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
open Langlands.Global in
local instance complexIrreducibleFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
open Langlands.Global in
local instance complexIrreducibleStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance complexIrreducibleSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace ComplexPlaceIrreducible

variable {n : ℕ} {ds : List ComplexCharacterData}

theorem translate_eq_rep (k : unitaryCompact ℂ n) (f : complexStandardKFinite n ds) :
    complexStandardTranslate n ds k f = complexStandardRep n ds ⟨_, k.2⟩ f := by
  obtain ⟨_, e⟩ := (isComplexStandardIntertwining_id n ds).1 k f
  exact e

theorem derivative_eq_lie (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds) :
    complexStandardDerivative n ds X f = complexStandardLie n ds (1 ⊗ₜ X) f := by
  obtain ⟨_, e⟩ := (isComplexStandardIntertwining_id n ds).2 X f
  exact e

/-- A subspace stable under translations is stable under `complexStandardRep`. -/
theorem rep_mem {W : Submodule ℂ (complexStandardKFinite n ds)}
    (hWk : ∀ (k : unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
      f ∈ W → complexStandardTranslate n ds k f ∈ W)
    (k : Matrix.unitaryGroup (Fin n) ℂ) {f : complexStandardKFinite n ds} (hf : f ∈ W) :
    complexStandardRep n ds k f ∈ W := by
  have hk := hWk ⟨Unitary.toUnits k, k.2⟩ f hf
  rw [translate_eq_rep] at hk
  exact hk

/-- A subspace stable under derivatives is stable under `complexStandardLie`. -/
theorem lie_mem {W : Submodule ℂ (complexStandardKFinite n ds)}
    (hWX : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
      f ∈ W → complexStandardDerivative n ds X f ∈ W)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) {f : complexStandardKFinite n ds} (hf : f ∈ W) :
    complexStandardLie n ds Y f ∈ W := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, LinearMap.smul_apply]
    refine W.smul_mem z ?_
    have hX := hWX X f hf
    rw [derivative_eq_lie] at hX
    exact hX
  | add Y₁ Y₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem h₁ h₂

end ComplexPlaceIrreducible

open ComplexPlaceIrreducible

section Main

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (Langlands.Global.AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}
  {w : {v : NumberField.InfinitePlace F // v.IsComplex}}

/-- The standard module of a parameter of `T` at `w` is an irreducible `(𝔤, K)`-module. -/
theorem isIrreducibleGKModule_of_parameter {d : List ComplexCharacterData}
    (hd : T.realization.HasComplexPlaceParameter w d) :
    IsIrreducibleGKModule (complexStandardRep (r + 1) d) (complexStandardLie (r + 1) d) := by
  obtain ⟨hlen, A, hAinj, hAK, hAL⟩ := hd
  obtain ⟨W₀, hW₀, -⟩ := T.exists_complexPlaceComponent w
  exact isIrreducibleGKModule_of_embedding hW₀
    (fun Z hP hZ => OperatorRealization.IsComplexPlaceCommutantStable.eq_bot_or_eq_top
      ⟨hP, hZ.1, hZ.2⟩ T.irreducible) hlen hAinj ⟨hAK, hAL⟩

/-- The irreducibility premise for one realization, place and parameter. -/
theorem isComplexStandardIrreducible_of_parameter {d : List ComplexCharacterData}
    (hd : T.realization.HasComplexPlaceParameter w d) :
    IsComplexStandardIrreducible (r + 1) d := by
  have h := isIrreducibleGKModule_of_parameter hd
  exact ⟨h.1, fun W hWk hWX => h.2 W (fun k _ hf => rep_mem hWk k hf)
    (fun Y _ hf => lie_mem hWX Y hf)⟩

end Main

/-- **The irreducibility premise.** -/
theorem complexPlaceParameterIrreducible : ComplexPlaceParameterIrreducibleStatement.{u} :=
  fun _ _ _ _ _ _ _ _ hd => isComplexStandardIrreducible_of_parameter hd

end Langlands.Global.RankinSelbergGlobal
