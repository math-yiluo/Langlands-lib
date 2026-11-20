import Langlands.Global.RankinSelberg.ComplexPlaceStableOperator
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof

/-!
# Isotypy at a complex place of an irreducible realization with a given parameter

Let `S` be an operator realization of `GL_n` over a number field, `w` a complex place and `ds`
a list of complex characters. A `(𝔤, K)`-map at `w` (`IsComplexPlaceMap`) is a linear map from
the `U(n)`-finite functions of the complex standard module of `ds` into `S` carrying right
translation by `U(n)` and right derivatives along real directions of `𝔤𝔩_n(ℂ)` to the compact
and Lie place actions at `w`. The sum `complexPlaceIsotypic` of their images is stable under
the place actions at `w` and under every endomorphism commuting with them. If `S` is
irreducible and has the parameter `ds` at `w`, this sum is all of `S`
(`complexPlaceIsotypic_eq_top`).
-/

noncomputable section
universe u
open scoped TensorProduct Manifold ContDiff
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

private local instance bridgeRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance bridgeContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance bridgeSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance bridgeFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance bridgeStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance bridgeSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

variable (S : OperatorRealization F n)

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- `A` is a `(𝔤, K)`-map at the complex place `w` from the `U(n)`-finite standard module of
`ds` into `S`: it carries right translation by `k ∈ U(n)` to the compact action of `k` at `w`
and the right derivative along a real direction `X ∈ 𝔤𝔩_n(ℂ)` to the Lie action of `X` at
`w`. These are the clauses of `HasComplexPlaceParameter`, without injectivity. -/
def IsComplexPlaceMap (w : CP) (ds : List ComplexCharacterData)
    (A : complexStandardKFinite n ds →ₗ[ℂ] S.Space) : Prop :=
  (∀ (k : Archimedean.unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
      ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
          (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
            complexStandardKFinite n ds,
        A ⟨_, hf⟩ = S.complexPlaceCompactRepresentation w
          ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f)) ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
      ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
          (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ complexStandardKFinite n ds,
        A ⟨_, hf⟩ = S.complexPlaceLieAction w (1 ⊗ₜ X) (A f)

/-- The sum of the images of all `(𝔤, K)`-maps at `w` from the standard module of `ds`. -/
def complexPlaceIsotypic (w : CP) (ds : List ComplexCharacterData) : Submodule ℂ S.Space :=
  ⨆ A : {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space // S.IsComplexPlaceMap w ds A},
    LinearMap.range A.1

variable {S}

theorem apply_mem_complexPlaceIsotypic {w : CP} {ds : List ComplexCharacterData}
    {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsComplexPlaceMap w ds A)
    (f : complexStandardKFinite n ds) : A f ∈ S.complexPlaceIsotypic w ds :=
  Submodule.mem_iSup_of_mem (⟨A, hA⟩ : {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space //
    S.IsComplexPlaceMap w ds A}) ⟨f, rfl⟩

/-- A linear endomorphism maps the sum of images into itself as soon as it maps every image
generator into it. -/
theorem complexPlaceIsotypic_stable {w : CP} {ds : List ComplexCharacterData}
    (E : S.Space →ₗ[ℂ] S.Space)
    (hE : ∀ (A : complexStandardKFinite n ds →ₗ[ℂ] S.Space), S.IsComplexPlaceMap w ds A →
      ∀ f, E (A f) ∈ S.complexPlaceIsotypic w ds) :
    ∀ x ∈ S.complexPlaceIsotypic w ds, E x ∈ S.complexPlaceIsotypic w ds := by
  intro x hx
  have hle : S.complexPlaceIsotypic w ds ≤ (S.complexPlaceIsotypic w ds).comap E := by
    refine iSup_le fun A => ?_
    rintro _ ⟨f, rfl⟩
    exact hE A.1 A.2 f
  exact hle hx

/-- Composing a `(𝔤, K)`-map with an endomorphism commuting with the place actions gives a
`(𝔤, K)`-map. -/
theorem IsComplexPlaceMap.comp {w : CP} {ds : List ComplexCharacterData}
    {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsComplexPlaceMap w ds A)
    (P : S.Space →ₗ[ℂ] S.Space)
    (hPκ : ∀ (k : CK) (y : S.Space),
      P (S.complexPlaceCompactRepresentation w k y) =
        S.complexPlaceCompactRepresentation w k (P y))
    (hPπ : ∀ (X : ℂ ⊗[ℝ] CM) (y : S.Space),
      P (S.complexPlaceLieAction w X y) = S.complexPlaceLieAction w X (P y)) :
    S.IsComplexPlaceMap w ds (P ∘ₗ A) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, he⟩ := hA.1 k f
    exact ⟨hf, (congrArg P he).trans (hPκ _ _)⟩
  · exact Exists.elim (hA.2 X f) fun hf he => ⟨hf, (congrArg P he).trans (hPπ _ _)⟩

/-- The image of a `(𝔤, K)`-map is stable under the compact action at `w`. -/
theorem IsComplexPlaceMap.compact_mem_range {w : CP} {ds : List ComplexCharacterData}
    {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsComplexPlaceMap w ds A)
    (l : CK) (f : complexStandardKFinite n ds) :
    S.complexPlaceCompactRepresentation w l (A f) ∈ LinearMap.range A := by
  obtain ⟨hf, he⟩ := hA.1 ⟨Unitary.toUnits l, l.2⟩ f
  exact ⟨_, he⟩

/-- The image of a `(𝔤, K)`-map is stable under the Lie action at `w`. -/
theorem IsComplexPlaceMap.lie_mem_range {w : CP} {ds : List ComplexCharacterData}
    {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsComplexPlaceMap w ds A)
    (X : ℂ ⊗[ℝ] CM) (f : complexStandardKFinite n ds) :
    S.complexPlaceLieAction w X (A f) ∈ LinearMap.range A := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.complexPlaceLieAction w (z ⊗ₜ[ℝ] X) (A f) =
        z • S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (A f) :=
      (congrArg (fun Y => S.complexPlaceLieAction w Y (A f)) hzX).trans
        (LinearMap.congr_fun ((S.complexPlaceLieAction w).map_smul z ((1 : ℂ) ⊗ₜ[ℝ] X)) (A f))
    have hmem : S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (A f) ∈ LinearMap.range A :=
      Exists.elim (hA.2 X f) fun _ he => ⟨_, he⟩
    exact (congrArg (fun y => y ∈ LinearMap.range A) heq).mpr (Submodule.smul_mem _ z hmem)
  | add X Y hX hY =>
    have heq : S.complexPlaceLieAction w (X + Y) (A f) =
        S.complexPlaceLieAction w X (A f) + S.complexPlaceLieAction w Y (A f) :=
      LinearMap.congr_fun ((S.complexPlaceLieAction w).map_add X Y) (A f)
    exact (congrArg (fun y => y ∈ LinearMap.range A) heq).mpr (Submodule.add_mem _ hX hY)

/-- The sum of the images of all `(𝔤, K)`-maps at `w` is stable under the place actions at `w`
and under their commutant. -/
theorem complexPlaceIsotypic_isComplexPlaceCommutantStable (w : CP)
    (ds : List ComplexCharacterData) :
    S.IsComplexPlaceCommutantStable w (S.complexPlaceIsotypic w ds) := by
  refine ⟨fun P hPκ hPπ => ?_, fun k => ?_, fun X => ?_⟩
  · exact complexPlaceIsotypic_stable P fun A hA f =>
      apply_mem_complexPlaceIsotypic (hA.comp P hPκ hPπ) f
  · refine complexPlaceIsotypic_stable (S.complexPlaceCompactRepresentation w k) fun A hA f => ?_
    obtain ⟨f', hf'⟩ := hA.compact_mem_range k f
    exact (congrArg (fun y => y ∈ S.complexPlaceIsotypic w ds) hf').mp
      (apply_mem_complexPlaceIsotypic hA f')
  · refine complexPlaceIsotypic_stable (S.complexPlaceLieAction w X) fun A hA f => ?_
    exact (LinearMap.mem_range.mp (hA.lie_mem_range X f)).elim fun f' hf' =>
      (congrArg (fun y => y ∈ S.complexPlaceIsotypic w ds) hf').mp
        (apply_mem_complexPlaceIsotypic hA f')

/-- **Isotypy.** If an irreducible realization `S` has the parameter `ds` at the complex place
`w`, every vector of `S` lies in the sum of the images of the `(𝔤, K)`-maps at `w` from the
standard module of `ds`. -/
theorem complexPlaceIsotypic_eq_top (hS : S.IsIrreducible) {w : CP}
    {ds : List ComplexCharacterData} (hd : S.HasComplexPlaceParameter w ds) :
    S.complexPlaceIsotypic w ds = ⊤ := by
  obtain ⟨hlen, A, hinj, hκ, hπ⟩ := hd
  have hA : S.IsComplexPlaceMap w ds A := ⟨hκ, hπ⟩
  have := Archimedean.complexStandardNontrivial n ds hlen
  rcases (complexPlaceIsotypic_isComplexPlaceCommutantStable (S := S) w ds).eq_bot_or_eq_top
    hS with h | h
  · exfalso
    obtain ⟨f, hf⟩ := exists_ne (0 : complexStandardKFinite n ds)
    have hmem := apply_mem_complexPlaceIsotypic hA f
    rw [h, Submodule.mem_bot] at hmem
    exact hf (hinj (hmem.trans (map_zero A).symm))
  · exact h

end OperatorRealization

end Langlands.Automorphic
