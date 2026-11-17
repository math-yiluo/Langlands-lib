import Langlands.Global.RankinSelberg.RealPlaceStableOperator
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-!
# Isotypy at a real place of an irreducible realization with a given parameter

Let `S` be an operator realization of `GL_n` over a number field, `w` a real place and `ds`
a list of real blocks. A `(𝔤, K)`-map at `w` (`IsRealPlaceMap`) is a linear map from
the `O(n)`-finite functions of the real standard module of `ds` into `S` carrying right
translation by `O(n)` and right derivatives along real directions of `𝔤𝔩_n(ℝ)` to the compact
and Lie place actions at `w`. The sum `realPlaceIsotypic` of their images is stable under
the place actions at `w` and under every endomorphism commuting with them. If `S` is
irreducible and has the parameter `ds` at `w`, this sum is all of `S`
(`realPlaceIsotypic_eq_top`).
-/

noncomputable section
universe u
open scoped TensorProduct Manifold ContDiff
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

local instance bridgeRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance bridgeContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance bridgeSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance bridgeFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance bridgeStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance bridgeSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ

variable (S : OperatorRealization F n)

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- `A` is a `(𝔤, K)`-map at the real place `w` from the `O(n)`-finite standard module of
`ds` into `S`: it carries right translation by `k ∈ O(n)` to the compact action of `k` at `w`
and the right derivative along a real direction `X ∈ 𝔤𝔩_n(ℝ)` to the Lie action of `X` at
`w`. These are the clauses of `HasRealPlaceParameter`, without injectivity. -/
def IsRealPlaceMap (w : RP) (ds : List RealBlock)
    (A : realStandardKFinite n ds →ₗ[ℂ] S.Space) : Prop :=
  (∀ (k : Archimedean.unitaryCompact ℝ n) (f : realStandardKFinite n ds),
      ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            realStandardKFinite n ds,
        A ⟨_, hf⟩ = S.realPlaceCompactRepresentation w
          ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A f)) ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds),
      ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℝ n) X
          (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ realStandardKFinite n ds,
        A ⟨_, hf⟩ = S.realPlaceLieAction w (1 ⊗ₜ X) (A f)

/-- The sum of the images of all `(𝔤, K)`-maps at `w` from the standard module of `ds`. -/
def realPlaceIsotypic (w : RP) (ds : List RealBlock) : Submodule ℂ S.Space :=
  ⨆ A : {A : realStandardKFinite n ds →ₗ[ℂ] S.Space // S.IsRealPlaceMap w ds A},
    LinearMap.range A.1

variable {S}

theorem apply_mem_realPlaceIsotypic {w : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsRealPlaceMap w ds A)
    (f : realStandardKFinite n ds) : A f ∈ S.realPlaceIsotypic w ds :=
  Submodule.mem_iSup_of_mem (⟨A, hA⟩ : {A : realStandardKFinite n ds →ₗ[ℂ] S.Space //
    S.IsRealPlaceMap w ds A}) ⟨f, rfl⟩

/-- A linear endomorphism maps the sum of images into itself as soon as it maps every image
generator into it. -/
theorem realPlaceIsotypic_stable {w : RP} {ds : List RealBlock}
    (E : S.Space →ₗ[ℂ] S.Space)
    (hE : ∀ (A : realStandardKFinite n ds →ₗ[ℂ] S.Space), S.IsRealPlaceMap w ds A →
      ∀ f, E (A f) ∈ S.realPlaceIsotypic w ds) :
    ∀ x ∈ S.realPlaceIsotypic w ds, E x ∈ S.realPlaceIsotypic w ds := by
  intro x hx
  have hle : S.realPlaceIsotypic w ds ≤ (S.realPlaceIsotypic w ds).comap E := by
    refine iSup_le fun A => ?_
    rintro _ ⟨f, rfl⟩
    exact hE A.1 A.2 f
  exact hle hx

/-- Composing a `(𝔤, K)`-map with an endomorphism commuting with the place actions gives a
`(𝔤, K)`-map. -/
theorem IsRealPlaceMap.comp {w : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsRealPlaceMap w ds A)
    (P : S.Space →ₗ[ℂ] S.Space)
    (hPκ : ∀ (k : RK) (y : S.Space),
      P (S.realPlaceCompactRepresentation w k y) =
        S.realPlaceCompactRepresentation w k (P y))
    (hPπ : ∀ (X : ℂ ⊗[ℝ] RM) (y : S.Space),
      P (S.realPlaceLieAction w X y) = S.realPlaceLieAction w X (P y)) :
    S.IsRealPlaceMap w ds (P ∘ₗ A) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, he⟩ := hA.1 k f
    exact ⟨hf, (congrArg P he).trans (hPκ _ _)⟩
  · exact Exists.elim (hA.2 X f) fun hf he => ⟨hf, (congrArg P he).trans (hPπ _ _)⟩

/-- The image of a `(𝔤, K)`-map is stable under the compact action at `w`. -/
theorem IsRealPlaceMap.compact_mem_range {w : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsRealPlaceMap w ds A)
    (l : RK) (f : realStandardKFinite n ds) :
    S.realPlaceCompactRepresentation w l (A f) ∈ LinearMap.range A := by
  obtain ⟨hf, he⟩ := hA.1 ⟨Unitary.toUnits l, l.2⟩ f
  exact ⟨_, he⟩

/-- The image of a `(𝔤, K)`-map is stable under the Lie action at `w`. -/
theorem IsRealPlaceMap.lie_mem_range {w : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] S.Space} (hA : S.IsRealPlaceMap w ds A)
    (X : ℂ ⊗[ℝ] RM) (f : realStandardKFinite n ds) :
    S.realPlaceLieAction w X (A f) ∈ LinearMap.range A := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.realPlaceLieAction w (z ⊗ₜ[ℝ] X) (A f) =
        z • S.realPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (A f) :=
      (congrArg (fun Y => S.realPlaceLieAction w Y (A f)) hzX).trans
        (LinearMap.congr_fun ((S.realPlaceLieAction w).map_smul z ((1 : ℂ) ⊗ₜ[ℝ] X)) (A f))
    have hmem : S.realPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (A f) ∈ LinearMap.range A :=
      Exists.elim (hA.2 X f) fun _ he => ⟨_, he⟩
    exact (congrArg (fun y => y ∈ LinearMap.range A) heq).mpr (Submodule.smul_mem _ z hmem)
  | add X Y hX hY =>
    have heq : S.realPlaceLieAction w (X + Y) (A f) =
        S.realPlaceLieAction w X (A f) + S.realPlaceLieAction w Y (A f) :=
      LinearMap.congr_fun ((S.realPlaceLieAction w).map_add X Y) (A f)
    exact (congrArg (fun y => y ∈ LinearMap.range A) heq).mpr (Submodule.add_mem _ hX hY)

/-- The sum of the images of all `(𝔤, K)`-maps at `w` is stable under the place actions at `w`
and under their commutant. -/
theorem realPlaceIsotypic_isRealPlaceCommutantStable (w : RP)
    (ds : List RealBlock) :
    S.IsRealPlaceCommutantStable w (S.realPlaceIsotypic w ds) := by
  refine ⟨fun P hPκ hPπ => ?_, fun k => ?_, fun X => ?_⟩
  · exact realPlaceIsotypic_stable P fun A hA f =>
      apply_mem_realPlaceIsotypic (hA.comp P hPκ hPπ) f
  · refine realPlaceIsotypic_stable (S.realPlaceCompactRepresentation w k) fun A hA f => ?_
    obtain ⟨f', hf'⟩ := hA.compact_mem_range k f
    exact (congrArg (fun y => y ∈ S.realPlaceIsotypic w ds) hf').mp
      (apply_mem_realPlaceIsotypic hA f')
  · refine realPlaceIsotypic_stable (S.realPlaceLieAction w X) fun A hA f => ?_
    exact (LinearMap.mem_range.mp (hA.lie_mem_range X f)).elim fun f' hf' =>
      (congrArg (fun y => y ∈ S.realPlaceIsotypic w ds) hf').mp
        (apply_mem_realPlaceIsotypic hA f')

/-- **Isotypy.** If an irreducible realization `S` has the parameter `ds` at the real place
`w`, every vector of `S` lies in the sum of the images of the `(𝔤, K)`-maps at `w` from the
standard module of `ds`. -/
theorem realPlaceIsotypic_eq_top (hS : S.IsIrreducible) {w : RP}
    {ds : List RealBlock} (hd : S.HasRealPlaceParameter w ds) :
    S.realPlaceIsotypic w ds = ⊤ := by
  obtain ⟨hlen, A, hinj, hκ, hπ⟩ := hd
  have hA : S.IsRealPlaceMap w ds A := ⟨hκ, hπ⟩
  have := Archimedean.realStandardNontrivial n ds hlen
  rcases (realPlaceIsotypic_isRealPlaceCommutantStable (S := S) w ds).eq_bot_or_eq_top
    hS with h | h
  · exfalso
    obtain ⟨f, hf⟩ := exists_ne (0 : realStandardKFinite n ds)
    have hmem := apply_mem_realPlaceIsotypic hA f
    rw [h, Submodule.mem_bot] at hmem
    exact hf (hinj (hmem.trans (map_zero A).symm))
  · exact h

end OperatorRealization

end Langlands.Automorphic
