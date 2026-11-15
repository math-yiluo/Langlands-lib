import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationStatement
import Langlands.Global.RankinSelberg.EqualEulerFactorizationStatement
import Langlands.Global.RankinSelberg.SchwartzBruhatStatement

/-! # Reduction of the equal-rank dual Euler factorization to the direct one

`EqualDualEulerFactorizationStatement` follows from `EqualEulerFactorizationStatement`
applied to the inverse character `ψ⁻¹` and the contragredient realizations, together with
`SchwartzBruhatStatement` and two further premises stated here: the contragredient
Whittaker identity `W̃_x = W^(ψ⁻¹)_(x̃)` (Cogdell 2004, pp.201 and 207) and the
unramified behaviour of the Fourier transform outside `S`. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.CuspidalPairBoundaryNonvanishing
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalDualReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalDualReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### Premises -/

/-- **Cogdell 2004, pp.201–202 and 206–207**: the contragredient Whittaker identity.

Let `ψ` be a unitary character of `𝔸` trivial on `F`, let `T` be an actual cuspidal
realization of `GL_(r+1)` and `Td` an actual cuspidal realization of its contragredient. For
every vector `x` of `T` fixed by `GL_(r+1)(𝒪_v)` at every finite place `v ∉ S` there is a
vector `xd` of `Td`, fixed by `GL_(r+1)(𝒪_v)` at every finite place `v ∉ S`, whose
`ψ⁻¹`-Whittaker function is `W̃_x(g) = W_x(w_n ᵗg⁻¹)`, where `W_x` is the
`ψ`-Whittaker function of `x`. In the source `xd` is the cusp form
`φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp form `φ` of `x`. -/
def ContragredientDualWhittakerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
  ∀ (S : Finset (FinitePlace F)) (x : T.Space), IsSphericalOutside F T S x →
    ∃ xd : Td.Space, IsSphericalOutside F Td S xd ∧
      cuspWhittaker F Td ψ.complex⁻¹ xd =
        dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)

/-- **Tate 1967 (thesis), §2.2, pp.309–311, the unramified local Fourier transform**,
used in Cogdell 2004, p.211 (`Φ̂ = ⊗ Φ̂_v`): if every finite component
`ψ_v`, `v ∉ S`, of the unitary character `ψ` of `𝔸` has conductor `𝒪_v`, and the function
`Φ` on `𝔸^n` is "equal to `1_(𝒪_v^n)` at every finite place `v ∉ S`" in the sense of
`IsStandardOutside` (it vanishes unless `x_v ∈ 𝒪_v^n` for all finite `v ∉ S`, and there it
depends only on the coordinates at the infinite places and at `S`), then so is its Fourier
transform `Φ̂`. -/
def FourierStandardOutsideStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (S : Finset (FinitePlace F)),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (n : ℕ) (Φ : RowVector F n → ℂ), IsStandardOutside F n S Φ →
    IsStandardOutside F n S (fourierTransform F n ψ.complex Φ)

/-- The reduction: the Euler factorization of the direct equal-rank integral, the
Schwartz–Bruhat facts, the contragredient Whittaker identity and the unramified Fourier
transform imply the Euler factorization of the dual equal-rank integral. -/
def EqualDualEulerFactorizationReductionStatement : Prop :=
  EqualEulerFactorizationStatement.{u, uQ} → SchwartzBruhatStatement.{u} →
    ContragredientDualWhittakerStatement.{u} → FourierStandardOutsideStatement.{u} →
    EqualDualEulerFactorizationStatement.{u, uQ}

/-! ### The inverse character -/

section Inverse

variable {A : Type*} [AddCommGroup A] {t : TopologicalSpace A}

/-- The inverse `ψ⁻¹(a) = ψ(-a) = ψ(a)⁻¹` of a unitary additive character. -/
def inverseCharacter (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) :
    HarmonicAnalysis.UnitaryAdditiveCharacter A where
  toAddChar := ψ.toAddChar⁻¹
  continuous_toFun := by
    have h : ⇑(ψ.toAddChar⁻¹) = fun a => (ψ.toAddChar a)⁻¹ :=
      funext (AddChar.inv_apply' ψ.toAddChar)
    rw [h]
    exact ψ.continuous_toFun.inv
  nontrivial h := ψ.nontrivial (inv_eq_one.mp h)

theorem inverseCharacter_apply (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) (a : A) :
    inverseCharacter ψ a = (ψ a)⁻¹ :=
  AddChar.inv_apply' ψ.toAddChar a

theorem complex_inverseCharacter (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter A) :
    (inverseCharacter ψ).complex = ψ.complex⁻¹ := by
  ext a
  rfl

end Inverse

/-- The inverse of a character trivial on `F` is trivial on `F`. -/
theorem inverseCharacter_rational {F : Type u} [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (x : F) :
    inverseCharacter ψ (algebraMap F (Adeles F) x) = 1 := by
  rw [inverseCharacter_apply, hψ x, inv_one]

/-- A local character and its inverse have the same conductor. -/
theorem additiveConductor_inverseCharacter {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}
    (T : K.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ T.topology) :
    T.additiveConductor (inverseCharacter ψ) = T.additiveConductor ψ := by
  have key : ∀ m : ℤ, T.AdditiveTrivialAt (inverseCharacter ψ) m ↔ T.AdditiveTrivialAt ψ m := by
    intro m
    constructor
    · intro h x hx
      have h' := h x hx
      rw [inverseCharacter_apply, inv_eq_one] at h'
      exact h'
    · intro h x hx
      rw [inverseCharacter_apply, h x hx, inv_one]
  apply le_antisymm
  · exact (T.additiveTrivialAt_iff_le_conductor ψ _).mp
      ((key _).mp (T.additiveConductor_spec (inverseCharacter ψ)).1)
  · exact (T.additiveTrivialAt_iff_le_conductor (inverseCharacter ψ) _).mp
      ((key _).mpr (T.additiveConductor_spec ψ).1)

/-- The finite components of `ψ⁻¹` are the inverses of those of `ψ`, with the same
conductors. -/
theorem finiteAdditiveSupport_inverseCharacter {F : Type u} [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (S : Finset (FinitePlace F))
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S) :
    FunctionalEquationComparison.FiniteAdditiveSupport (inverseCharacter ψ) S := by
  intro z hz
  obtain ⟨ψz, hcan, hcond⟩ := hS z hz
  refine ⟨inverseCharacter ψz, ?_, ?_⟩
  · intro x
    exact (inverseCharacter_apply ψz x).trans
      ((congrArg (·⁻¹) (hcan x)).trans (inverseCharacter_apply ψ _).symm)
  · rw [additiveConductor_inverseCharacter]
    exact hcond

/-- The complex form of a unitary character of `𝔸` trivial on `F` is standard. -/
theorem isStandardAdditiveCharacter_of_unitary {F : Type u} [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    IsStandardAdditiveCharacter F ψ.complex := by
  refine ⟨ψ.continuous_complex, fun h1 => ψ.nontrivial ?_, fun x => ?_, ψ.norm_complex⟩
  · ext x
    have hx := congrArg (fun χ : AddChar (Adeles F) ℂ => χ x) h1
    simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      AddChar.one_apply] at hx
    rw [AddChar.one_apply, Circle.coe_one]
    exact hx
  · rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, hψ x, Circle.coe_one]

/-! ### The reduction -/

theorem equalDualEulerFactorizationReduction :
    EqualDualEulerFactorizationReductionStatement.{u, uQ} := by
  intro hEuler hSB hDual hFourier F _ _ _ ψ hψ r T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hS
  have hψi := inverseCharacter_rational ψ hψ
  obtain ⟨σ, hσ⟩ := hEuler F (inverseCharacter ψ) hψi r Td Td' Pd Pd' S hPd hPd'
    (finiteAdditiveSupport_inverseCharacter ψ S hS)
  refine ⟨σ, ?_⟩
  intro x x' Φ hx hx' hΦ hΦS
  obtain ⟨xd, hxd, hW⟩ := hDual F ψ hψ r T Td hTd S x hx
  obtain ⟨xd', hxd', hW'⟩ := hDual F (inverseCharacter ψ) hψi r T' Td' hTd' S x' hx'
  rw [complex_inverseCharacter, inv_inv] at hW'
  have hΦhat : fourierTransform F (r + 1) ψ.complex Φ ∈ schwartzBruhat F (r + 1) :=
    ((hSB F (r + 1)).2 ψ.complex (isStandardAdditiveCharacter_of_unitary ψ hψ) Φ hΦ).2.1
  have hΦhatS : IsStandardOutside F (r + 1) S (fourierTransform F (r + 1) ψ.complex Φ) :=
    hFourier F ψ S hS (r + 1) Φ hΦS
  have H := hσ xd xd' (fourierTransform F (r + 1) ψ.complex Φ) hxd hxd' hΦhat hΦhatS
  rw [complex_inverseCharacter, inv_inv, hW, hW'] at H
  exact H

end Langlands.Global.RankinSelbergGlobal
