import Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises
import Langlands.Automorphic.PlaceComponentRealization
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof

/-! # Reduction of the contragredient-parameter premise

This module proves `ComplexPlaceContragredientParameterReductionStatement`: the premise
`ComplexPlaceContragredientParameterStatement` of the complex-place functional-equation
reduction follows from the irreducibility premise `ComplexPlaceParameterIrreducibleStatement`
and the local pairing premise `ComplexStandardPairingParameterStatement` (both stated, not
proved, in `ComplexPlaceContragredientPremises`).

The proved content is `exists_complexStandardInvariantPairing`: the contragredient pairing of
`T` and `Td` restricts, through the embeddings of the parameters, to a nonzero invariant
pairing of the two standard modules. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField
open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean
open Langlands.Global.ArchimedeanGL

/-! ### Place-equivariant maps and the annihilator -/

namespace ComplexPlaceContragredient

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance contraRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance contraContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance contraSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance contraFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance contraStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance contraSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The element of `U(n) ⊆ GL_n(ℂ)` underlying a unitary matrix. -/
def ofUnitary (l : CK) : unitaryCompact ℂ n :=
  ⟨Unitary.toUnits l, l.2⟩

theorem ofUnitary_unitaryGroup (l : CK) :
    (⟨(((ofUnitary l : unitaryCompact ℂ n) : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ), (ofUnitary l).2⟩ : CK) = l := rfl

/-- `Φ` is equivariant for the actions at the complex place `w`: it carries right translation
by `k ∈ U(n)` and the right derivative along `X ∈ 𝔤𝔩_n(ℂ)` to the compact and Lie actions at
`w`. -/
def IsPlaceEquivariant (S : OperatorRealization F n) (w : CP) (ds : List ComplexCharacterData)
    (Φ : complexStandardKFinite n ds →ₗ[ℂ] S.Space) : Prop :=
  (∀ (k : unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
      Φ (complexStandardTranslate n ds k f) =
        S.complexPlaceCompactRepresentation w
          ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (Φ f)) ∧
    ∀ (X : CM) (f : complexStandardKFinite n ds),
      Φ (complexStandardDerivative n ds X f) =
        S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (Φ f)

set_option backward.isDefEq.respectTransparency false in
/-- The map of a parameter is place-equivariant. -/
theorem isPlaceEquivariant_of_parameter (S : OperatorRealization F n) (w : CP)
    (ds : List ComplexCharacterData) (A : complexStandardKFinite n ds →ₗ[ℂ] S.Space)
    (hK : ∀ (k : Archimedean.unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
            (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
              complexStandardKFinite n ds,
          A ⟨_, hf⟩ = S.complexPlaceCompactRepresentation w
            ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f))
    (hX : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
            (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ complexStandardKFinite n ds,
          A ⟨_, hf⟩ = S.complexPlaceLieAction w (1 ⊗ₜ X) (A f)) :
    IsPlaceEquivariant S w ds A := by
  exact ⟨fun k f => (hK k f).2, fun X f => (hX X f).2⟩

/-- Composing a place-equivariant map with an operator commuting with the actions at `w`
gives a place-equivariant map. -/
theorem IsPlaceEquivariant.comp {S : OperatorRealization F n} {w : CP}
    {ds : List ComplexCharacterData} {Φ : complexStandardKFinite n ds →ₗ[ℂ] S.Space}
    (hΦ : IsPlaceEquivariant S w ds Φ) (c : S.Space →ₗ[ℂ] S.Space)
    (hck : ∀ (l : CK) (x : S.Space),
      c (S.complexPlaceCompactRepresentation w l x) = S.complexPlaceCompactRepresentation w l (c x))
    (hcX : ∀ (X : CM) (x : S.Space),
      c (S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x) =
        S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (c x)) :
    IsPlaceEquivariant S w ds (c ∘ₗ Φ) := by
  exact ⟨fun k f => (congrArg c (hΦ.1 k f)).trans (hck _ _),
    fun X f => (congrArg c (hΦ.2 X f)).trans (hcX _ _)⟩

section Annihilator

/-- The vectors of `S` orthogonal under `B` to the image of every place-equivariant map from
the standard module of `ds` into `S'`. -/
def annihilator (S S' : OperatorRealization F n) (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ)
    (w : CP) (ds : List ComplexCharacterData) : Submodule ℂ S.Space where
  carrier := {y | ∀ Φ : complexStandardKFinite n ds →ₗ[ℂ] S'.Space,
    IsPlaceEquivariant S' w ds Φ → ∀ f, B y (Φ f) = 0}
  zero_mem' := by
    intro Φ _ f
    exact LinearMap.map_zero₂ B (Φ f)
  add_mem' := by
    intro y₁ y₂ h₁ h₂ Φ hΦ f
    change B (y₁ + y₂) (Φ f) = 0
    rw [LinearMap.map_add₂, h₁ Φ hΦ f, h₂ Φ hΦ f, add_zero]
  smul_mem' := by
    intro c y h Φ hΦ f
    change B (c • y) (Φ f) = 0
    rw [LinearMap.map_smul₂, h Φ hΦ f, smul_zero]

theorem mem_annihilator {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {w : CP} {ds : List ComplexCharacterData}
    (y : S.Space) :
    y ∈ annihilator S S' B w ds ↔ ∀ Φ : complexStandardKFinite n ds →ₗ[ℂ] S'.Space,
      IsPlaceEquivariant S' w ds Φ → ∀ f, B y (Φ f) = 0 := Iff.rfl

/-- An operator `c` of `S` with a `B`-adjoint `c'` commuting with the actions at `w` preserves
the annihilator. -/
theorem annihilator_map {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {w : CP} {ds : List ComplexCharacterData}
    (c : S.Space → S.Space) (c' : S'.Space →ₗ[ℂ] S'.Space)
    (hadj : ∀ y x, B (c y) x = B y (c' x))
    (hck : ∀ (l : CK) (x : S'.Space),
      c' (S'.complexPlaceCompactRepresentation w l x) =
        S'.complexPlaceCompactRepresentation w l (c' x))
    (hcX : ∀ (X : CM) (x : S'.Space),
      c' (S'.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x) =
        S'.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) (c' x))
    {y : S.Space} (hy : y ∈ annihilator S S' B w ds) : c y ∈ annihilator S S' B w ds :=
  (mem_annihilator (c y)).2 fun Φ hΦ f =>
    (hadj y (Φ f)).trans ((mem_annihilator y).1 hy (c' ∘ₗ Φ) (hΦ.comp c' hck hcX) f)

/-- The compact action of an element of the compact factors that is trivial at `w` commutes
with the actions at `w`. -/
theorem compact_comm_of_trivial (T : OperatorRealization F n) (w : CP)
    (q : ArchimedeanCompactFactors F n) (hq : q.2 w = 1) :
    (∀ (l : CK) (x : T.Space),
      T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
          (T.complexPlaceCompactRepresentation w l x) =
        T.complexPlaceCompactRepresentation w l
          (T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) x)) ∧
    ∀ (X : CM) (x : T.Space),
      T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
          (T.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x) =
        T.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X)
          (T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) x) := by
  classical
  refine ⟨fun l x => ?_, fun X x => ?_⟩
  · have hcomm : q * ArchimedeanCompactFactors.complexPlaceFactor F n w l =
        ArchimedeanCompactFactors.complexPlaceFactor F n w l * q := by
      refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
      · change q.1 v * 1 = 1 * q.1 v
        rw [mul_one, one_mul]
      · change q.2 v * (Pi.mulSingle w l : CP → CK) v = (Pi.mulSingle w l : CP → CK) v * q.2 v
        by_cases hv : v = w
        · subst hv
          rw [hq, one_mul, mul_one]
        · rw [Pi.mulSingle_eq_of_ne hv, mul_one, one_mul]
    have hk : ArchimedeanCompactFactors.toStandardCompact F n q *
        complexPlaceCompactInclusion F n w l =
        complexPlaceCompactInclusion F n w l *
          ArchimedeanCompactFactors.toStandardCompact F n q := by
      change ArchimedeanCompactFactors.toStandardCompact F n q *
          ArchimedeanCompactFactors.toStandardCompact F n
            (ArchimedeanCompactFactors.complexPlaceFactor F n w l) =
        ArchimedeanCompactFactors.toStandardCompact F n
            (ArchimedeanCompactFactors.complexPlaceFactor F n w l) *
          ArchimedeanCompactFactors.toStandardCompact F n q
      rw [← map_mul, ← map_mul, hcomm]
    have h1 := (T.compactRepresentation.map_mul _ _).symm.trans
      ((congrArg T.compactRepresentation hk).trans (T.compactRepresentation.map_mul _ _))
    exact LinearMap.congr_fun h1 x
  · have hX : unitaryMatrixComplexLieConjugation ℂ n (q.2 w) ((1 : ℂ) ⊗ₜ[ℝ] X) =
        (1 : ℂ) ⊗ₜ[ℝ] X := by
      rw [hq, unitaryMatrixComplexLieConjugation_one' ℂ _]
    exact (T.compactRepresentation_complexPlaceLieAction q w _ x).trans
      (congrArg (fun Z => T.complexPlaceLieAction w Z
        (T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) x)) hX)

theorem annihilator_finite {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (g : FiniteAdelicGL F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B w ds) :
    S.finiteRepresentation g y ∈ annihilator S S' B w ds := by
  refine annihilator_map (S.finiteRepresentation g) (S'.finiteRepresentation g⁻¹)
    (fun y' x => ?_)
    (fun l x => S'.finiteRepresentation_complexPlaceCompactRepresentation g⁻¹ w l x)
    (fun X x => S'.finiteRepresentation_complexPlaceLieAction g⁻¹ w _ x) hy
  have h := hB.1 g y' (S'.finiteRepresentation g⁻¹ x)
  have hx : S'.finiteRepresentation g (S'.finiteRepresentation g⁻¹ x) = x :=
    Representation.self_inv_apply _ g x
  exact (congrArg (fun z => B (S.finiteRepresentation g y') z) hx).symm.trans h

/-- Compact elements trivial at `w` preserve the annihilator. -/
theorem annihilator_compact_trivial {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (q q' : ArchimedeanCompactFactors F n)
    (hqq' : q * q' = 1) (hq' : q'.2 w = 1)
    {y : S.Space} (hy : y ∈ annihilator S S' B w ds) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y ∈
      annihilator S S' B w ds := by
  have hcomm := compact_comm_of_trivial S' w q' hq'
  refine annihilator_map _
    (S'.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q'))
    (fun y' x => ?_) hcomm.1 hcomm.2 hy
  have h := hB.2.1 (ArchimedeanCompactFactors.toStandardCompact F n q) y'
    (S'.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q') x)
  have hk : ArchimedeanCompactFactors.toStandardCompact F n q *
      ArchimedeanCompactFactors.toStandardCompact F n q' = 1 := by
    rw [← map_mul, hqq', map_one]
  have hx : S'.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
      (S'.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q') x) = x := by
    have h1 := (S'.compactRepresentation.map_mul
      (ArchimedeanCompactFactors.toStandardCompact F n q)
      (ArchimedeanCompactFactors.toStandardCompact F n q')).symm.trans
      ((congrArg S'.compactRepresentation hk).trans S'.compactRepresentation.map_one)
    exact LinearMap.congr_fun h1 x
  exact (congrArg (fun z => B (S.compactRepresentation
    (ArchimedeanCompactFactors.toStandardCompact F n q) y') z) hx).symm.trans h

/-- Compact elements at `w` preserve the annihilator. -/
theorem annihilator_placeCompact {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (l : CK) {y : S.Space}
    (hy : y ∈ annihilator S S' B w ds) :
    S.complexPlaceCompactRepresentation w l y ∈ annihilator S S' B w ds := by
  refine (mem_annihilator _).2 fun Φ hΦ f => ?_
  have h := hB.2.1 (complexPlaceCompactInclusion F n w l) y
    (S'.complexPlaceCompactRepresentation w l⁻¹ (Φ f))
  have hx : S'.complexPlaceCompactRepresentation w l
      (S'.complexPlaceCompactRepresentation w l⁻¹ (Φ f)) = Φ f :=
    Representation.self_inv_apply _ l (Φ f)
  have hT : Φ (complexStandardTranslate n ds (ofUnitary l⁻¹) f) =
      S'.complexPlaceCompactRepresentation w l⁻¹ (Φ f) := hΦ.1 (ofUnitary l⁻¹) f
  have h0 : B y (S'.complexPlaceCompactRepresentation w l⁻¹ (Φ f)) = 0 :=
    (congrArg (fun z => B y z) hT).symm.trans
      ((mem_annihilator y).1 hy Φ hΦ (complexStandardTranslate n ds (ofUnitary l⁻¹) f))
  have h2 : B (S.complexPlaceCompactRepresentation w l y)
      (S'.complexPlaceCompactRepresentation w l
        (S'.complexPlaceCompactRepresentation w l⁻¹ (Φ f))) =
      B y (S'.complexPlaceCompactRepresentation w l⁻¹ (Φ f)) := h
  exact (congrArg (fun z => B (S.complexPlaceCompactRepresentation w l y) z) hx).symm.trans
    (h2.trans h0)

/-- The compact action preserves the annihilator. -/
theorem annihilator_compact {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (k : standardInfiniteCompact F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B w ds) :
    S.compactRepresentation k y ∈ annihilator S S' B w ds := by
  classical
  refine (ArchimedeanCompactFactors.toStandardCompact_surjective F n k).elim fun p hpk => ?_
  have hex : ∃ p' : ArchimedeanCompactFactors F n,
      p'.1 = p.1 ∧ p'.2 = Function.update p.2 w 1 := ⟨(p.1, Function.update p.2 w 1), rfl, rfl⟩
  refine hex.elim fun p' hp' => ?_
  have hp'1 := hp'.1
  have hp'2 := hp'.2
  have hp : p = ArchimedeanCompactFactors.complexPlaceFactor F n w (p.2 w) * p' := by
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · change p.1 v = 1 * p'.1 v
      rw [hp'1, one_mul]
    · change p.2 v = (Pi.mulSingle w (p.2 w) : CP → CK) v * p'.2 v
      rw [hp'2]
      by_cases hv : v = w
      · subst hv
        rw [Pi.mulSingle_eq_same, Function.update_self, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hv, Function.update_of_ne hv, one_mul]
  have hp'w : p'.2 w = 1 := by rw [hp'2, Function.update_self]
  have hp'' : p' * p'⁻¹ = 1 := mul_inv_cancel p'
  have hp''w : p'⁻¹.2 w = 1 := by
    rw [Prod.snd_inv, Pi.inv_apply, hp'w, inv_one]
  have hCx : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y ∈
      annihilator S S' B w ds := annihilator_compact_trivial hB p' p'⁻¹ hp'' hp''w hy
  have h2 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n w (p.2 w) * p')) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n w (p.2 w))) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
    (congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)
  have hsplit : S.compactRepresentation k y =
      S.complexPlaceCompactRepresentation w (p.2 w)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) :=
    ((congrArg (fun r => S.compactRepresentation r y) hpk.symm).trans
      (congrArg (fun r => S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n r) y) hp)).trans
      (LinearMap.congr_fun h2 y)
  exact (congrArg (fun x => x ∈ annihilator S S' B w ds) hsplit).mpr
    (annihilator_placeCompact hB (p.2 w) hCx)

/-- The real Lie action preserves the annihilator. -/
theorem annihilator_lieAction {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (X : RealLieAlgebra F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B w ds) :
    S.lieAction X y ∈ annihilator S S' B w ds := by
  classical
  refine (mem_annihilator _).2 fun Φ hΦ f => ?_
  have h := hB.2.2 X y (Φ f)
  have hreal : ∀ v : RP, B y (S'.realPlaceLieAction v
      ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) (Φ f)) = 0 := by
    intro v
    exact (mem_annihilator y).1 hy
      ((S'.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X)) ∘ₗ Φ)
      (hΦ.comp _
        (fun l x => (S'.complexPlaceCompactRepresentation_realPlaceLieAction w v l _ x).symm)
        (fun Y x => S'.realPlaceLieAction_comm_complexPlace v w _ _ x)) f
  have hcomplex : ∀ v : CP, B y (S'.complexPlaceLieAction v
      ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X) (Φ f)) = 0 := by
    intro v
    by_cases hv : v = w
    · rw [hv]
      exact (congrArg (fun z => B y z) (hΦ.2 (complexPlaceLieProjection F n w X) f)).symm.trans
        ((mem_annihilator y).1 hy Φ hΦ _)
    · exact (mem_annihilator y).1 hy ((S'.complexPlaceLieAction v
          ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X)) ∘ₗ Φ)
        (hΦ.comp _
          (fun l x =>
            (S'.complexPlaceCompactRepresentation_complexPlaceLieAction_of_ne w v hv l _ x).symm)
          (fun Y x => S'.complexPlaceLieAction_comm_of_ne (Ne.symm hv) _ _ x)) f
  have hsplit : S'.lieAction X (Φ f) =
      (∑ v : RP, S'.realPlaceLieAction v
        ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) (Φ f)) +
      (∑ v : CP, S'.complexPlaceLieAction v
        ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X) (Φ f)) :=
    S'.complexify_action_eq_sum_place X (Φ f)
  have hmem : S'.lieAction X (Φ f) ∈ LinearMap.ker (B y) := by
    refine (congrArg (fun z => z ∈ LinearMap.ker (B y)) hsplit).mpr ?_
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun v _ => ?_)
      (Submodule.sum_mem _ fun v _ => ?_)
    · exact LinearMap.mem_ker.2 (hreal v)
    · exact LinearMap.mem_ker.2 (hcomplex v)
  have hsum : B y (S'.lieAction X (Φ f)) = 0 := LinearMap.mem_ker.1 hmem
  exact (eq_neg_of_add_eq_zero_left h).trans ((congrArg Neg.neg hsum).trans neg_zero)

theorem annihilator_complexLieAction {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (Y : ComplexLieAlgebra F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B w ds) :
    S.complexLieAction Y y ∈ annihilator S S' B w ds := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.complexLieAction (z ⊗ₜ[ℝ] X) y =
        z • S.complexLieAction (complexify F n X) y :=
      (congrArg (fun Y => S.complexLieAction Y y) hzX).trans
        (LinearMap.congr_fun (S.complexLieAction.map_smul z (complexify F n X)) y)
    have hmem : S.complexLieAction (complexify F n X) y ∈ annihilator S S' B w ds :=
      annihilator_lieAction hB X hy
    exact (congrArg (fun x => x ∈ annihilator S S' B w ds) heq).mpr
      (Submodule.smul_mem _ z hmem)
  | add Y₁ Y₂ h₁ h₂ =>
    have heq : S.complexLieAction (Y₁ + Y₂) y =
        S.complexLieAction Y₁ y + S.complexLieAction Y₂ y :=
      LinearMap.congr_fun (S.complexLieAction.map_add Y₁ Y₂) y
    exact (congrArg (fun x => x ∈ annihilator S S' B w ds) heq).mpr
      (Submodule.add_mem _ h₁ h₂)

theorem annihilator_enveloping {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (u : EnvelopingAlgebra F n) :
    ∀ y ∈ annihilator S S' B w ds, S.envelopingAction u y ∈ annihilator S S' B w ds := by
  have hu : u ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra F n → EnvelopingAlgebra F n)) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨Y, rfl⟩ := hu
    intro y hy
    exact annihilator_complexLieAction hB Y hy
  | algebraMap c =>
    intro y hy
    have heq : S.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n) c) y = c • y :=
      LinearMap.congr_fun (S.envelopingAction.commutes c) y
    exact (congrArg (fun x => x ∈ annihilator S S' B w ds) heq).mpr
      (Submodule.smul_mem _ c hy)
  | add a b _ _ ha hb =>
    intro y hy
    have heq : S.envelopingAction (a + b) y = S.envelopingAction a y + S.envelopingAction b y :=
      LinearMap.congr_fun (S.envelopingAction.map_add a b) y
    exact (congrArg (fun x => x ∈ annihilator S S' B w ds) heq).mpr
      (Submodule.add_mem _ (ha y hy) (hb y hy))
  | mul a b _ _ ha hb =>
    intro y hy
    have heq : S.envelopingAction (a * b) y = S.envelopingAction a (S.envelopingAction b y) :=
      LinearMap.congr_fun (S.envelopingAction.map_mul a b) y
    exact (congrArg (fun x => x ∈ annihilator S S' B w ds) heq).mpr
      (ha _ (hb y hy))

/-- The annihilator is preserved by the whole concrete operator algebra. -/
theorem annihilator_operator {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {ds : List ComplexCharacterData} (a : automorphicOperatorAlgebra F n) :
    ∀ y ∈ annihilator S S' B w ds, S.representation a y ∈ annihilator S S' B w ds := by
  obtain ⟨e, he⟩ := a
  induction he using Algebra.adjoin_induction with
  | mem e he =>
    rcases he with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · exact fun y hy => annihilator_finite hB g hy
    · exact fun y hy => annihilator_compact hB k hy
    · exact fun y hy => annihilator_enveloping hB u y hy
  | algebraMap c =>
    intro y hy
    have h : S.representation ⟨algebraMap ℂ (FiniteSmoothEnd F n) c,
        Subalgebra.algebraMap_mem _ c⟩ y = c • y := rfl
    rw [h]
    exact Submodule.smul_mem _ c hy
  | add e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro y hy
    have h : S.representation ⟨e₁ + e₂, Subalgebra.add_mem _ he₁ he₂⟩ y =
        S.representation ⟨e₁, he₁⟩ y + S.representation ⟨e₂, he₂⟩ y := rfl
    rw [h]
    exact Submodule.add_mem _ (h₁ y hy) (h₂ y hy)
  | mul e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro y hy
    have h : S.representation ⟨e₁ * e₂, Subalgebra.mul_mem _ he₁ he₂⟩ y =
        S.representation ⟨e₁, he₁⟩ (S.representation ⟨e₂, he₂⟩ y) := rfl
    rw [h]
    exact h₁ _ (h₂ y hy)

/-- The annihilator as a subrepresentation. -/
def annihilatorSubrepresentation (S S' : OperatorRealization F n)
    (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ) (hB : S.IsInvariantPairing S' B) (w : CP)
    (ds : List ComplexCharacterData) : Subrepresentation S.representation where
  toSubmodule := annihilator S S' B w ds
  apply_mem_toSubmodule a y hy := annihilator_operator hB a y hy

end Annihilator

/-- The pairing of the standard modules induced by `B`, a map `A` into `S` and a map `Φ` into
`S'`: `(f, f') ↦ B (A f) (Φ f')`. -/
def inducedPairing {S S' : OperatorRealization F n} (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ)
    {d dd : List ComplexCharacterData} (A : complexStandardKFinite n d →ₗ[ℂ] S.Space)
    (Φ : complexStandardKFinite n dd →ₗ[ℂ] S'.Space) :
    complexStandardKFinite n d →ₗ[ℂ] complexStandardKFinite n dd →ₗ[ℂ] ℂ :=
  (B ∘ₗ A).compl₂ Φ

theorem inducedPairing_apply {S S' : OperatorRealization F n}
    (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ) {d dd : List ComplexCharacterData}
    (A : complexStandardKFinite n d →ₗ[ℂ] S.Space)
    (Φ : complexStandardKFinite n dd →ₗ[ℂ] S'.Space) (f : complexStandardKFinite n d)
    (f' : complexStandardKFinite n dd) :
    inducedPairing B A Φ f f' = B (A f) (Φ f') := rfl

/-- The Lie action at `w` of `1 ⊗ X` is the Lie action of the real direction `X` at `w`. -/
theorem complexPlaceLieAction_one_tmul (S : OperatorRealization F n) (w : CP) (X : CM)
    (y : S.Space) :
    S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) y =
      S.lieAction (complexPlaceLieInclusion F n w X) y := by
  have h1 : S.lieAction (complexPlaceLieInclusion F n w X) y =
      S.complexLieAction (complexify F n (complexPlaceLieInclusion F n w X)) y := rfl
  have h2 : S.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) y =
      S.complexLieAction (complexPlaceComplexLieInclusion F n w ((1 : ℂ) ⊗ₜ[ℝ] X)) y := rfl
  exact h2.trans ((congrArg (fun Z => S.complexLieAction Z y)
    ((complexPlaceComplexLieInclusion_tmul F n w 1 X).trans
      (complexify_apply F n (complexPlaceLieInclusion F n w X)).symm)).trans h1.symm)

/-- An invariant pairing of operator realizations induces, through place-equivariant maps at
`w`, an invariant pairing of the standard modules. -/
theorem isComplexStandardInvariantPairing_induced {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {d dd : List ComplexCharacterData} {A : complexStandardKFinite n d →ₗ[ℂ] S.Space}
    {Φ : complexStandardKFinite n dd →ₗ[ℂ] S'.Space} (hA : IsPlaceEquivariant S w d A)
    (hΦ : IsPlaceEquivariant S' w dd Φ) :
    IsComplexStandardInvariantPairing n d dd (inducedPairing B A Φ) := by
  refine ⟨fun k f f' => ?_, fun X f f' => ?_⟩
  · have h1 : inducedPairing B A Φ (complexStandardTranslate n d k f)
        (complexStandardTranslate n dd k f') =
        B (S.complexPlaceCompactRepresentation w
            ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f))
          (S'.complexPlaceCompactRepresentation w
            ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (Φ f')) :=
      congrArg₂ (fun a b => B a b) (hA.1 k f) (hΦ.1 k f')
    exact h1.trans (hB.2.1 (complexPlaceCompactInclusion F n w
      ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩) (A f) (Φ f'))
  · have h1 : inducedPairing B A Φ (complexStandardDerivative n d X f) f' +
        inducedPairing B A Φ f (complexStandardDerivative n dd X f') =
        B (S.lieAction (complexPlaceLieInclusion F n w X) (A f)) (Φ f') +
          B (A f) (S'.lieAction (complexPlaceLieInclusion F n w X) (Φ f')) :=
      congrArg₂ (fun a b => a + b)
        (congrArg (fun a => B a (Φ f'))
          ((hA.2 X f).trans (complexPlaceLieAction_one_tmul S w X (A f))))
        (congrArg (fun b => B (A f) b)
          ((hΦ.2 X f').trans (complexPlaceLieAction_one_tmul S' w X (Φ f'))))
    exact h1.trans (hB.2.2 (complexPlaceLieInclusion F n w X) (A f) (Φ f'))

/-- If the annihilator is the whole representation, every vector lies in it. -/
theorem mem_annihilator_of_eq_top {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {hB : S.IsInvariantPairing S' B} {w : CP}
    {ds : List ComplexCharacterData} (htop : annihilatorSubrepresentation S S' B hB w ds = ⊤)
    (y : S.Space) : y ∈ annihilator S S' B w ds := by
  have h : annihilator S S' B w ds = ⊤ := congrArg Subrepresentation.toSubmodule htop
  exact (congrArg (fun p : Submodule ℂ S.Space => y ∈ p) h).mpr Submodule.mem_top

/-- If the annihilator is zero, its only vector is zero. -/
theorem eq_zero_of_mem_annihilator {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {hB : S.IsInvariantPairing S' B} {w : CP}
    {ds : List ComplexCharacterData} (hbot : annihilatorSubrepresentation S S' B hB w ds = ⊥)
    {y : S.Space} (hy : y ∈ annihilator S S' B w ds) : y = 0 := by
  have h : annihilator S S' B w ds = ⊥ := congrArg Subrepresentation.toSubmodule hbot
  exact (Submodule.mem_bot ℂ).1 ((congrArg (fun p : Submodule ℂ S.Space => y ∈ p) h).mp hy)

/-- If `B.flip` is injective and some injective place-equivariant map from a nontrivial
standard module into `S'` exists, the annihilator is not the whole representation. -/
theorem annihilatorSubrepresentation_ne_top {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B)
    (hBinj : Function.Injective B.flip) {w : CP} {ds : List ComplexCharacterData}
    [Nontrivial (complexStandardKFinite n ds)]
    {Ad : complexStandardKFinite n ds →ₗ[ℂ] S'.Space} (hAd : IsPlaceEquivariant S' w ds Ad)
    (hAdinj : Function.Injective Ad) :
    annihilatorSubrepresentation S S' B hB w ds ≠ ⊤ := by
  intro htop
  have hne := exists_ne (0 : complexStandardKFinite n ds)
  obtain ⟨f', hf'0⟩ := hne
  have hflip : B.flip (Ad f') = 0 := by
    refine LinearMap.ext fun y => ?_
    have h : B y (Ad f') = 0 :=
      (mem_annihilator y).1 (mem_annihilator_of_eq_top htop y) Ad hAd f'
    exact ((LinearMap.flip_apply B y (Ad f')).trans h).trans (LinearMap.zero_apply y).symm
  have hAd0 : Ad f' = 0 := hBinj (hflip.trans (map_zero B.flip).symm)
  exact hf'0 (hAdinj (hAd0.trans (map_zero Ad).symm))

/-- If the annihilator is zero, then for an injective place-equivariant `A` from a nontrivial
standard module, some induced pairing `inducedPairing B A Φ` is nonzero; it is invariant. -/
theorem exists_inducedPairing_ne_zero {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {w : CP}
    {d dd : List ComplexCharacterData} [Nontrivial (complexStandardKFinite n d)]
    {A : complexStandardKFinite n d →ₗ[ℂ] S.Space} (hA : IsPlaceEquivariant S w d A)
    (hAinj : Function.Injective A)
    (hbot : annihilatorSubrepresentation S S' B hB w dd = ⊥) :
    ∃ P : complexStandardKFinite n d →ₗ[ℂ] complexStandardKFinite n dd →ₗ[ℂ] ℂ,
      IsComplexStandardInvariantPairing n d dd P ∧ P ≠ 0 := by
  have hne := exists_ne (0 : complexStandardKFinite n d)
  obtain ⟨f, hf0⟩ := hne
  have hAf0 : A f ≠ 0 := fun h => hf0 (hAinj (h.trans (map_zero A).symm))
  have hex : ∃ Φ : complexStandardKFinite n dd →ₗ[ℂ] S'.Space,
      IsPlaceEquivariant S' w dd Φ ∧
        ∃ f' : complexStandardKFinite n dd, B (A f) (Φ f') ≠ 0 := by
    by_contra hcon
    refine hAf0 (eq_zero_of_mem_annihilator hbot
      ((mem_annihilator (A f)).2 fun Φ hΦ f' => ?_))
    by_contra hne'
    exact hcon ⟨Φ, hΦ, f', hne'⟩
  obtain ⟨Φ, hΦ, f', hf'⟩ := hex
  refine ⟨inducedPairing B A Φ, isComplexStandardInvariantPairing_induced hB hA hΦ,
    fun hP => ?_⟩
  have h := LinearMap.congr_fun (LinearMap.congr_fun hP f) f'
  have h0 : ((0 : complexStandardKFinite n d →ₗ[ℂ]
      complexStandardKFinite n dd →ₗ[ℂ] ℂ) f) f' = 0 := rfl
  exact hf' ((inducedPairing_apply B A Φ f f').symm.trans (h.trans h0))

variable [CompactSpace (AdeleQuotient F)]

/-- **The contragredient pairing restricts to the parameters.** If `Td` is contragredient to
the actual cuspidal realization `T`, and `d`, `dd` are parameters of `T`, `Td` at the complex
place `w`, then the `U(r+1)`-finite complex standard modules of `d` and `dd` carry a nonzero
invariant pairing. -/
theorem exists_complexStandardInvariantPairing {r : ℕ}
    (T Td : CuspidalOperatorRealization F r)
    (hTd : Td.realization.IsContragredientOf T.realization) (w : CP)
    (d dd : List ComplexCharacterData) (hd : T.realization.HasComplexPlaceParameter w d)
    (hdd : Td.realization.HasComplexPlaceParameter w dd) :
    ∃ P : complexStandardKFinite (r + 1) d →ₗ[ℂ] complexStandardKFinite (r + 1) dd →ₗ[ℂ] ℂ,
      IsComplexStandardInvariantPairing (r + 1) d dd P ∧ P ≠ 0 := by
  obtain ⟨B, hBi, -, hBinj, -⟩ := hTd
  obtain ⟨hlen, A, hAinj, hAK, hAX⟩ := hd
  obtain ⟨hlend, Ad, hAdinj, hAdK, hAdX⟩ := hdd
  have hA := isPlaceEquivariant_of_parameter T.realization w d A hAK hAX
  have hAd := isPlaceEquivariant_of_parameter Td.realization w dd Ad hAdK hAdX
  have hntr : Nontrivial (complexStandardKFinite (r + 1) d) :=
    complexStandardNontrivial (r + 1) d hlen
  have hntrd : Nontrivial (complexStandardKFinite (r + 1) dd) :=
    complexStandardNontrivial (r + 1) dd hlend
  rcases T.irreducible.eq_bot_or_eq_top
      (annihilatorSubrepresentation T.realization Td.realization B hBi w dd) with hbot | htop
  · exact exists_inducedPairing_ne_zero hBi hA hAinj hbot
  · exact absurd htop (annihilatorSubrepresentation_ne_top hBi hBinj hAd hAdinj)

end ComplexPlaceContragredient

open ComplexPlaceContragredient in
theorem complexPlaceContragredientParameterReduction :
    ComplexPlaceContragredientParameterReductionStatement.{u} := by
  intro hG hL F _ _ _ r T Td hTd w d dd hd hdd
  obtain ⟨P, hP, hP0⟩ := exists_complexStandardInvariantPairing T Td hTd w d dd hd hdd
  exact hL (r + 1) d dd hd.1 hdd.1 (hG F r T w d hd) (hG F r Td w dd hdd) P hP hP0

end Langlands.Global.RankinSelbergGlobal
