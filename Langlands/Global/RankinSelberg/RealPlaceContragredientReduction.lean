import Langlands.Global.RankinSelberg.RealPlaceContragredientPremises
import Langlands.Automorphic.PlaceComponentRealization
import Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-! # Reduction of the real-place contragredient pair-factor statement

This module proves `RealPlaceContragredientPairLReductionStatement`: the statement
`RealPlaceContragredientPairLStatement` follows from the real half of the published
irreducibility statement `Automorphic.CuspidalArchimedeanStandardIrreducibleStatement` and the
local pairing premise `RealStandardPairingPairLStatement` (stated, not proved, in
`RealPlaceContragredientPremises`).

The proved content is `exists_realStandardInvariantPairing`: the contragredient pairing of `T`
and `Td` restricts, through the embeddings of the parameters at a real place, to a nonzero
invariant pairing of the two real standard modules. See the paired Markdown.
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

namespace RealPlaceContragredient

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ

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

/-- `Φ` is equivariant for the actions at the real place `v`: it carries right translation by
`k ∈ O(n)` and the right derivative along `X ∈ 𝔤𝔩_n(ℝ)` to the compact and Lie actions at
`v`. -/
def IsPlaceEquivariant (S : OperatorRealization F n) (v : RP) (ds : List RealBlock)
    (Φ : realStandardKFinite n ds →ₗ[ℂ] S.Space) : Prop :=
  (∀ (l : RK) (f : realStandardKFinite n ds),
      Φ (realStandardRep n ds l f) = S.realPlaceCompactRepresentation v l (Φ f)) ∧
    ∀ (X : RM) (f : realStandardKFinite n ds),
      Φ (realStandardLie n ds ((1 : ℂ) ⊗ₜ[ℝ] X) f) =
        S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) (Φ f)

set_option backward.isDefEq.respectTransparency false in
/-- The map of a real-place parameter is injective and place-equivariant. -/
theorem exists_isPlaceEquivariant_of_parameter (S : OperatorRealization F n) (v : RP)
    {ds : List RealBlock} (hds : S.HasRealPlaceParameter v ds) :
    ∃ A : realStandardKFinite n ds →ₗ[ℂ] S.Space,
      Function.Injective A ∧ IsPlaceEquivariant S v ds A := by
  obtain ⟨-, A, hAinj, hK, hX⟩ := hds
  exact ⟨A, hAinj, fun l f => OperatorRealization.realPlaceParameter_compact hK l f,
    fun X f => OperatorRealization.realPlaceParameter_lie hX X f⟩

/-- Composing a place-equivariant map with an operator commuting with the actions at `v`
gives a place-equivariant map. -/
theorem IsPlaceEquivariant.comp {S : OperatorRealization F n} {v : RP}
    {ds : List RealBlock} {Φ : realStandardKFinite n ds →ₗ[ℂ] S.Space}
    (hΦ : IsPlaceEquivariant S v ds Φ) (c : S.Space →ₗ[ℂ] S.Space)
    (hck : ∀ (l : RK) (x : S.Space),
      c (S.realPlaceCompactRepresentation v l x) = S.realPlaceCompactRepresentation v l (c x))
    (hcX : ∀ (X : RM) (x : S.Space),
      c (S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) x) =
        S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) (c x)) :
    IsPlaceEquivariant S v ds (c ∘ₗ Φ) := by
  exact ⟨fun l f => (congrArg c (hΦ.1 l f)).trans (hck _ _),
    fun X f => (congrArg c (hΦ.2 X f)).trans (hcX _ _)⟩

section Annihilator

/-- The vectors of `S` orthogonal under `B` to the image of every place-equivariant map from
the real standard module of `ds` into `S'`. -/
def annihilator (S S' : OperatorRealization F n) (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ)
    (v : RP) (ds : List RealBlock) : Submodule ℂ S.Space where
  carrier := {y | ∀ Φ : realStandardKFinite n ds →ₗ[ℂ] S'.Space,
    IsPlaceEquivariant S' v ds Φ → ∀ f, B y (Φ f) = 0}
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
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {v : RP} {ds : List RealBlock}
    (y : S.Space) :
    y ∈ annihilator S S' B v ds ↔ ∀ Φ : realStandardKFinite n ds →ₗ[ℂ] S'.Space,
      IsPlaceEquivariant S' v ds Φ → ∀ f, B y (Φ f) = 0 := Iff.rfl

/-- An operator `c` of `S` with a `B`-adjoint `c'` commuting with the actions at `v` preserves
the annihilator. -/
theorem annihilator_map {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {v : RP} {ds : List RealBlock}
    (c : S.Space → S.Space) (c' : S'.Space →ₗ[ℂ] S'.Space)
    (hadj : ∀ y x, B (c y) x = B y (c' x))
    (hck : ∀ (l : RK) (x : S'.Space),
      c' (S'.realPlaceCompactRepresentation v l x) =
        S'.realPlaceCompactRepresentation v l (c' x))
    (hcX : ∀ (X : RM) (x : S'.Space),
      c' (S'.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) x) =
        S'.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) (c' x))
    {y : S.Space} (hy : y ∈ annihilator S S' B v ds) : c y ∈ annihilator S S' B v ds :=
  (mem_annihilator (c y)).2 fun Φ hΦ f =>
    (hadj y (Φ f)).trans ((mem_annihilator y).1 hy (c' ∘ₗ Φ) (hΦ.comp c' hck hcX) f)

/-- The compact action of an element of the compact factors that is trivial at `v` commutes
with the actions at `v`. -/
theorem compact_comm_of_trivial (T : OperatorRealization F n) (v : RP)
    (q : ArchimedeanCompactFactors F n) (hq : q.1 v = 1) :
    (∀ (l : RK) (x : T.Space),
      T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
          (T.realPlaceCompactRepresentation v l x) =
        T.realPlaceCompactRepresentation v l
          (T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) x)) ∧
    ∀ (X : RM) (x : T.Space),
      T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
          (T.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) x) =
        T.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X)
          (T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) x) := by
  classical
  refine ⟨fun l x => ?_, fun X x => ?_⟩
  · have hcomm : q * ArchimedeanCompactFactors.realPlaceFactor F n v l =
        ArchimedeanCompactFactors.realPlaceFactor F n v l * q := by
      refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
      · change q.1 w * (Pi.mulSingle v l : RP → RK) w = (Pi.mulSingle v l : RP → RK) w * q.1 w
        by_cases hw : w = v
        · subst hw
          rw [hq, one_mul, mul_one]
        · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
      · change q.2 w * 1 = 1 * q.2 w
        rw [mul_one, one_mul]
    have hk : ArchimedeanCompactFactors.toStandardCompact F n q *
        realPlaceCompactInclusion F n v l =
        realPlaceCompactInclusion F n v l *
          ArchimedeanCompactFactors.toStandardCompact F n q := by
      change ArchimedeanCompactFactors.toStandardCompact F n q *
          ArchimedeanCompactFactors.toStandardCompact F n
            (ArchimedeanCompactFactors.realPlaceFactor F n v l) =
        ArchimedeanCompactFactors.toStandardCompact F n
            (ArchimedeanCompactFactors.realPlaceFactor F n v l) *
          ArchimedeanCompactFactors.toStandardCompact F n q
      rw [← map_mul, ← map_mul, hcomm]
    have h1 := (T.compactRepresentation.map_mul _ _).symm.trans
      ((congrArg T.compactRepresentation hk).trans (T.compactRepresentation.map_mul _ _))
    exact LinearMap.congr_fun h1 x
  · have hX : unitaryMatrixComplexLieConjugation ℝ n (q.1 v) ((1 : ℂ) ⊗ₜ[ℝ] X) =
        (1 : ℂ) ⊗ₜ[ℝ] X := by
      rw [hq, unitaryMatrixComplexLieConjugation_one' ℝ _]
    exact (T.compactRepresentation_realPlaceLieAction q v _ x).trans
      (congrArg (fun Z => T.realPlaceLieAction v Z
        (T.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) x)) hX)

theorem annihilator_finite {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (g : FiniteAdelicGL F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B v ds) :
    S.finiteRepresentation g y ∈ annihilator S S' B v ds := by
  refine annihilator_map (S.finiteRepresentation g) (S'.finiteRepresentation g⁻¹)
    (fun y' x => ?_)
    (fun l x => S'.finiteRepresentation_realPlaceCompactRepresentation g⁻¹ v l x)
    (fun X x => S'.finiteRepresentation_realPlaceLieAction g⁻¹ v _ x) hy
  have h := hB.1 g y' (S'.finiteRepresentation g⁻¹ x)
  have hx : S'.finiteRepresentation g (S'.finiteRepresentation g⁻¹ x) = x :=
    Representation.self_inv_apply _ g x
  exact (congrArg (fun z => B (S.finiteRepresentation g y') z) hx).symm.trans h

/-- Compact elements trivial at `v` preserve the annihilator. -/
theorem annihilator_compact_trivial {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (q q' : ArchimedeanCompactFactors F n)
    (hqq' : q * q' = 1) (hq' : q'.1 v = 1)
    {y : S.Space} (hy : y ∈ annihilator S S' B v ds) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y ∈
      annihilator S S' B v ds := by
  have hcomm := compact_comm_of_trivial S' v q' hq'
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

/-- Compact elements at `v` preserve the annihilator. -/
theorem annihilator_placeCompact {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (l : RK) {y : S.Space}
    (hy : y ∈ annihilator S S' B v ds) :
    S.realPlaceCompactRepresentation v l y ∈ annihilator S S' B v ds := by
  refine (mem_annihilator _).2 fun Φ hΦ f => ?_
  have h := hB.2.1 (realPlaceCompactInclusion F n v l) y
    (S'.realPlaceCompactRepresentation v l⁻¹ (Φ f))
  have hx : S'.realPlaceCompactRepresentation v l
      (S'.realPlaceCompactRepresentation v l⁻¹ (Φ f)) = Φ f :=
    Representation.self_inv_apply _ l (Φ f)
  have hT : Φ (realStandardRep n ds l⁻¹ f) =
      S'.realPlaceCompactRepresentation v l⁻¹ (Φ f) := hΦ.1 l⁻¹ f
  have h0 : B y (S'.realPlaceCompactRepresentation v l⁻¹ (Φ f)) = 0 :=
    (congrArg (fun z => B y z) hT).symm.trans
      ((mem_annihilator y).1 hy Φ hΦ (realStandardRep n ds l⁻¹ f))
  have h2 : B (S.realPlaceCompactRepresentation v l y)
      (S'.realPlaceCompactRepresentation v l
        (S'.realPlaceCompactRepresentation v l⁻¹ (Φ f))) =
      B y (S'.realPlaceCompactRepresentation v l⁻¹ (Φ f)) := h
  exact (congrArg (fun z => B (S.realPlaceCompactRepresentation v l y) z) hx).symm.trans
    (h2.trans h0)

/-- The compact action preserves the annihilator. -/
theorem annihilator_compact {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (k : standardInfiniteCompact F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B v ds) :
    S.compactRepresentation k y ∈ annihilator S S' B v ds := by
  classical
  refine (ArchimedeanCompactFactors.toStandardCompact_surjective F n k).elim fun p hpk => ?_
  have hex : ∃ p' : ArchimedeanCompactFactors F n,
      p'.1 = Function.update p.1 v 1 ∧ p'.2 = p.2 := ⟨(Function.update p.1 v 1, p.2), rfl, rfl⟩
  refine hex.elim fun p' hp' => ?_
  have hp'1 := hp'.1
  have hp'2 := hp'.2
  have hp : p = ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v) * p' := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · change p.1 w = (Pi.mulSingle v (p.1 v) : RP → RK) w * p'.1 w
      rw [hp'1]
      by_cases hw : w = v
      · subst hw
        rw [Pi.mulSingle_eq_same, Function.update_self, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw, one_mul]
    · change p.2 w = 1 * p'.2 w
      rw [hp'2, one_mul]
  have hp'v : p'.1 v = 1 := by rw [hp'1, Function.update_self]
  have hp'' : p' * p'⁻¹ = 1 := mul_inv_cancel p'
  have hp''v : p'⁻¹.1 v = 1 := by
    rw [Prod.fst_inv, Pi.inv_apply, hp'v, inv_one]
  have hCx : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y ∈
      annihilator S S' B v ds := annihilator_compact_trivial hB p' p'⁻¹ hp'' hp''v hy
  have h2 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v) * p')) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v))) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
    (congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)
  have hsplit : S.compactRepresentation k y =
      S.realPlaceCompactRepresentation v (p.1 v)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) :=
    ((congrArg (fun r => S.compactRepresentation r y) hpk.symm).trans
      (congrArg (fun r => S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n r) y) hp)).trans
      (LinearMap.congr_fun h2 y)
  exact (congrArg (fun x => x ∈ annihilator S S' B v ds) hsplit).mpr
    (annihilator_placeCompact hB (p.1 v) hCx)

/-- The real Lie action preserves the annihilator. -/
theorem annihilator_lieAction {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (X : RealLieAlgebra F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B v ds) :
    S.lieAction X y ∈ annihilator S S' B v ds := by
  classical
  refine (mem_annihilator _).2 fun Φ hΦ f => ?_
  have h := hB.2.2 X y (Φ f)
  have hreal : ∀ w : RP, B y (S'.realPlaceLieAction w
      ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n w X) (Φ f)) = 0 := by
    intro w
    by_cases hw : w = v
    · rw [hw]
      exact (congrArg (fun z => B y z) (hΦ.2 (realPlaceLieProjection F n v X) f)).symm.trans
        ((mem_annihilator y).1 hy Φ hΦ _)
    · exact (mem_annihilator y).1 hy ((S'.realPlaceLieAction w
          ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n w X)) ∘ₗ Φ)
        (hΦ.comp _
          (fun l x =>
            (S'.realPlaceCompactRepresentation_realPlaceLieAction_of_ne v w hw l _ x).symm)
          (fun Y x => S'.realPlaceLieAction_comm_of_ne (Ne.symm hw) _ _ x)) f
  have hcomplex : ∀ w : CP, B y (S'.complexPlaceLieAction w
      ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n w X) (Φ f)) = 0 := by
    intro w
    exact (mem_annihilator y).1 hy
      ((S'.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n w X)) ∘ₗ Φ)
      (hΦ.comp _
        (fun l x => (S'.realPlaceCompactRepresentation_complexPlaceLieAction v w l _ x).symm)
        (fun Y x => (S'.realPlaceLieAction_comm_complexPlace v w _ _ x).symm)) f
  have hsplit : S'.lieAction X (Φ f) =
      (∑ w : RP, S'.realPlaceLieAction w
        ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n w X) (Φ f)) +
      (∑ w : CP, S'.complexPlaceLieAction w
        ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n w X) (Φ f)) :=
    S'.complexify_action_eq_sum_place X (Φ f)
  have hmem : S'.lieAction X (Φ f) ∈ LinearMap.ker (B y) := by
    refine (congrArg (fun z => z ∈ LinearMap.ker (B y)) hsplit).mpr ?_
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun w _ => ?_)
      (Submodule.sum_mem _ fun w _ => ?_)
    · exact LinearMap.mem_ker.2 (hreal w)
    · exact LinearMap.mem_ker.2 (hcomplex w)
  have hsum : B y (S'.lieAction X (Φ f)) = 0 := LinearMap.mem_ker.1 hmem
  exact (eq_neg_of_add_eq_zero_left h).trans ((congrArg Neg.neg hsum).trans neg_zero)

theorem annihilator_complexLieAction {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (Y : ComplexLieAlgebra F n) {y : S.Space}
    (hy : y ∈ annihilator S S' B v ds) :
    S.complexLieAction Y y ∈ annihilator S S' B v ds := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.complexLieAction (z ⊗ₜ[ℝ] X) y =
        z • S.complexLieAction (complexify F n X) y :=
      (congrArg (fun Y => S.complexLieAction Y y) hzX).trans
        (LinearMap.congr_fun (S.complexLieAction.map_smul z (complexify F n X)) y)
    have hmem : S.complexLieAction (complexify F n X) y ∈ annihilator S S' B v ds :=
      annihilator_lieAction hB X hy
    exact (congrArg (fun x => x ∈ annihilator S S' B v ds) heq).mpr
      (Submodule.smul_mem _ z hmem)
  | add Y₁ Y₂ h₁ h₂ =>
    have heq : S.complexLieAction (Y₁ + Y₂) y =
        S.complexLieAction Y₁ y + S.complexLieAction Y₂ y :=
      LinearMap.congr_fun (S.complexLieAction.map_add Y₁ Y₂) y
    exact (congrArg (fun x => x ∈ annihilator S S' B v ds) heq).mpr
      (Submodule.add_mem _ h₁ h₂)

theorem annihilator_enveloping {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (u : EnvelopingAlgebra F n) :
    ∀ y ∈ annihilator S S' B v ds, S.envelopingAction u y ∈ annihilator S S' B v ds := by
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
    exact (congrArg (fun x => x ∈ annihilator S S' B v ds) heq).mpr
      (Submodule.smul_mem _ c hy)
  | add a b _ _ ha hb =>
    intro y hy
    have heq : S.envelopingAction (a + b) y = S.envelopingAction a y + S.envelopingAction b y :=
      LinearMap.congr_fun (S.envelopingAction.map_add a b) y
    exact (congrArg (fun x => x ∈ annihilator S S' B v ds) heq).mpr
      (Submodule.add_mem _ (ha y hy) (hb y hy))
  | mul a b _ _ ha hb =>
    intro y hy
    have heq : S.envelopingAction (a * b) y = S.envelopingAction a (S.envelopingAction b y) :=
      LinearMap.congr_fun (S.envelopingAction.map_mul a b) y
    exact (congrArg (fun x => x ∈ annihilator S S' B v ds) heq).mpr
      (ha _ (hb y hy))

/-- The annihilator is preserved by the whole concrete operator algebra. -/
theorem annihilator_operator {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {ds : List RealBlock} (a : automorphicOperatorAlgebra F n) :
    ∀ y ∈ annihilator S S' B v ds, S.representation a y ∈ annihilator S S' B v ds := by
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
    (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ) (hB : S.IsInvariantPairing S' B) (v : RP)
    (ds : List RealBlock) : Subrepresentation S.representation where
  toSubmodule := annihilator S S' B v ds
  apply_mem_toSubmodule a y hy := annihilator_operator hB a y hy

end Annihilator

/-- The pairing of the real standard modules induced by `B`, a map `A` into `S` and a map `Φ`
into `S'`: `(f, f') ↦ B (A f) (Φ f')`. -/
def inducedPairing {S S' : OperatorRealization F n} (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ)
    {d dd : List RealBlock} (A : realStandardKFinite n d →ₗ[ℂ] S.Space)
    (Φ : realStandardKFinite n dd →ₗ[ℂ] S'.Space) :
    realStandardKFinite n d →ₗ[ℂ] realStandardKFinite n dd →ₗ[ℂ] ℂ :=
  (B ∘ₗ A).compl₂ Φ

theorem inducedPairing_apply {S S' : OperatorRealization F n}
    (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ) {d dd : List RealBlock}
    (A : realStandardKFinite n d →ₗ[ℂ] S.Space)
    (Φ : realStandardKFinite n dd →ₗ[ℂ] S'.Space) (f : realStandardKFinite n d)
    (f' : realStandardKFinite n dd) :
    inducedPairing B A Φ f f' = B (A f) (Φ f') := rfl

/-- The Lie action at `v` of `1 ⊗ X` is the Lie action of the real direction `X` at `v`. -/
theorem realPlaceLieAction_one_tmul (S : OperatorRealization F n) (v : RP) (X : RM)
    (y : S.Space) :
    S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) y =
      S.lieAction (realPlaceLieInclusion F n v X) y := by
  have h1 : S.lieAction (realPlaceLieInclusion F n v X) y =
      S.complexLieAction (complexify F n (realPlaceLieInclusion F n v X)) y := rfl
  have h2 : S.realPlaceLieAction v ((1 : ℂ) ⊗ₜ[ℝ] X) y =
      S.complexLieAction (realPlaceComplexLieInclusion F n v ((1 : ℂ) ⊗ₜ[ℝ] X)) y := rfl
  exact h2.trans ((congrArg (fun Z => S.complexLieAction Z y)
    ((realPlaceComplexLieInclusion_tmul F n v 1 X).trans
      (complexify_apply F n (realPlaceLieInclusion F n v X)).symm)).trans h1.symm)

/-- An invariant pairing of operator realizations induces, through place-equivariant maps at
`v`, an invariant pairing of the real standard modules. -/
theorem isRealStandardInvariantPairing_induced {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {d dd : List RealBlock} {A : realStandardKFinite n d →ₗ[ℂ] S.Space}
    {Φ : realStandardKFinite n dd →ₗ[ℂ] S'.Space} (hA : IsPlaceEquivariant S v d A)
    (hΦ : IsPlaceEquivariant S' v dd Φ) :
    IsRealStandardInvariantPairing n d dd (inducedPairing B A Φ) := by
  refine ⟨fun l f f' => ?_, fun X f f' => ?_⟩
  · have h1 : inducedPairing B A Φ (realStandardRep n d l f) (realStandardRep n dd l f') =
        B (S.realPlaceCompactRepresentation v l (A f))
          (S'.realPlaceCompactRepresentation v l (Φ f')) :=
      congrArg₂ (fun a b => B a b) (hA.1 l f) (hΦ.1 l f')
    exact h1.trans (hB.2.1 (realPlaceCompactInclusion F n v l) (A f) (Φ f'))
  · have h1 : inducedPairing B A Φ (realStandardLie n d ((1 : ℂ) ⊗ₜ[ℝ] X) f) f' +
        inducedPairing B A Φ f (realStandardLie n dd ((1 : ℂ) ⊗ₜ[ℝ] X) f') =
        B (S.lieAction (realPlaceLieInclusion F n v X) (A f)) (Φ f') +
          B (A f) (S'.lieAction (realPlaceLieInclusion F n v X) (Φ f')) :=
      congrArg₂ (fun a b => a + b)
        (congrArg (fun a => B a (Φ f'))
          ((hA.2 X f).trans (realPlaceLieAction_one_tmul S v X (A f))))
        (congrArg (fun b => B (A f) b)
          ((hΦ.2 X f').trans (realPlaceLieAction_one_tmul S' v X (Φ f'))))
    exact h1.trans (hB.2.2 (realPlaceLieInclusion F n v X) (A f) (Φ f'))

/-- If the annihilator is the whole representation, every vector lies in it. -/
theorem mem_annihilator_of_eq_top {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {hB : S.IsInvariantPairing S' B} {v : RP}
    {ds : List RealBlock} (htop : annihilatorSubrepresentation S S' B hB v ds = ⊤)
    (y : S.Space) : y ∈ annihilator S S' B v ds := by
  have h : annihilator S S' B v ds = ⊤ := congrArg Subrepresentation.toSubmodule htop
  exact (congrArg (fun p : Submodule ℂ S.Space => y ∈ p) h).mpr Submodule.mem_top

/-- If the annihilator is zero, its only vector is zero. -/
theorem eq_zero_of_mem_annihilator {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} {hB : S.IsInvariantPairing S' B} {v : RP}
    {ds : List RealBlock} (hbot : annihilatorSubrepresentation S S' B hB v ds = ⊥)
    {y : S.Space} (hy : y ∈ annihilator S S' B v ds) : y = 0 := by
  have h : annihilator S S' B v ds = ⊥ := congrArg Subrepresentation.toSubmodule hbot
  exact (Submodule.mem_bot ℂ).1 ((congrArg (fun p : Submodule ℂ S.Space => y ∈ p) h).mp hy)

/-- If `B.flip` is injective and some injective place-equivariant map from a nontrivial
real standard module into `S'` exists, the annihilator is not the whole representation. -/
theorem annihilatorSubrepresentation_ne_top {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B)
    (hBinj : Function.Injective B.flip) {v : RP} {ds : List RealBlock}
    [Nontrivial (realStandardKFinite n ds)]
    {Ad : realStandardKFinite n ds →ₗ[ℂ] S'.Space} (hAd : IsPlaceEquivariant S' v ds Ad)
    (hAdinj : Function.Injective Ad) :
    annihilatorSubrepresentation S S' B hB v ds ≠ ⊤ := by
  intro htop
  have hne := exists_ne (0 : realStandardKFinite n ds)
  obtain ⟨f', hf'0⟩ := hne
  have hflip : B.flip (Ad f') = 0 := by
    refine LinearMap.ext fun y => ?_
    have h : B y (Ad f') = 0 :=
      (mem_annihilator y).1 (mem_annihilator_of_eq_top htop y) Ad hAd f'
    exact ((LinearMap.flip_apply B y (Ad f')).trans h).trans (LinearMap.zero_apply y).symm
  have hAd0 : Ad f' = 0 := hBinj (hflip.trans (map_zero B.flip).symm)
  exact hf'0 (hAdinj (hAd0.trans (map_zero Ad).symm))

/-- If the annihilator is zero, then for an injective place-equivariant `A` from a nontrivial
real standard module, some induced pairing `inducedPairing B A Φ` is nonzero; it is
invariant. -/
theorem exists_inducedPairing_ne_zero {S S' : OperatorRealization F n}
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsInvariantPairing S' B) {v : RP}
    {d dd : List RealBlock} [Nontrivial (realStandardKFinite n d)]
    {A : realStandardKFinite n d →ₗ[ℂ] S.Space} (hA : IsPlaceEquivariant S v d A)
    (hAinj : Function.Injective A)
    (hbot : annihilatorSubrepresentation S S' B hB v dd = ⊥) :
    ∃ P : realStandardKFinite n d →ₗ[ℂ] realStandardKFinite n dd →ₗ[ℂ] ℂ,
      IsRealStandardInvariantPairing n d dd P ∧ P ≠ 0 := by
  have hne := exists_ne (0 : realStandardKFinite n d)
  obtain ⟨f, hf0⟩ := hne
  have hAf0 : A f ≠ 0 := fun h => hf0 (hAinj (h.trans (map_zero A).symm))
  have hex : ∃ Φ : realStandardKFinite n dd →ₗ[ℂ] S'.Space,
      IsPlaceEquivariant S' v dd Φ ∧
        ∃ f' : realStandardKFinite n dd, B (A f) (Φ f') ≠ 0 := by
    by_contra hcon
    refine hAf0 (eq_zero_of_mem_annihilator hbot
      ((mem_annihilator (A f)).2 fun Φ hΦ f' => ?_))
    by_contra hne'
    exact hcon ⟨Φ, hΦ, f', hne'⟩
  obtain ⟨Φ, hΦ, f', hf'⟩ := hex
  refine ⟨inducedPairing B A Φ, isRealStandardInvariantPairing_induced hB hA hΦ,
    fun hP => ?_⟩
  have h := LinearMap.congr_fun (LinearMap.congr_fun hP f) f'
  have h0 : ((0 : realStandardKFinite n d →ₗ[ℂ]
      realStandardKFinite n dd →ₗ[ℂ] ℂ) f) f' = 0 := rfl
  exact hf' ((inducedPairing_apply B A Φ f f').symm.trans (h.trans h0))

variable [CompactSpace (AdeleQuotient F)]

/-- **The contragredient pairing restricts to the parameters.** If `Td` is contragredient to
the actual cuspidal realization `T`, and `ds`, `dds` are parameters of `T`, `Td` at the real
place `v`, then the `O(r+1)`-finite real standard modules of `ds` and `dds` carry a nonzero
invariant pairing. -/
theorem exists_realStandardInvariantPairing {r : ℕ}
    (T Td : CuspidalOperatorRealization F r)
    (hTd : Td.realization.IsContragredientOf T.realization) (v : RP)
    (ds dds : List RealBlock) (hds : T.realization.HasRealPlaceParameter v ds)
    (hdds : Td.realization.HasRealPlaceParameter v dds) :
    ∃ P : realStandardKFinite (r + 1) ds →ₗ[ℂ] realStandardKFinite (r + 1) dds →ₗ[ℂ] ℂ,
      IsRealStandardInvariantPairing (r + 1) ds dds P ∧ P ≠ 0 := by
  obtain ⟨B, hBi, -, hBinj, -⟩ := hTd
  obtain ⟨A, hAinj, hA⟩ := exists_isPlaceEquivariant_of_parameter T.realization v hds
  obtain ⟨Ad, hAdinj, hAd⟩ := exists_isPlaceEquivariant_of_parameter Td.realization v hdds
  have hntr : Nontrivial (realStandardKFinite (r + 1) ds) :=
    realStandardNontrivial (r + 1) ds hds.1
  have hntrd : Nontrivial (realStandardKFinite (r + 1) dds) :=
    realStandardNontrivial (r + 1) dds hdds.1
  rcases T.irreducible.eq_bot_or_eq_top
      (annihilatorSubrepresentation T.realization Td.realization B hBi v dds) with hbot | htop
  · exact exists_inducedPairing_ne_zero hBi hA hAinj hbot
  · exact absurd htop (annihilatorSubrepresentation_ne_top hBi hBinj hAd hAdinj)

end RealPlaceContragredient

open RealPlaceContragredient in
/-- **The reduction.** The real half of the published irreducibility statement and the local
pairing premise imply `RealPlaceContragredientPairLStatement`. -/
theorem realPlaceContragredientPairLReduction :
    RealPlaceContragredientPairLReductionStatement.{u} := by
  intro hG hL F _ _ _ r t T Td T' Td' hTd hTd' v ds es dds ees hds hes hdds hees
  obtain ⟨P, hP, hP0⟩ := exists_realStandardInvariantPairing T Td hTd v ds dds hds hdds
  obtain ⟨P', hP', hP'0⟩ := exists_realStandardInvariantPairing T' Td' hTd' v es ees hes hees
  have h1 := (hL (r + 1) ds dds hds.1 hdds.1 ((hG F r T).1 v ds hds)
    ((hG F r Td).1 v dds hdds) P hP hP0 ees).1
  have h2 := (hL (t + 1) es ees hes.1 hees.1 ((hG F t T').1 v es hes)
    ((hG F t Td').1 v ees hees) P' hP' hP'0 (ds.map RealLocalJacquet.dualBlock)).2
  exact h1.trans h2

end Langlands.Global.RankinSelbergGlobal
