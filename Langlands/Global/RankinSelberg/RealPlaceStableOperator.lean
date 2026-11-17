import Langlands.Automorphic.PlaceComponentRealization

/-!
# Subspaces stable under the commutant of the place actions at a real place

Let `S` be an operator realization of `GL_n` over a number field and `w` a real place. If a
subspace `Z` of `S` is stable under the compact and Lie place actions at `w` and under every
linear endomorphism commuting with both, then `Z` is stable under the whole concrete operator
algebra. In an irreducible realization such a `Z` is `⊥` or `⊤`.

The proof copies the Library's proof that the free set at a real place is stable
(`OperatorRealization.realFreeSet_operator`, module `PlaceComponentRealization`), with the
free set replaced by `Z`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance placeStableRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeStableContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeStableSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeStableFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeStableStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeStableSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- `Z` is stable under the place actions at the real place `w` and under every linear
endomorphism of `S` commuting with them. -/
def IsRealPlaceCommutantStable (w : RP) (Z : Submodule ℂ S.Space) : Prop :=
  (∀ P : S.Space →ₗ[ℂ] S.Space,
      (∀ (k : RK) (y : S.Space),
        P (S.realPlaceCompactRepresentation w k y) =
          S.realPlaceCompactRepresentation w k (P y)) →
      (∀ (X : ℂ ⊗[ℝ] RM) (y : S.Space),
        P (S.realPlaceLieAction w X y) = S.realPlaceLieAction w X (P y)) →
      ∀ x ∈ Z, P x ∈ Z) ∧
    (∀ (k : RK), ∀ x ∈ Z, S.realPlaceCompactRepresentation w k x ∈ Z) ∧
    ∀ (X : ℂ ⊗[ℝ] RM), ∀ x ∈ Z, S.realPlaceLieAction w X x ∈ Z

variable {S}

section Stable

theorem IsRealPlaceCommutantStable.finite {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) (g : FiniteAdelicGL F n) {x : S.Space}
    (hx : x ∈ Z) : S.finiteRepresentation g x ∈ Z :=
  hZ.1 (S.finiteRepresentation g)
    (fun k y => S.finiteRepresentation_realPlaceCompactRepresentation g w k y)
    (fun X y => S.finiteRepresentation_realPlaceLieAction g w X y) x hx

theorem IsRealPlaceCommutantStable.realLie {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) {v : RP} (X : ℂ ⊗[ℝ] RM) {x : S.Space}
    (hx : x ∈ Z) : S.realPlaceLieAction v X x ∈ Z := by
  by_cases hv : v = w
  · subst hv
    exact hZ.2.2 X x hx
  · exact hZ.1 (S.realPlaceLieAction v X)
      (fun k y =>
        (S.realPlaceCompactRepresentation_realPlaceLieAction_of_ne w v hv k X y).symm)
      (fun Y y => (S.realPlaceLieAction_comm_of_ne hv Y X y).symm) x hx

theorem IsRealPlaceCommutantStable.complexLie {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) (v : CP) (X : ℂ ⊗[ℝ] CM) {x : S.Space}
    (hx : x ∈ Z) : S.complexPlaceLieAction v X x ∈ Z :=
  hZ.1 (S.complexPlaceLieAction v X)
    (fun k y => (S.realPlaceCompactRepresentation_complexPlaceLieAction w v k X y).symm)
    (fun Y y => (S.realPlaceLieAction_comm_complexPlace w v Y X y).symm) x hx

theorem IsRealPlaceCommutantStable.complexLieAction {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) (Y : ComplexLieAlgebra F n)
    {x : S.Space} (hx : x ∈ Z) : S.complexLieAction Y x ∈ Z := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hzX : z ⊗ₜ[ℝ] X = z • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have heq : S.complexLieAction (z ⊗ₜ[ℝ] X) x =
        z • S.complexLieAction (complexify F n X) x :=
      (congrArg (fun Y => S.complexLieAction Y x) hzX).trans
        (LinearMap.congr_fun (S.complexLieAction.map_smul z (complexify F n X)) x)
    have hmem : S.complexLieAction (complexify F n X) x ∈ Z := by
      refine (congrArg (fun y => y ∈ Z) (S.complexify_action_eq_sum_place X x)).mpr ?_
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun v _ => ?_)
        (Submodule.sum_mem _ fun v _ => ?_)
      · exact hZ.realLie _ hx
      · exact hZ.complexLie v _ hx
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.smul_mem _ z hmem)
  | add Y₁ Y₂ h₁ h₂ =>
    have heq : S.complexLieAction (Y₁ + Y₂) x =
        S.complexLieAction Y₁ x + S.complexLieAction Y₂ x :=
      LinearMap.congr_fun (S.complexLieAction.map_add Y₁ Y₂) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.add_mem _ h₁ h₂)

theorem IsRealPlaceCommutantStable.enveloping {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) (u : EnvelopingAlgebra F n) :
    ∀ x ∈ Z, S.envelopingAction u x ∈ Z := by
  have hu : u ∈ Algebra.adjoin ℂ
      (Set.range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra F n → EnvelopingAlgebra F n)) := by
    rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
    trivial
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨Y, rfl⟩ := hu
    intro x hx
    exact hZ.complexLieAction Y hx
  | algebraMap c =>
    intro x hx
    have heq : S.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n) c) x = c • x :=
      LinearMap.congr_fun (S.envelopingAction.commutes c) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.smul_mem _ c hx)
  | add a b _ _ ha hb =>
    intro x hx
    have heq : S.envelopingAction (a + b) x = S.envelopingAction a x + S.envelopingAction b x :=
      LinearMap.congr_fun (S.envelopingAction.map_add a b) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (Submodule.add_mem _ (ha x hx) (hb x hx))
  | mul a b _ _ ha hb =>
    intro x hx
    have heq : S.envelopingAction (a * b) x = S.envelopingAction a (S.envelopingAction b x) :=
      LinearMap.congr_fun (S.envelopingAction.map_mul a b) x
    exact (congrArg (fun y => y ∈ Z) heq).mpr (ha _ (hb x hx))

theorem IsRealPlaceCommutantStable.compact {v : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable v Z) (k : standardInfiniteCompact F n) {x : S.Space}
    (hx : x ∈ Z) : S.compactRepresentation k x ∈ Z := by
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
  have hcomm : ∀ l : RK, p' * ArchimedeanCompactFactors.realPlaceFactor F n v l =
      ArchimedeanCompactFactors.realPlaceFactor F n v l * p' := fun l => by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · change p'.1 w * (Pi.mulSingle v l : RP → RK) w = (Pi.mulSingle v l : RP → RK) w * p'.1 w
      rw [hp'1]
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, one_mul, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
    · change p'.2 w * 1 = 1 * p'.2 w
      rw [mul_one, one_mul]
  have hCκ : ∀ (l : RK) (y : S.Space),
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p')
          (S.realPlaceCompactRepresentation v l y) =
        S.realPlaceCompactRepresentation v l
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) := by
    intro l y
    have hk : ArchimedeanCompactFactors.toStandardCompact F n p' *
        ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l) =
        ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l) *
        ArchimedeanCompactFactors.toStandardCompact F n p' := by
      rw [← map_mul, ← map_mul, hcomm l]
    have h1 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') *
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l)) =
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
          (ArchimedeanCompactFactors.realPlaceFactor F n v l)) *
        S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
      (S.compactRepresentation.map_mul _ _).symm.trans
        ((congrArg S.compactRepresentation hk).trans (S.compactRepresentation.map_mul _ _))
    exact LinearMap.congr_fun h1 y
  have hp'v : p'.1 v = 1 := by rw [hp'1, Function.update_self]
  have hCπ : ∀ (X : ℂ ⊗[ℝ] RM) (y : S.Space),
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p')
          (S.realPlaceLieAction v X y) =
        S.realPlaceLieAction v X
          (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y) := by
    intro X y
    have hX : unitaryMatrixComplexLieConjugation ℝ n (p'.1 v) X = X := by
      rw [hp'v, unitaryMatrixComplexLieConjugation_one' ℝ X]
    exact (S.compactRepresentation_realPlaceLieAction p' v X y).trans
      (congrArg (fun Z => S.realPlaceLieAction v Z
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') y)) hX)
  have hCx : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') x ∈
      Z := hZ.1 _ hCκ hCπ x hx
  have h2 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v) * p')) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v))) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') :=
    (congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)
  have hsplit : S.compactRepresentation k x =
      S.realPlaceCompactRepresentation v (p.1 v)
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p') x) :=
    ((congrArg (fun r => S.compactRepresentation r x) hpk.symm).trans
      (congrArg (fun r => S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n r) x) hp)).trans
      (LinearMap.congr_fun h2 x)
  exact (congrArg (fun y => y ∈ Z) hsplit).mpr (hZ.2.1 (p.1 v) _ hCx)

/-- A subspace stable under the place actions at `w` and their commutant is stable under the
whole concrete operator algebra. -/
theorem IsRealPlaceCommutantStable.operator {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) (a : automorphicOperatorAlgebra F n) :
    ∀ x ∈ Z, S.representation a x ∈ Z := by
  obtain ⟨e, he⟩ := a
  induction he using Algebra.adjoin_induction with
  | mem e he =>
    rcases he with (⟨g, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
    · exact fun x hx => hZ.finite g hx
    · exact fun x hx => hZ.compact k hx
    · exact fun x hx => hZ.enveloping u x hx
  | algebraMap c =>
    intro x hx
    have h : S.representation ⟨algebraMap ℂ (FiniteSmoothEnd F n) c,
        Subalgebra.algebraMap_mem _ c⟩ x = c • x := rfl
    rw [h]
    exact Submodule.smul_mem _ c hx
  | add e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : S.representation ⟨e₁ + e₂, Subalgebra.add_mem _ he₁ he₂⟩ x =
        S.representation ⟨e₁, he₁⟩ x + S.representation ⟨e₂, he₂⟩ x := rfl
    rw [h]
    exact Submodule.add_mem _ (h₁ x hx) (h₂ x hx)
  | mul e₁ e₂ he₁ he₂ h₁ h₂ =>
    intro x hx
    have h : S.representation ⟨e₁ * e₂, Subalgebra.mul_mem _ he₁ he₂⟩ x =
        S.representation ⟨e₁, he₁⟩ (S.representation ⟨e₂, he₂⟩ x) := rfl
    rw [h]
    exact h₁ _ (h₂ x hx)

/-- In an irreducible realization a subspace stable under the place actions at `w` and their
commutant is `⊥` or `⊤`. -/
theorem IsRealPlaceCommutantStable.eq_bot_or_eq_top {w : RP} {Z : Submodule ℂ S.Space}
    (hZ : S.IsRealPlaceCommutantStable w Z) (hS : S.IsIrreducible) :
    Z = ⊥ ∨ Z = ⊤ := by
  let Z' : Subrepresentation S.representation := ⟨Z, fun a x hx => hZ.operator a x hx⟩
  have hirr : IsSimpleOrder (Subrepresentation S.representation) := hS
  rcases hirr.eq_bot_or_eq_top Z' with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

end Stable

end OperatorRealization

end Langlands.Automorphic
