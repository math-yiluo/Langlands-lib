import Langlands.Automorphic.PlaceComponentCarrier

/-!
# An admissible carrier for the place actions at a complex place

The complex-place analogue of `Langlands.Automorphic.PlaceComponentCarrier`: for an operator
realization `S`, a complex place `v`, an open subgroup `L` of the finite adelic group and a
representation `R` of the compact factors on `ℂ^m`, the carrier `S.complexCarrier v L R` of
linear maps `ℂ^m → S` with `L`-fixed values intertwining `R` with the compact action on the
factors trivial at `v` is stable under post-composition with the place actions at `v`, and it
is admissible for `U(n)` when `S` is jointly admissible.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance carrierCRationalAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance carrierCContinuousAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance carrierCSmoothAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance carrierCFormsAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance carrierCStableAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance carrierCSpaceAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

open scoped Classical in
/-- The compact factors with the component at the complex place `v` replaced by `1`. -/
def awayComplex (v : CP) : ArchimedeanCompactFactors F n →* ArchimedeanCompactFactors F n where
  toFun p := (p.1, Function.update p.2 v 1)
  map_one' := by
    refine Prod.ext rfl (funext fun w => ?_)
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Function.update_of_ne hw]
  map_mul' p q := by
    refine Prod.ext rfl (funext fun w => ?_)
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Function.update_of_ne hw]

open scoped Classical in
omit [NumberField F] in
theorem awayComplex_snd_self (v : CP) (p : ArchimedeanCompactFactors F n) :
    (awayComplex v p).2 v = 1 :=
  Function.update_self ..

open scoped Classical in
omit [NumberField F] in
theorem eq_complexPlaceFactor_mul_awayComplex (v : CP) (p : ArchimedeanCompactFactors F n) :
    p = ArchimedeanCompactFactors.complexPlaceFactor F n v (p.2 v) * awayComplex v p := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change p.1 w = 1 * p.1 w
    rw [one_mul]
  · change p.2 w = (Pi.mulSingle v (p.2 v) : CP → CK) w * Function.update p.2 v 1 w
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same, Function.update_self, mul_one]
    · rw [Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw, one_mul]

omit [NumberField F] in
/-- Compact factors trivial at `v` commute with the factor at `v`. -/
theorem commute_complexPlaceFactor (v : CP) {q : ArchimedeanCompactFactors F n}
    (hq : q.2 v = 1) (l : CK) : q * ArchimedeanCompactFactors.complexPlaceFactor F n v l =
      ArchimedeanCompactFactors.complexPlaceFactor F n v l * q := by
  classical
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change q.1 w * 1 = 1 * q.1 w
    rw [mul_one, one_mul]
  · change q.2 w * (Pi.mulSingle v l : CP → CK) w = (Pi.mulSingle v l : CP → CK) w * q.2 w
    by_cases hw : w = v
    · subst hw
      rw [hq, one_mul, mul_one]
    · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- Compact translation by factors trivial at `v` commutes with the compact action at `v`. -/
theorem compact_comm_complexPlaceCompact (v : CP) {q : ArchimedeanCompactFactors F n}
    (hq : q.2 v = 1) (l : CK) (y : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (S.complexPlaceCompactRepresentation v l y) =
      S.complexPlaceCompactRepresentation v l
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) := by
  have hk : ArchimedeanCompactFactors.toStandardCompact F n q *
      ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v l) =
      ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v l) *
      ArchimedeanCompactFactors.toStandardCompact F n q := by
    rw [← map_mul, ← map_mul, commute_complexPlaceFactor v hq l]
  have h1 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v l)) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v l)) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) :=
    (S.compactRepresentation.map_mul _ _).symm.trans
      ((congrArg S.compactRepresentation hk).trans (S.compactRepresentation.map_mul _ _))
  exact LinearMap.congr_fun h1 y

/-- Compact translation by factors trivial at `v` commutes with the Lie action at `v`. -/
theorem compact_comm_complexPlaceLie (v : CP) {q : ArchimedeanCompactFactors F n}
    (hq : q.2 v = 1) (X : ℂ ⊗[ℝ] CM) (y : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (S.complexPlaceLieAction v X y) =
      S.complexPlaceLieAction v X
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) := by
  have hX : unitaryMatrixComplexLieConjugation ℂ n (q.2 v) X = X := by
    rw [hq, unitaryMatrixComplexLieConjugation_one' ℂ X]
  exact (S.compactRepresentation_complexPlaceLieAction q v X y).trans
    (congrArg (fun Z => S.complexPlaceLieAction v Z
      (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y)) hX)

/-- The carrier at a complex place: linear maps `ℂ^m → S` with `L`-fixed values intertwining `R`
with the compact action on the factors trivial at `v`. -/
def complexCarrier (v : CP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] S.Space) where
  carrier := {φ | (∀ x, φ x ∈ fixedVectors S.finiteRepresentation L) ∧
    ∀ q : ArchimedeanCompactFactors F n, q.2 v = 1 → ∀ x,
      φ (R q x) = S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (φ x)}
  add_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun x => Submodule.add_mem _ (h1 x) (h3 x), fun q hq x =>
      (congrArg₂ (· + ·) (h2 q hq x) (h4 q hq x)).trans (map_add _ _ _).symm⟩
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun q _ x => (map_zero _).symm⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2⟩
    exact ⟨fun x => Submodule.smul_mem _ c (h1 x), fun q hq x =>
      (congrArg (c • ·) (h2 q hq x)).trans (map_smul _ c _).symm⟩

theorem mem_complexCarrier (v : CP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ))
    (φ : (Fin m → ℂ) →ₗ[ℂ] S.Space) :
    φ ∈ S.complexCarrier v L R ↔ (∀ x, φ x ∈ fixedVectors S.finiteRepresentation L) ∧
      ∀ q : ArchimedeanCompactFactors F n, q.2 v = 1 → ∀ x,
        φ (R q x) = S.compactRepresentation
          (ArchimedeanCompactFactors.toStandardCompact F n q) (φ x) :=
  Iff.rfl

/-- The carrier is stable under post-composition with the place actions at `v`. -/
theorem isStable_complexCarrier (v : CP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    IsStable (postRep m (S.complexPlaceCompactRepresentation v))
      (postLie m (S.complexPlaceLieAction v)) (S.complexCarrier v L R) := by
  refine ⟨fun l φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩,
    fun X φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩⟩
  · intro d
    exact (S.finiteRepresentation_complexPlaceCompactRepresentation d v l (φ x)).trans
      (congrArg (S.complexPlaceCompactRepresentation v l) (hφ.1 x d))
  · exact (congrArg (S.complexPlaceCompactRepresentation v l) (hφ.2 q hq x)).trans
      (S.compact_comm_complexPlaceCompact v hq l (φ x)).symm
  · intro d
    exact (S.finiteRepresentation_complexPlaceLieAction d v X (φ x)).trans
      (congrArg (S.complexPlaceLieAction v X) (hφ.1 x d))
  · exact (congrArg (S.complexPlaceLieAction v X) (hφ.2 q hq x)).trans
      (S.compact_comm_complexPlaceLie v hq X (φ x)).symm

/-- A compact translation splits into its factor at `v` and the rest. -/
theorem compact_eq_complexPlace_mul (v : CP) (k : standardInfiniteCompact F n) (y : S.Space) :
    S.compactRepresentation k y = S.complexPlaceCompactRepresentation v ((factorEquiv k).2 v)
      (S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n (awayComplex v (factorEquiv k))) y) := by
  have hk : k = ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v ((factorEquiv k).2 v) *
        awayComplex v (factorEquiv k)) :=
    (toStandardCompact_factorEquiv k).symm.trans
      (congrArg (ArchimedeanCompactFactors.toStandardCompact F n)
        (eq_complexPlaceFactor_mul_awayComplex v (factorEquiv k)))
  exact (congrArg (fun r => S.compactRepresentation r y) hk).trans
    (LinearMap.congr_fun ((congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)) y)

end OperatorRealization

/-- The representation `τ` at `v` tensored with `R` away from `v`, of the standard compact. -/
def complexCarrierRep (v : CP) {d m : ℕ} (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    Representation ℂ (standardInfiniteCompact F n) ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ)) :=
  Representation.tprod
    ((matrixRep τ).comp ((Pi.evalMonoidHom (fun _ : CP => CK) v).comp
      ((MonoidHom.snd _ _).comp (factorEquiv (F := F) (n := n)).toMonoidHom)))
    (R.comp ((awayComplex v).comp (factorEquiv (F := F) (n := n)).toMonoidHom))

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- The curried form of an intertwiner into the carrier intertwines `τ ⊗ R`. -/
theorem lift_mem_jointMultiplicity_complex (v : CP) (L : Subgroup (FiniteAdelicGL F n)) {d m : ℕ}
    (τ : CK →* Matrix (Fin d) (Fin d) ℂ)
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ))
    {Φ : (Fin d → ℂ) →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] S.Space)}
    (hΦ : Φ ∈ intertwiners (postRep m (S.complexPlaceCompactRepresentation v))
      (S.complexCarrier v L R) d τ) :
    (∀ t, TensorProduct.lift Φ t ∈ fixedVectors S.finiteRepresentation L) ∧
      ∀ (k : standardInfiniteCompact F n) t,
        TensorProduct.lift Φ (complexCarrierRep v τ R k t) =
          S.compactRepresentation k (TensorProduct.lift Φ t) := by
  refine ⟨fun t => ?_, fun k t => ?_⟩
  · induction t using TensorProduct.inductionOn with
    | tmul a b => exact (hΦ.1 a).1 b
    | add t₁ t₂ h₁ h₂ =>
      exact (map_add (TensorProduct.lift Φ) t₁ t₂).symm ▸ Submodule.add_mem _ h₁ h₂
  · induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have hp := awayComplex_snd_self v (factorEquiv k)
      have e1 : Φ (τ ((factorEquiv k).2 v) *ᵥ a) (R (awayComplex v (factorEquiv k)) b) =
          S.complexPlaceCompactRepresentation v ((factorEquiv k).2 v)
            (Φ a (R (awayComplex v (factorEquiv k)) b)) :=
        LinearMap.congr_fun (hΦ.2 ((factorEquiv k).2 v) a) _
      have e2 : Φ a (R (awayComplex v (factorEquiv k)) b) =
          S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
            (awayComplex v (factorEquiv k))) (Φ a b) := (hΦ.1 a).2 _ hp b
      exact e1.trans ((congrArg (S.complexPlaceCompactRepresentation v ((factorEquiv k).2 v)) e2).trans
        (S.compact_eq_complexPlace_mul v k (Φ a b)).symm)
    | add t₁ t₂ h₁ h₂ =>
      exact ((congrArg (TensorProduct.lift Φ) (map_add _ t₁ t₂)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) h₁ h₂))).trans
        ((map_add _ _ _).symm.trans (congrArg _ (map_add _ t₁ t₂).symm))

/-- **Admissibility of the carrier.** If `S` is jointly admissible, the carrier at a complex
place is admissible for the compact action at `v`. -/
theorem isAdmissible_complexCarrier (hJ : S.IsJointlyAdmissible) (v : CP)
    (L : OpenSubgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    PlaceComponent.IsAdmissible (postRep m (S.complexPlaceCompactRepresentation v))
      (S.complexCarrier v L.toSubgroup R) := by
  intro d τ _
  let ε := (Module.finBasis ℂ ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ))).equivFun
  let σ := conjRep ε (complexCarrierRep v τ R)
  have hfin : FiniteDimensional ℂ (jointMultiplicitySpace S.finiteRepresentation
      S.compactRepresentation L.toSubgroup σ) := hJ L _ σ
  have hmem : ∀ Φ ∈ intertwiners (postRep m (S.complexPlaceCompactRepresentation v))
      (S.complexCarrier v L.toSubgroup R) d τ,
      TensorProduct.lift Φ ∘ₗ ε.symm.toLinearMap ∈ jointMultiplicitySpace
        S.finiteRepresentation S.compactRepresentation L.toSubgroup σ := by
    intro Φ hΦ
    have h := S.lift_mem_jointMultiplicity_complex v L.toSubgroup τ R hΦ
    refine ⟨fun y => h.1 _, fun k y => ?_⟩
    have hσ : ε.symm (σ k y) = complexCarrierRep v τ R k (ε.symm y) :=
      ε.symm_apply_apply (complexCarrierRep v τ R k (ε.symm y))
    exact (congrArg (TensorProduct.lift Φ) hσ).trans (h.2 k (ε.symm y))
  let Ψ : intertwiners (postRep m (S.complexPlaceCompactRepresentation v))
      (S.complexCarrier v L.toSubgroup R) d τ →ₗ[ℂ] jointMultiplicitySpace
        S.finiteRepresentation S.compactRepresentation L.toSubgroup σ :=
    { toFun := fun Φ => ⟨TensorProduct.lift Φ.1 ∘ₗ ε.symm.toLinearMap, hmem Φ.1 Φ.2⟩
      map_add' := fun Φ₁ Φ₂ => Subtype.ext
        ((congrArg (· ∘ₗ ε.symm.toLinearMap)
          ((TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _).map_add Φ₁.1 Φ₂.1)).trans
          (LinearMap.add_comp _ _ _))
      map_smul' := fun c Φ => Subtype.ext
        ((congrArg (· ∘ₗ ε.symm.toLinearMap)
          ((TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _).map_smul c Φ.1)).trans
          (LinearMap.smul_comp _ _ _)) }
  have hΨ : Function.Injective Ψ := by
    intro Φ₁ Φ₂ h
    have h1 : TensorProduct.lift Φ₁.1 ∘ₗ ε.symm.toLinearMap =
        TensorProduct.lift Φ₂.1 ∘ₗ ε.symm.toLinearMap := congrArg Subtype.val h
    have h2 : TensorProduct.lift Φ₁.1 = TensorProduct.lift Φ₂.1 :=
      LinearMap.ext fun t => by
        have := LinearMap.congr_fun h1 (ε t)
        simpa using this
    exact Subtype.ext ((TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _).injective h2)
  have hN : IsNoetherian ℂ (jointMultiplicitySpace S.finiteRepresentation
      S.compactRepresentation L.toSubgroup σ) :=
    isNoetherian_of_isNoetherianRing_of_finite ℂ (jointMultiplicitySpace
      S.finiteRepresentation S.compactRepresentation L.toSubgroup σ)
  exact Module.Finite.of_injective Ψ hΨ

end OperatorRealization

end Langlands.Automorphic
