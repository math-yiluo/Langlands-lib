import Langlands.Automorphic.PlaceComponentHom
import Langlands.Automorphic.PlaceComponentRealization
import Langlands.Automorphic.CuspidalJointAdmissibility

/-!
# An admissible carrier for the place actions at a real place

Let `S` be an operator realization of `GL_n`, `v` a real place, `L` an open subgroup of the
finite adelic group and `R` a representation of the compact factors `∏_w K_w` on `ℂ^m`. The
carrier `S.realCarrier v L R` is the space of linear maps `φ : ℂ^m → S` with `L`-fixed values
that intertwine `R` with the compact action on the factors trivial at `v`. The place actions at
`v` act on it by post-composition. If `S` is jointly admissible, the carrier is admissible for
`O(n)`: an intertwiner `Φ` from a matrix representation `τ` of `O(n)` into the carrier curries
to a linear map on `ℂ^d ⊗ ℂ^m` that intertwines `τ ⊗ R` (as a representation of the whole
standard compact) with the compact action, with `L`-fixed values.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Global Langlands.Global.ArchimedeanGL PlaceComponent

local instance carrierRationalAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance carrierContinuousAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance carrierSmoothAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance carrierFormsAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance carrierStableAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance carrierSpaceAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ

open scoped Classical in
/-- The compact factors with the component at the real place `v` replaced by `1`. -/
def awayReal (v : RP) : ArchimedeanCompactFactors F n →* ArchimedeanCompactFactors F n where
  toFun p := (Function.update p.1 v 1, p.2)
  map_one' := by
    refine Prod.ext (funext fun w => ?_) rfl
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Function.update_of_ne hw]
  map_mul' p q := by
    refine Prod.ext (funext fun w => ?_) rfl
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Function.update_of_ne hw]

open scoped Classical in
omit [NumberField F] in
theorem awayReal_fst_self (v : RP) (p : ArchimedeanCompactFactors F n) :
    (awayReal v p).1 v = 1 :=
  Function.update_self ..

open scoped Classical in
omit [NumberField F] in
theorem eq_realPlaceFactor_mul_awayReal (v : RP) (p : ArchimedeanCompactFactors F n) :
    p = ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v) * awayReal v p := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change p.1 w = (Pi.mulSingle v (p.1 v) : RP → RK) w * Function.update p.1 v 1 w
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same, Function.update_self, mul_one]
    · rw [Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw, one_mul]
  · change p.2 w = 1 * p.2 w
    rw [one_mul]

omit [NumberField F] in
/-- Compact factors trivial at `v` commute with the factor at `v`. -/
theorem commute_realPlaceFactor (v : RP) {q : ArchimedeanCompactFactors F n} (hq : q.1 v = 1)
    (l : RK) : q * ArchimedeanCompactFactors.realPlaceFactor F n v l =
      ArchimedeanCompactFactors.realPlaceFactor F n v l * q := by
  classical
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change q.1 w * (Pi.mulSingle v l : RP → RK) w = (Pi.mulSingle v l : RP → RK) w * q.1 w
    by_cases hw : w = v
    · subst hw
      rw [hq, one_mul, mul_one]
    · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
  · change q.2 w * 1 = 1 * q.2 w
    rw [mul_one, one_mul]

/-- The inverse of the product decomposition of the standard compact. -/
def factorEquiv : standardInfiniteCompact F n ≃* ArchimedeanCompactFactors F n :=
  (MulEquiv.ofBijective (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩).symm

omit [NumberField F] in
theorem toStandardCompact_factorEquiv (k : standardInfiniteCompact F n) :
    ArchimedeanCompactFactors.toStandardCompact F n (factorEquiv k) = k :=
  (MulEquiv.ofBijective (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩).apply_symm_apply k

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- Compact translation by factors trivial at `v` commutes with the compact action at `v`. -/
theorem compact_comm_realPlaceCompact (v : RP) {q : ArchimedeanCompactFactors F n}
    (hq : q.1 v = 1) (l : RK) (y : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (S.realPlaceCompactRepresentation v l y) =
      S.realPlaceCompactRepresentation v l
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) := by
  have hk : ArchimedeanCompactFactors.toStandardCompact F n q *
      ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v l) =
      ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v l) *
      ArchimedeanCompactFactors.toStandardCompact F n q := by
    rw [← map_mul, ← map_mul, commute_realPlaceFactor v hq l]
  have h1 : S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v l)) =
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v l)) *
      S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) :=
    (S.compactRepresentation.map_mul _ _).symm.trans
      ((congrArg S.compactRepresentation hk).trans (S.compactRepresentation.map_mul _ _))
  exact LinearMap.congr_fun h1 y

/-- Compact translation by factors trivial at `v` commutes with the Lie action at `v`. -/
theorem compact_comm_realPlaceLie (v : RP) {q : ArchimedeanCompactFactors F n}
    (hq : q.1 v = 1) (X : ℂ ⊗[ℝ] RM) (y : S.Space) :
    S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q)
        (S.realPlaceLieAction v X y) =
      S.realPlaceLieAction v X
        (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y) := by
  have hX : unitaryMatrixComplexLieConjugation ℝ n (q.1 v) X = X := by
    rw [hq, unitaryMatrixComplexLieConjugation_one' ℝ X]
  exact (S.compactRepresentation_realPlaceLieAction q v X y).trans
    (congrArg (fun Z => S.realPlaceLieAction v Z
      (S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n q) y)) hX)

/-- The carrier at a real place: linear maps `ℂ^m → S` with `L`-fixed values intertwining `R`
with the compact action on the factors trivial at `v`. -/
def realCarrier (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] S.Space) where
  carrier := {φ | (∀ x, φ x ∈ fixedVectors S.finiteRepresentation L) ∧
    ∀ q : ArchimedeanCompactFactors F n, q.1 v = 1 → ∀ x,
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

theorem mem_realCarrier (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ))
    (φ : (Fin m → ℂ) →ₗ[ℂ] S.Space) :
    φ ∈ S.realCarrier v L R ↔ (∀ x, φ x ∈ fixedVectors S.finiteRepresentation L) ∧
      ∀ q : ArchimedeanCompactFactors F n, q.1 v = 1 → ∀ x,
        φ (R q x) = S.compactRepresentation
          (ArchimedeanCompactFactors.toStandardCompact F n q) (φ x) :=
  Iff.rfl

/-- The carrier is stable under post-composition with the place actions at `v`. -/
theorem isStable_realCarrier (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    IsStable (postRep m (S.realPlaceCompactRepresentation v))
      (postLie m (S.realPlaceLieAction v)) (S.realCarrier v L R) := by
  refine ⟨fun l φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩,
    fun X φ hφ => ⟨fun x => ?_, fun q hq x => ?_⟩⟩
  · intro d
    exact (S.finiteRepresentation_realPlaceCompactRepresentation d v l (φ x)).trans
      (congrArg (S.realPlaceCompactRepresentation v l) (hφ.1 x d))
  · exact (congrArg (S.realPlaceCompactRepresentation v l) (hφ.2 q hq x)).trans
      (S.compact_comm_realPlaceCompact v hq l (φ x)).symm
  · intro d
    exact (S.finiteRepresentation_realPlaceLieAction d v X (φ x)).trans
      (congrArg (S.realPlaceLieAction v X) (hφ.1 x d))
  · exact (congrArg (S.realPlaceLieAction v X) (hφ.2 q hq x)).trans
      (S.compact_comm_realPlaceLie v hq X (φ x)).symm

/-- A compact translation splits into its factor at `v` and the rest. -/
theorem compact_eq_realPlace_mul (v : RP) (k : standardInfiniteCompact F n) (y : S.Space) :
    S.compactRepresentation k y = S.realPlaceCompactRepresentation v ((factorEquiv k).1 v)
      (S.compactRepresentation
        (ArchimedeanCompactFactors.toStandardCompact F n (awayReal v (factorEquiv k))) y) := by
  have hk : k = ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v ((factorEquiv k).1 v) *
        awayReal v (factorEquiv k)) :=
    (toStandardCompact_factorEquiv k).symm.trans
      (congrArg (ArchimedeanCompactFactors.toStandardCompact F n)
        (eq_realPlaceFactor_mul_awayReal v (factorEquiv k)))
  exact (congrArg (fun r => S.compactRepresentation r y) hk).trans
    (LinearMap.congr_fun ((congrArg S.compactRepresentation
      ((ArchimedeanCompactFactors.toStandardCompact F n).map_mul _ _)).trans
      (S.compactRepresentation.map_mul _ _)) y)

end OperatorRealization

/-- A matrix representation as a representation on column vectors. -/
def matrixRep {K : Type*} [Group K] {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ K (Fin d → ℂ) where
  toFun k := Matrix.mulVecLin (τ k)
  map_one' := by
    rw [map_one, Matrix.mulVecLin_one]
    rfl
  map_mul' k l := by
    rw [map_mul, Matrix.mulVecLin_mul]
    rfl

/-- Transport of a representation along a linear equivalence. -/
def conjRep {G : Type*} [Group G] {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (ε : M ≃ₗ[ℂ] N) (ρ : Representation ℂ G M) :
    Representation ℂ G N where
  toFun g := ε.toLinearMap ∘ₗ ρ g ∘ₗ ε.symm.toLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp

/-- The representation `τ` at `v` tensored with `R` away from `v`, of the standard compact. -/
def realCarrierRep (v : RP) {d m : ℕ} (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    Representation ℂ (standardInfiniteCompact F n) ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ)) :=
  Representation.tprod
    ((matrixRep τ).comp ((Pi.evalMonoidHom (fun _ : RP => RK) v).comp
      ((MonoidHom.fst _ _).comp (factorEquiv (F := F) (n := n)).toMonoidHom)))
    (R.comp ((awayReal v).comp (factorEquiv (F := F) (n := n)).toMonoidHom))

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- The curried form of an intertwiner into the carrier intertwines `τ ⊗ R`. -/
theorem lift_mem_jointMultiplicity (v : RP) (L : Subgroup (FiniteAdelicGL F n)) {d m : ℕ}
    (τ : RK →* Matrix (Fin d) (Fin d) ℂ)
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ))
    {Φ : (Fin d → ℂ) →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] S.Space)}
    (hΦ : Φ ∈ intertwiners (postRep m (S.realPlaceCompactRepresentation v))
      (S.realCarrier v L R) d τ) :
    (∀ t, TensorProduct.lift Φ t ∈ fixedVectors S.finiteRepresentation L) ∧
      ∀ (k : standardInfiniteCompact F n) t,
        TensorProduct.lift Φ (realCarrierRep v τ R k t) =
          S.compactRepresentation k (TensorProduct.lift Φ t) := by
  refine ⟨fun t => ?_, fun k t => ?_⟩
  · induction t using TensorProduct.inductionOn with
    | tmul a b => exact (hΦ.1 a).1 b
    | add t₁ t₂ h₁ h₂ =>
      exact (map_add (TensorProduct.lift Φ) t₁ t₂).symm ▸ Submodule.add_mem _ h₁ h₂
  · induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have hp := awayReal_fst_self v (factorEquiv k)
      have e1 : Φ (τ ((factorEquiv k).1 v) *ᵥ a) (R (awayReal v (factorEquiv k)) b) =
          S.realPlaceCompactRepresentation v ((factorEquiv k).1 v)
            (Φ a (R (awayReal v (factorEquiv k)) b)) :=
        LinearMap.congr_fun (hΦ.2 ((factorEquiv k).1 v) a) _
      have e2 : Φ a (R (awayReal v (factorEquiv k)) b) =
          S.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
            (awayReal v (factorEquiv k))) (Φ a b) := (hΦ.1 a).2 _ hp b
      exact e1.trans ((congrArg (S.realPlaceCompactRepresentation v ((factorEquiv k).1 v)) e2).trans
        (S.compact_eq_realPlace_mul v k (Φ a b)).symm)
    | add t₁ t₂ h₁ h₂ =>
      exact ((congrArg (TensorProduct.lift Φ) (map_add _ t₁ t₂)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) h₁ h₂))).trans
        ((map_add _ _ _).symm.trans (congrArg _ (map_add _ t₁ t₂).symm))

/-- **Admissibility of the carrier.** If `S` is jointly admissible, the carrier at a real
place is admissible for the compact action at `v`. -/
theorem isAdmissible_realCarrier (hJ : S.IsJointlyAdmissible) (v : RP)
    (L : OpenSubgroup (FiniteAdelicGL F n)) {m : ℕ}
    (R : Representation ℂ (ArchimedeanCompactFactors F n) (Fin m → ℂ)) :
    PlaceComponent.IsAdmissible (postRep m (S.realPlaceCompactRepresentation v))
      (S.realCarrier v L.toSubgroup R) := by
  intro d τ _
  let ε := (Module.finBasis ℂ ((Fin d → ℂ) ⊗[ℂ] (Fin m → ℂ))).equivFun
  let σ := conjRep ε (realCarrierRep v τ R)
  have hfin : FiniteDimensional ℂ (jointMultiplicitySpace S.finiteRepresentation
      S.compactRepresentation L.toSubgroup σ) := hJ L _ σ
  have hmem : ∀ Φ ∈ intertwiners (postRep m (S.realPlaceCompactRepresentation v))
      (S.realCarrier v L.toSubgroup R) d τ,
      TensorProduct.lift Φ ∘ₗ ε.symm.toLinearMap ∈ jointMultiplicitySpace
        S.finiteRepresentation S.compactRepresentation L.toSubgroup σ := by
    intro Φ hΦ
    have h := S.lift_mem_jointMultiplicity v L.toSubgroup τ R hΦ
    refine ⟨fun y => h.1 _, fun k y => ?_⟩
    have hσ : ε.symm (σ k y) = realCarrierRep v τ R k (ε.symm y) :=
      ε.symm_apply_apply (realCarrierRep v τ R k (ε.symm y))
    exact (congrArg (TensorProduct.lift Φ) hσ).trans (h.2 k (ε.symm y))
  let Ψ : intertwiners (postRep m (S.realPlaceCompactRepresentation v))
      (S.realCarrier v L.toSubgroup R) d τ →ₗ[ℂ] jointMultiplicitySpace
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
