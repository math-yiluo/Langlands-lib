import Langlands.Global.Factors.RelativeWeilLocalEuler
import Langlands.Correspondence.RankOneArithmeticLFactor
import Langlands.Correspondence.CharacterSumEuler
import Langlands.Representation.GodementJacquet.TateRationalContinuation
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.LocalFactor.Inductive.LocalInductionAux
import Langlands.Global.CompletionPadicTower
import Langlands.Global.Factors.RelativeWeilLocalEpsilonTransport
import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.Global.AdelicFunctoriality.Trace

/-!
# Rank-one L-factors of the local virtual identity as Tate's L-factors
-/

noncomputable section

set_option autoImplicit false

universe u uA w

open Polynomial

namespace Langlands.Weil.Local.InertiaEuler

open Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance eulerBridgeTopology (K : PadicField.{u} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- For a geometric reciprocity candidate `e` of `F`, the classical Euler polynomial of the
Weil character `η ∘ e` is Tate's Euler polynomial of the quasicharacter `η`. -/
theorem characterEulerPolynomial_weilCharacter {e : LocalFactor.RankOne.ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (η : QuasiCharacter F) :
    characterEulerPolynomial F (LocalFactor.RankOne.weilCharacter F e η) =
      LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData η := by
  classical
  unfold characterEulerPolynomial
  by_cases hc : F.canonicalTopologicalData.multiplicativeConductor η = 0
  · have hη := (isUnramifiedQuasicharacter_iff_isUnramifiedCharacter F η).mp
      ((F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff η).mp hc)
    have hI : ∀ x ∈ localInertia F, LocalFactor.RankOne.weilCharacter F e η x = 1 :=
      (weilCharacter_trivial_on_inertia_iff F he η).mpr hη
    rw [ite_eq_left hI, LocalFactor.PadicAbelian.lPolynomial, ite_eq_left hc]
    have hFr := weilCharacter_localGeometricFrobenius he hη
    change 1 - C ((weilCharacter F e η (localGeometricFrobenius F) : ℂˣ) : ℂ) * X = _
    rw [hFr]
  · have hI : ¬ ∀ x ∈ localInertia F, LocalFactor.RankOne.weilCharacter F e η x = 1 := by
      intro h
      apply hc
      exact (F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff η).mpr
        ((isUnramifiedQuasicharacter_iff_isUnramifiedCharacter F η).mpr
          ((weilCharacter_trivial_on_inertia_iff F he η).mp h))
    rw [ite_eq_right hI, LocalFactor.PadicAbelian.lPolynomial, ite_eq_right hc]

/-- With a geometric candidate `e` of `E`, the L-factor over `F` of the representation induced
from `η ∘ e` is Tate's L-factor of `η` with `X` replaced by `X^f`, `f` the residue degree. -/
theorem inducedLFactor_weilCharacter (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) {e : LocalFactor.RankOne.ReciprocityCandidate E}
    (he : IsGeometricReciprocity E e) (η : QuasiCharacter E) :
    inducedLFactor F E g (LocalFactor.RankOne.weilCharacter E e η) =
      (algebraMap ℂ[X] (RatFunc ℂ) (expand ℂ (extensionResidueDegree F E g)
        (LocalFactor.PadicAbelian.lPolynomial E.canonicalTopologicalData η)))⁻¹ := by
  rw [inducedLFactor, characterEulerPolynomial_weilCharacter E he η]

/-- With a geometric candidate `e` of `F`, the L-factor of the character `η ∘ e` is Tate's
rational L-factor of `η`. -/
theorem characterLFactor_weilCharacter {e : LocalFactor.RankOne.ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (η : QuasiCharacter F) :
    characterLFactor F (LocalFactor.RankOne.weilCharacter F e η) =
      LocalFactor.PadicAbelian.rationalLFactor F.canonicalTopologicalData η := by
  rw [characterLFactor, characterEulerPolynomial_weilCharacter F he η]
  rfl

section Evaluation

open RankinSelberg FiniteRepresentation VirtualRepresentation
  VirtualRepresentation.ExactGrothendieckGroup

/-- A rational function is a regular unit at `x` when it is a quotient of two polynomials,
neither of which vanishes at `x`. -/
def IsRegularUnitAt (x : ℂ) (r : RatFunc ℂ) : Prop :=
  ∃ N D : ℂ[X], N.eval x ≠ 0 ∧ D.eval x ≠ 0 ∧
    r = algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D

theorem eval_algebraMap_div_algebraMap (x : ℂ) (N D : ℂ[X]) (hD : D.eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) x
        (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D) =
      N.eval x / D.eval x :=
  (regular_and_eval_div x N D hD).2

namespace IsRegularUnitAt

variable {x : ℂ} {r r' : RatFunc ℂ}

theorem eval_ne_zero (hr : IsRegularUnitAt x r) : RatFunc.eval (RingHom.id ℂ) x r ≠ 0 := by
  obtain ⟨N, D, hN, hD, rfl⟩ := hr
  rw [eval_algebraMap_div_algebraMap x N D hD]
  exact div_ne_zero hN hD

theorem one : IsRegularUnitAt x 1 :=
  ⟨1, 1, by simp, by simp, by simp⟩

theorem eval_one : RatFunc.eval (RingHom.id ℂ) x 1 = 1 := by
  simp

theorem mul (hr : IsRegularUnitAt x r) (hr' : IsRegularUnitAt x r') :
    IsRegularUnitAt x (r * r') := by
  obtain ⟨N, D, hN, hD, rfl⟩ := hr
  obtain ⟨N', D', hN', hD', rfl⟩ := hr'
  refine ⟨N * N', D * D', by simp [hN, hN'], by simp [hD, hD'], ?_⟩
  rw [map_mul, map_mul, div_mul_div_comm]

theorem eval_mul (hr : IsRegularUnitAt x r) (hr' : IsRegularUnitAt x r') :
    RatFunc.eval (RingHom.id ℂ) x (r * r') =
      RatFunc.eval (RingHom.id ℂ) x r * RatFunc.eval (RingHom.id ℂ) x r' := by
  obtain ⟨N, D, hN, hD, rfl⟩ := hr
  obtain ⟨N', D', hN', hD', rfl⟩ := hr'
  have hDD : (D * D').eval x ≠ 0 := by simp [hD, hD']
  rw [div_mul_div_comm, ← map_mul, ← map_mul, eval_algebraMap_div_algebraMap x _ _ hDD,
    eval_algebraMap_div_algebraMap x N D hD, eval_algebraMap_div_algebraMap x N' D' hD',
    eval_mul, eval_mul, div_mul_div_comm]

theorem inv (hr : IsRegularUnitAt x r) : IsRegularUnitAt x r⁻¹ := by
  obtain ⟨N, D, hN, hD, rfl⟩ := hr
  exact ⟨D, N, hD, hN, inv_div _ _⟩

theorem eval_inv (hr : IsRegularUnitAt x r) :
    RatFunc.eval (RingHom.id ℂ) x r⁻¹ = (RatFunc.eval (RingHom.id ℂ) x r)⁻¹ := by
  obtain ⟨N, D, hN, hD, rfl⟩ := hr
  rw [inv_div, eval_algebraMap_div_algebraMap x D N hN, eval_algebraMap_div_algebraMap x N D hD,
    inv_div]

theorem div (hr : IsRegularUnitAt x r) (hr' : IsRegularUnitAt x r') :
    IsRegularUnitAt x (r / r') := by
  rw [div_eq_mul_inv]
  exact hr.mul hr'.inv

theorem eval_div (hr : IsRegularUnitAt x r) (hr' : IsRegularUnitAt x r') :
    RatFunc.eval (RingHom.id ℂ) x (r / r') =
      RatFunc.eval (RingHom.id ℂ) x r / RatFunc.eval (RingHom.id ℂ) x r' := by
  rw [div_eq_mul_inv, hr.eval_mul hr'.inv, hr'.eval_inv, ← div_eq_mul_inv]

theorem pow (hr : IsRegularUnitAt x r) (k : ℕ) : IsRegularUnitAt x (r ^ k) := by
  induction k with
  | zero => simpa using (one : IsRegularUnitAt x 1)
  | succ k ih => simpa [pow_succ] using ih.mul hr

theorem eval_pow (hr : IsRegularUnitAt x r) (k : ℕ) :
    RatFunc.eval (RingHom.id ℂ) x (r ^ k) = RatFunc.eval (RingHom.id ℂ) x r ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, (hr.pow k).eval_mul hr, ih, pow_succ]

theorem zpow (hr : IsRegularUnitAt x r) (k : ℤ) : IsRegularUnitAt x (r ^ k) := by
  cases k with
  | ofNat k => simpa using hr.pow k
  | negSucc k => simpa [zpow_negSucc] using (hr.pow (k + 1)).inv

theorem eval_zpow (hr : IsRegularUnitAt x r) (k : ℤ) :
    RatFunc.eval (RingHom.id ℂ) x (r ^ k) = RatFunc.eval (RingHom.id ℂ) x r ^ k := by
  cases k with
  | ofNat k => simpa using hr.eval_pow k
  | negSucc k => rw [zpow_negSucc, zpow_negSucc, (hr.pow (k + 1)).eval_inv, hr.eval_pow]

theorem prod {J : Type*} (S : Finset J) {f : J → RatFunc ℂ}
    (hf : ∀ j ∈ S, IsRegularUnitAt x (f j)) : IsRegularUnitAt x (∏ j ∈ S, f j) :=
  Finset.prod_induction f (IsRegularUnitAt x) (fun _ _ ha hb => ha.mul hb) one hf

theorem eval_prod {J : Type*} (S : Finset J) {f : J → RatFunc ℂ}
    (hf : ∀ j ∈ S, IsRegularUnitAt x (f j)) :
    RatFunc.eval (RingHom.id ℂ) x (∏ j ∈ S, f j) =
      ∏ j ∈ S, RatFunc.eval (RingHom.id ℂ) x (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS : ∀ j ∈ S, IsRegularUnitAt x (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      (hf a (Finset.mem_insert_self a S)).eval_mul (prod S hS), ih hS]

end IsRegularUnitAt

theorem isRegularUnitAt_inv_algebraMap {x : ℂ} {P : ℂ[X]} (hP : P.eval x ≠ 0) :
    IsRegularUnitAt x (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ :=
  ⟨1, P, by simp, hP, by rw [map_one, one_div]⟩

theorem eval_inv_algebraMap {x : ℂ} {P : ℂ[X]} (hP : P.eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) x (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ = (P.eval x)⁻¹ := by
  rw [← one_div, ← map_one (algebraMap ℂ[X] (RatFunc ℂ)), eval_algebraMap_div_algebraMap x 1 P hP,
    eval_one, one_div]

/-- Tate's L-factor is the inverse of the value of its Euler polynomial at the spectral
variable; at a pole both sides are `0`. -/
theorem lFactor_eq_inv_eval (K : PadicField.{u} p) (η : QuasiCharacter K) (s : ℂ) :
    LocalFactor.PadicAbelian.lFactor K.canonicalTopologicalData η s =
      ((LocalFactor.PadicAbelian.lPolynomial K.canonicalTopologicalData η).eval
        (LocalFactor.PadicAbelian.spectralVariable K.canonicalTopologicalData s))⁻¹ := by
  classical
  by_cases h : K.canonicalTopologicalData.multiplicativeConductor η = 0 <;>
    simp [LocalFactor.PadicAbelian.lPolynomial, LocalFactor.PadicAbelian.lFactor,
      LocalFactor.PadicAbelian.lFactorAt, h]

theorem eval_lPolynomial_ne_zero {K : PadicField.{u} p} {η : QuasiCharacter K} {s : ℂ}
    (hs : LocalFactor.PadicAbelian.lFactor K.canonicalTopologicalData η s ≠ 0) :
    (LocalFactor.PadicAbelian.lPolynomial K.canonicalTopologicalData η).eval
      (LocalFactor.PadicAbelian.spectralVariable K.canonicalTopologicalData s) ≠ 0 := by
  intro h
  apply hs
  rw [lFactor_eq_inv_eval, h, inv_zero]

/-- The spectral point `q_F^{-s}` of the target's local factors is Tate's spectral variable. -/
theorem spectralPoint_eq_spectralVariable (s : ℂ) :
    spectralPoint F.canonicalTopologicalData.residueCardinality s =
      LocalFactor.PadicAbelian.spectralVariable F.canonicalTopologicalData s :=
  GodementJacquet.Padic.tate_spectralPoint_eq F s

variable {F}

/-- At a point where Tate's L-factor of `η` is finite, the L-factor of the Weil character
`η ∘ e` is regular and nonzero at `q_F^{-s}`. -/
theorem isRegularUnitAt_characterLFactor_weilCharacter
    {e : LocalFactor.RankOne.ReciprocityCandidate F} (he : IsGeometricReciprocity F e)
    (η : QuasiCharacter F) {s : ℂ}
    (hs : LocalFactor.PadicAbelian.lFactor F.canonicalTopologicalData η s ≠ 0) :
    IsRegularUnitAt (spectralPoint F.canonicalTopologicalData.residueCardinality s)
      (characterLFactor F (LocalFactor.RankOne.weilCharacter F e η)) := by
  rw [characterLFactor, characterEulerPolynomial_weilCharacter F he η,
    spectralPoint_eq_spectralVariable]
  exact isRegularUnitAt_inv_algebraMap (eval_lPolynomial_ne_zero hs)

/-- At a point where Tate's L-factor of `η` is finite, the L-factor of `η ∘ e` evaluated at
`q_F^{-s}` is Tate's L-factor `L(s, η)`. -/
theorem eval_characterLFactor_weilCharacter
    {e : LocalFactor.RankOne.ReciprocityCandidate F} (he : IsGeometricReciprocity F e)
    (η : QuasiCharacter F) {s : ℂ}
    (hs : LocalFactor.PadicAbelian.lFactor F.canonicalTopologicalData η s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s)
        (characterLFactor F (LocalFactor.RankOne.weilCharacter F e η)) =
      LocalFactor.PadicAbelian.lFactor F.canonicalTopologicalData η s := by
  rw [characterLFactor, characterEulerPolynomial_weilCharacter F he η,
    spectralPoint_eq_spectralVariable, eval_inv_algebraMap (eval_lPolynomial_ne_zero hs),
    lFactor_eq_inv_eval]

theorem eval_expand_lPolynomial (E : PadicField.{u} p) (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (η : QuasiCharacter E) (s : ℂ) :
    (expand ℂ (extensionResidueDegree F E g)
        (LocalFactor.PadicAbelian.lPolynomial E.canonicalTopologicalData η)).eval
        (spectralPoint F.canonicalTopologicalData.residueCardinality s) =
      (LocalFactor.PadicAbelian.lPolynomial E.canonicalTopologicalData η).eval
        (LocalFactor.PadicAbelian.spectralVariable E.canonicalTopologicalData s) := by
  rw [spectralPoint_eq_spectralVariable]
  exact extensionExpandedPolynomial_eval F E g _ s

/-- At a point where Tate's L-factor of `η` over `E` is finite, the L-factor over `F` of the
representation induced from `η ∘ e` is regular and nonzero at `q_F^{-s}`. -/
theorem isRegularUnitAt_inducedLFactor_weilCharacter (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) {e : LocalFactor.RankOne.ReciprocityCandidate E}
    (he : IsGeometricReciprocity E e) (η : QuasiCharacter E) {s : ℂ}
    (hs : LocalFactor.PadicAbelian.lFactor E.canonicalTopologicalData η s ≠ 0) :
    IsRegularUnitAt (spectralPoint F.canonicalTopologicalData.residueCardinality s)
      (inducedLFactor F E g (LocalFactor.RankOne.weilCharacter E e η)) := by
  rw [inducedLFactor_weilCharacter F E g he η]
  apply isRegularUnitAt_inv_algebraMap
  rw [eval_expand_lPolynomial]
  exact eval_lPolynomial_ne_zero hs

/-- At a point where Tate's L-factor of `η` over `E` is finite, the L-factor over `F` of the
representation induced from `η ∘ e`, evaluated at `q_F^{-s}`, is Tate's `L(s, η)` over `E`. -/
theorem eval_inducedLFactor_weilCharacter (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) {e : LocalFactor.RankOne.ReciprocityCandidate E}
    (he : IsGeometricReciprocity E e) (η : QuasiCharacter E) {s : ℂ}
    (hs : LocalFactor.PadicAbelian.lFactor E.canonicalTopologicalData η s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s)
        (inducedLFactor F E g (LocalFactor.RankOne.weilCharacter E e η)) =
      LocalFactor.PadicAbelian.lFactor E.canonicalTopologicalData η s := by
  have hP := eval_lPolynomial_ne_zero hs
  rw [← eval_expand_lPolynomial E g η s] at hP
  rw [inducedLFactor_weilCharacter F E g he η, eval_inv_algebraMap hP, eval_expand_lPolynomial,
    lFactor_eq_inv_eval]

variable (F)

/-- The rank-one value of a local virtual identity
`[T] = d • [χ₀] + Σ_j n_j • Ind_{E_j}([η_j] - [η'_j])`:
`L(s, χ₀)^d Π_j (L(s, η_j) / L(s, η'_j))^{n_j}`, with Tate's L-factors of `F` and of the
`E_j`. -/
def virtualLValue {J : Type*} [Fintype J] (χ₀ : QuasiCharacter F) (d : ℤ)
    (E : J → PadicField.{u} p) (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ) (s : ℂ) : ℂ :=
  LocalFactor.PadicAbelian.lFactor F.canonicalTopologicalData χ₀ s ^ d *
    ∏ j, (LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η j) s /
      LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η' j) s) ^ n j

open WeilDeligneRepresentation in
/-- Under a local virtual identity whose characters are pulled back along geometric
reciprocity candidates, the arithmetic pair L-factor of the zero-monodromy pairs, evaluated
at `q_F^{-s}`, is `virtualLValue`, at every `s` where the rank-one Tate L-factors are finite. -/
theorem eval_arithmeticPairLFactor_eq_virtualLValue
    (V W : LocalWeilRepresentation.{u, uA} F) (T : LocalWeilRepresentation.{u, max u w} F)
    (hT : T.IsContinuous) (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W))
    {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    {e₀ : LocalFactor.RankOne.ReciprocityCandidate F} (he₀ : IsGeometricReciprocity F e₀)
    {e : ∀ j, LocalFactor.RankOne.ReciprocityCandidate (E j)}
    (he : ∀ j, IsGeometricReciprocity (E j) (e j))
    (χ₀ : QuasiCharacter F) (d : ℤ) (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ)
    (h : ofRepresentation _ ⟨T, hT⟩ =
      d • characterClass.{u, max u w} (LocalFactor.RankOne.weilCharacter F e₀ χ₀) +
      ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j)) -
          characterClass.{u, w} (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))))
    (s : ℂ) (hs₀ : LocalFactor.PadicAbelian.lFactor F.canonicalTopologicalData χ₀ s ≠ 0)
    (hs : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η j) s ≠ 0)
    (hs' : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η' j) s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s)
        (Correspondence.arithmeticPairLFactor F
          (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom V))
          (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom W))) =
      virtualLValue F χ₀ d E η η' n s := by
  rw [arithmeticPairLFactor_eq_of_virtualIdentity F V W T hT eT E g _ _ n _ d h]
  have hr₀ := isRegularUnitAt_characterLFactor_weilCharacter he₀ χ₀ hs₀
  have hr : ∀ j, IsRegularUnitAt (spectralPoint F.canonicalTopologicalData.residueCardinality s)
      (inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j))) :=
    fun j => isRegularUnitAt_inducedLFactor_weilCharacter (E j) (g j) (he j) (η j) (hs j)
  have hr' : ∀ j, IsRegularUnitAt (spectralPoint F.canonicalTopologicalData.residueCardinality s)
      (inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))) :=
    fun j => isRegularUnitAt_inducedLFactor_weilCharacter (E j) (g j) (he j) (η' j) (hs' j)
  have hq : ∀ j, IsRegularUnitAt (spectralPoint F.canonicalTopologicalData.residueCardinality s)
      ((inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j)) /
        inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))) ^
          n j) :=
    fun j => ((hr j).div (hr' j)).zpow (n j)
  rw [(hr₀.zpow d).eval_mul (IsRegularUnitAt.prod Finset.univ fun j _ => hq j),
    hr₀.eval_zpow, IsRegularUnitAt.eval_prod Finset.univ fun j _ => hq j,
    eval_characterLFactor_weilCharacter he₀ χ₀ hs₀, virtualLValue]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [((hr j).div (hr' j)).eval_zpow, (hr j).eval_div (hr' j),
    eval_inducedLFactor_weilCharacter (E j) (g j) (he j) (η j) (hs j),
    eval_inducedLFactor_weilCharacter (E j) (g j) (he j) (η' j) (hs' j)]

theorem weilCharacter_inv' (K : PadicField.{u} p)
    (e : LocalFactor.RankOne.ReciprocityCandidate K) (η : QuasiCharacter K) :
    (LocalFactor.RankOne.weilCharacter K e η)⁻¹ = LocalFactor.RankOne.weilCharacter K e η⁻¹ := by
  ext x
  rfl

open WeilDeligneRepresentation in
/-- The dual form of `eval_arithmeticPairLFactor_eq_virtualLValue`: under the same virtual
identity, the arithmetic pair L-factor of the zero-monodromy pairs of any `Vd ≃ V^∨` and
`Wd ≃ W^∨`, evaluated at `q_F^{-s}`, is `virtualLValue` of the inverse characters. -/
theorem eval_arithmeticPairLFactor_dual_eq_virtualLValue
    (V W : LocalWeilRepresentation.{u, uA} F) (T : LocalWeilRepresentation.{u, max u w} F)
    (hT : T.IsContinuous) (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W))
    (Vd Wd : LocalWeilRepresentation.{u, uA} F)
    (eV : FiniteRepresentation.Equiv Vd (FiniteRepresentation.dual V))
    (eW : FiniteRepresentation.Equiv Wd (FiniteRepresentation.dual W))
    {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    {e₀ : LocalFactor.RankOne.ReciprocityCandidate F} (he₀ : IsGeometricReciprocity F e₀)
    {e : ∀ j, LocalFactor.RankOne.ReciprocityCandidate (E j)}
    (he : ∀ j, IsGeometricReciprocity (E j) (e j))
    (χ₀ : QuasiCharacter F) (d : ℤ) (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ)
    (h : ofRepresentation _ ⟨T, hT⟩ =
      d • characterClass.{u, max u w} (LocalFactor.RankOne.weilCharacter F e₀ χ₀) +
      ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j)) -
          characterClass.{u, w} (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))))
    (s : ℂ) (hs₀ : LocalFactor.PadicAbelian.lFactor F.canonicalTopologicalData χ₀⁻¹ s ≠ 0)
    (hs : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η j)⁻¹ s ≠ 0)
    (hs' : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η' j)⁻¹ s ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s)
        (Correspondence.arithmeticPairLFactor F
          (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom Vd))
          (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom Wd))) =
      virtualLValue F χ₀⁻¹ d E (fun j => (η j)⁻¹) (fun j => (η' j)⁻¹) n s := by
  have hTd : (FiniteRepresentation.dual T).IsContinuous := (isContinuous_dual_iff T).mpr hT
  let eTd : FiniteRepresentation.Equiv (FiniteRepresentation.dual T)
      (FiniteRepresentation.tensor Vd Wd) :=
    ((FiniteRepresentation.dualEquiv eT).symm.trans
      (FiniteRepresentation.tensorDualEquiv V W).symm).trans
      (FiniteRepresentation.tensorEquiv eV eW).symm
  apply eval_arithmeticPairLFactor_eq_virtualLValue F Vd Wd _ hTd eTd E g he₀ he _ d _ _ n _ s
    hs₀ hs hs'
  have hd := congrArg continuousDual h
  simp only [continuousDual_ofRepresentation, map_add, map_zsmul, map_sum, map_sub,
    continuousDual_continuousInduceAlong, continuousDual_characterClass, weilCharacter_inv'] at hd
  simp only [map_sub]
  exact hd

end Evaluation

end Langlands.Weil.Local.InertiaEuler

namespace Langlands.LocalFactor.PadicAbelian

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

/-- Two realizations of a p-adic field with the same topology and the same valuative relation
are equal; the remaining fields are certificates. -/
theorem topologicalData_ext {T₁ T₂ : F.TopologicalData} (ht : T₁.topology = T₂.topology)
    (hv : T₁.valuativeRel = T₂.valuativeRel) : T₁ = T₂ := by
  cases T₁
  cases T₂
  dsimp only at ht hv
  subst ht hv
  rfl

/-- A quasicharacter for one topology, viewed as a quasicharacter for an equal topology. The
underlying homomorphism is unchanged. -/
def quasicharacterCongr {X : Type*} [Field X] {t₁ t₂ : TopologicalSpace X} (ht : t₁ = t₂)
    (χ : @HarmonicAnalysis.Quasicharacter X _ t₁) : @HarmonicAnalysis.Quasicharacter X _ t₂ :=
  @ContinuousMonoidHom.mk Xˣ ℂˣ _ _ (@Units.instTopologicalSpaceUnits X t₂ _) _
    (@ContinuousMonoidHom.toMonoidHom Xˣ ℂˣ _ _ (@Units.instTopologicalSpaceUnits X t₁ _) _ χ)
    (by subst ht; exact χ.2)

/-- A unitary additive character for one topology, viewed as a unitary additive character for
an equal topology. The underlying additive character is unchanged. -/
def unitaryCharacterCongr {X : Type*} [AddGroup X] {t₁ t₂ : TopologicalSpace X} (ht : t₁ = t₂)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter X _ t₁) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter X _ t₂ :=
  @HarmonicAnalysis.UnitaryAdditiveCharacter.mk X _ t₂
    (@HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar X _ t₁ ψ) (by subst ht; exact ψ.2)
    (@HarmonicAnalysis.UnitaryAdditiveCharacter.nontrivial X _ t₁ ψ)

/-- An additive Haar measure for one topology, viewed as an additive Haar measure for an
equal topology and its Borel measurable space. -/
def haarMeasureCongr {X : Type*} [AddGroup X] {t₁ t₂ : TopologicalSpace X} (ht : t₁ = t₂)
    (μ : @HarmonicAnalysis.AdditiveHaarMeasure X _ t₁ (@borel X t₁)) :
    @HarmonicAnalysis.AdditiveHaarMeasure X _ t₂ (@borel X t₂) := by
  subst ht
  exact μ

/-- Tate's L-factor is unchanged when the realization is replaced by an equal one and the
quasicharacter is transported along the equality of topologies. -/
theorem lFactor_quasicharacterCongr {T₁ T₂ : F.TopologicalData} (hT : T₁ = T₂)
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T₁.topology) (s : ℂ) :
    lFactor T₂ (quasicharacterCongr (congrArg PadicField.TopologicalData.topology hT) χ) s =
      lFactor T₁ χ s := by
  subst hT
  rfl

/-- Tate's fixed-Haar epsilon factor is unchanged when the realization is replaced by an equal
one and the quasicharacter and Haar measure are transported along the equality of topologies;
the additive character only has to have the same underlying additive character. -/
theorem epsilon_quasicharacterCongr {T₁ T₂ : F.TopologicalData} (hT : T₁ = T₂)
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T₁.topology)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T₁.topology)
    (ψ' : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T₂.topology)
    (hψ : @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar F.Carrier _ T₂.topology ψ' =
      @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar F.Carrier _ T₁.topology ψ)
    (μ : @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T₁.topology (@borel _ T₁.topology))
    (s : ℂ) :
    epsilon T₂ (quasicharacterCongr (congrArg PadicField.TopologicalData.topology hT) χ) ψ'
        (@HarmonicAnalysis.AdditiveHaarMeasure.measure F.Carrier _ T₂.topology
          (@borel _ T₂.topology)
          (haarMeasureCongr (congrArg PadicField.TopologicalData.topology hT) μ)) s =
      epsilon T₁ χ ψ
        (@HarmonicAnalysis.AdditiveHaarMeasure.measure F.Carrier _ T₁.topology
          (@borel _ T₁.topology) μ) s := by
  subst hT
  obtain ⟨ψ₀, _, _⟩ := ψ'
  subst hψ
  rfl

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.Global.CompletionPadic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open AdelicFunctoriality LocalFactor

section LocalFactorTransport

variable {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The local-field realization of `K_w` with the completion topology is the canonical
realization of its p-adic package. -/
theorem topologicalData_eq_canonicalTopologicalData :
    topologicalData w = (padicField w).canonicalTopologicalData :=
  PadicAbelian.topologicalData_ext (completion_topology_eq w) rfl

variable {p : ℕ} [Fact p.Prime] (h : residuePrime w = p)

/-- The completion topology is the canonical topology of the package at an equal prime. -/
theorem padicFieldAt_topology_eq :
    (topologicalData w).topology = (padicFieldAt w h).canonicalTopologicalData.topology := by
  subst h
  exact completion_topology_eq w

/-- A character of `K_wˣ`, continuous for the completion topology, as a quasicharacter of the
canonical package at an equal prime. -/
def quasicharacterAt (χ : (w.adicCompletion K)ˣ →ₜ* ℂˣ) :
    Correspondence.QuasiCharacter (padicFieldAt w h) :=
  PadicAbelian.quasicharacterCongr (padicFieldAt_topology_eq w h) χ

theorem quasicharacterAt_toMonoidHom (χ : (w.adicCompletion K)ˣ →ₜ* ℂˣ) :
    @ContinuousMonoidHom.toMonoidHom _ _ _ _
        (@Units.instTopologicalSpaceUnits _ (padicFieldAt w h).canonicalTopologicalData.topology _) _
        (quasicharacterAt w h χ) = χ.toMonoidHom :=
  rfl

theorem quasicharacterAt_inv (χ : (w.adicCompletion K)ˣ →ₜ* ℂˣ) :
    (quasicharacterAt w h χ)⁻¹ = quasicharacterAt w h χ⁻¹ :=
  rfl

/-- An additive character of `K_w`, continuous for the completion topology, as a nontrivial
additive character of the canonical package at an equal prime. -/
def additiveCharacterAt
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter (w.adicCompletion K) _
      (topologicalData w).topology) :
    Correspondence.NontrivialAdditiveCharacter (padicFieldAt w h) :=
  PadicAbelian.unitaryCharacterCongr (padicFieldAt_topology_eq w h) ψ

theorem additiveCharacterAt_toAddChar
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter (w.adicCompletion K) _
      (topologicalData w).topology) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
        (padicFieldAt w h).canonicalTopologicalData.topology (additiveCharacterAt w h ψ) =
      ψ.toAddChar :=
  rfl

/-- An additive Haar measure of `K_w` for the completion topology, as an additive Haar measure
of the canonical package at an equal prime. -/
def haarMeasureAt
    (μ : @HarmonicAnalysis.AdditiveHaarMeasure (w.adicCompletion K) _
      (topologicalData w).topology (@borel _ (topologicalData w).topology)) :
    Correspondence.LocalAdditiveHaarMeasure (padicFieldAt w h) :=
  PadicAbelian.haarMeasureCongr (padicFieldAt_topology_eq w h) μ

/-- The canonical realization at an equal prime has the residue cardinality of the completion
realization. -/
theorem residueCardinality_padicFieldAt :
    (padicFieldAt w h).canonicalTopologicalData.residueCardinality =
      (topologicalData w).residueCardinality := by
  subst h
  exact congrArg PadicField.TopologicalData.residueCardinality
    (topologicalData_eq_canonicalTopologicalData w).symm

/-- Tate's L-factor of `χ` for the completion realization of `K_w` is Tate's L-factor of the
transported quasicharacter for the canonical package at an equal prime. -/
theorem lFactor_quasicharacterAt (χ : (w.adicCompletion K)ˣ →ₜ* ℂˣ) (s : ℂ) :
    PadicAbelian.lFactor (padicFieldAt w h).canonicalTopologicalData (quasicharacterAt w h χ) s =
      PadicAbelian.lFactor (topologicalData w) χ s := by
  subst h
  exact PadicAbelian.lFactor_quasicharacterCongr (topologicalData_eq_canonicalTopologicalData w)
    χ s

/-- Tate's fixed-Haar epsilon factor for the completion realization of `K_w` is the epsilon
factor of the transported quasicharacter and Haar measure for the canonical package at an
equal prime; the additive character only has to have the same underlying additive
character. -/
theorem epsilon_quasicharacterAt (χ : (w.adicCompletion K)ˣ →ₜ* ℂˣ)
    (ψE : Correspondence.NontrivialAdditiveCharacter (padicFieldAt w h))
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter (w.adicCompletion K) _
      (topologicalData w).topology)
    (hψ : @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
      (padicFieldAt w h).canonicalTopologicalData.topology ψE = ψ.toAddChar)
    (μ : @HarmonicAnalysis.AdditiveHaarMeasure (w.adicCompletion K) _
      (topologicalData w).topology (@borel _ (topologicalData w).topology)) (s : ℂ) :
    PadicAbelian.epsilon (padicFieldAt w h).canonicalTopologicalData (quasicharacterAt w h χ) ψE
        (@HarmonicAnalysis.AdditiveHaarMeasure.measure _ _
          (padicFieldAt w h).canonicalTopologicalData.topology
          (@borel _ (padicFieldAt w h).canonicalTopologicalData.topology)
          (haarMeasureAt w h μ)) s =
      letI := (topologicalData w).topology
      letI : MeasurableSpace (padicField w).Carrier := borel _
      PadicAbelian.epsilon (topologicalData w) χ ψ μ.measure s := by
  subst h
  exact PadicAbelian.epsilon_quasicharacterCongr (topologicalData_eq_canonicalTopologicalData w)
    χ ψ ψE hψ μ s

end LocalFactorTransport

section TraceTransport

open ClassField.Global.RelativeWeilGroup

variable {F K : Type u} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The trace character of the standalone tower extension `K_w / F_v`, for the transported
base character, is the base character composed with the local trace of the completions. -/
theorem standaloneTraceCharacter_additiveCharacterAt
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter (v.adicCompletion F) _
      (topologicalData v).topology) (x : w.adicCompletion K) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
        (towerPadicField v w).canonicalTopologicalData.topology
        (Weil.Local.SystemEpsilon.standaloneTraceCharacter (padicField v) (towerPadicField v w)
          (completionPadicAlgHom v w) (additiveCharacterAt v rfl ψ)) x =
      ψ.toAddChar (FiniteExtension.localTrace v w x) :=
  rfl

end TraceTransport

end Langlands.Global.CompletionPadic
