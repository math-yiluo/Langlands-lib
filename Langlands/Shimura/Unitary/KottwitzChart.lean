import Langlands.Shimura.Unitary.CMData
import Langlands.Shimura.Unitary.Adelic
import Langlands.Shimura.Unitary.PlaceTensorDecomposition
import Langlands.Shimura.Unitary.PointsSplit

/-! # Kottwitz's good primes: standard unramified charts and hyperspecial levels -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct

set_option linter.unusedSectionVars false

universe u v w

namespace Langlands.Shimura.KottwitzUnramified

open Langlands.Global.AdelicFunctoriality

section Places

variable (E : Type u) (K : Type v)
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]

/-- The CM conjugation restricted to the ring of integers. -/
def integerConjugation : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (cmConjugation E K).toRingEquiv

variable {E K}

omit [NumberField E] in
theorem integerConjugation_algebraMap (x : 𝓞 ℚ) :
    integerConjugation E K (algebraMap (𝓞 ℚ) (𝓞 K) x) = algebraMap (𝓞 ℚ) (𝓞 K) x := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have h := map_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x)
      rw [Int.cast_id, RingEquiv.symm_apply_apply] at h
      exact h.symm⟩
  rw [map_intCast, map_intCast]

variable (p : HeightOneSpectrum (𝓞 ℚ))

/-- The conjugate `w̄ = c⁻¹(w)` of a place above `p`: the prime of elements whose
conjugate lies in `w`. -/
def placeConj (w : FinitePlacesAbove K p) : FinitePlacesAbove K p :=
  ⟨HeightOneSpectrum.comap (integerConjugation E K).toRingHom
      (fun y => (integerConjugation E K).surjective y) w.1, ⟨by
    have h : p.asIdeal = w.1.asIdeal.under (𝓞 ℚ) := w.2.over
    ext x
    refine (SetLike.ext_iff.mp h x).trans ?_
    simp only [Ideal.under, Ideal.mem_comap]
    change _ ↔ integerConjugation E K (algebraMap (𝓞 ℚ) (𝓞 K) x) ∈ w.1.asIdeal
    rw [integerConjugation_algebraMap]⟩⟩

omit [NumberField E] in
theorem integerConjugation_involutive (x : 𝓞 K) :
    integerConjugation E K (integerConjugation E K x) = x := by
  apply RingOfIntegers.ext
  exact cmConjugation_involutive E K (x : K)

omit [NumberField E] in
@[simp] theorem mem_placeConj (w : FinitePlacesAbove K p) (x : 𝓞 K) :
    x ∈ (placeConj (E := E) p w).1.asIdeal ↔ integerConjugation E K x ∈ w.1.asIdeal :=
  Iff.rfl

omit [NumberField E] in
/-- Conjugation of places is an involution. -/
@[simp] theorem placeConj_placeConj (w : FinitePlacesAbove K p) :
    placeConj (E := E) p (placeConj (E := E) p w) = w := by
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_placeConj, mem_placeConj, integerConjugation_involutive]

/-- Kottwitz's first condition requires the CM field to be unramified at `p`.
The ramification index is Mathlib's index of each actual place above `p`. -/
def IsUnramifiedAt (K : Type v) [Field K] [NumberField K] : Prop :=
  ∀ w : FinitePlacesAbove K p, w.1.asIdeal.ramificationIdx (𝓞 ℚ) = 1

end Places

section Chart

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
variable [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
variable (σ : SecondKindInvolution E K A) (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)

variable (K) in
/-- The product `Π_{w ∣ p} M_n(K_w)` of matrix algebras over the completions of
the CM field at the places above `p`. -/
abbrev MatrixProduct :=
  Π w : FinitePlacesAbove K p, Matrix (Fin n) (Fin n) (w.1.adicCompletion K)

variable (K A) in
/-- A family of `K_w`-algebra isomorphisms `K_w ⊗[K] A ≃ M_n(K_w)`, one at each
place `w` of `K` above `p`. -/
abbrev PlaceCharts :=
  ∀ w : FinitePlacesAbove K p,
    (w.1.adicCompletion K ⊗[K] A) ≃ₐ[w.1.adicCompletion K]
      Matrix (Fin n) (Fin n) (w.1.adicCompletion K)

variable {p n}

/-- The ring isomorphism `ℚ_p ⊗[ℚ] A ≃ Π_{w ∣ p} M_n(K_w)` obtained from the
published decomposition over the places above `p` and the charts. -/
def chartEquiv (φ : PlaceCharts K A p n) :
    p.adicCompletion ℚ ⊗[ℚ] A ≃+* MatrixProduct K p n :=
  (PlaceTensor.placeTensorEquiv (K := K) p A).trans
    (RingEquiv.piCongrRight fun w => (φ w).toRingEquiv)

/-- The involution `σ ⊗ 1` of `ℚ_p ⊗[ℚ] A`, transported to the matrix product by
the charts. -/
def transportedInvolution (φ : PlaceCharts K A p n) (x : MatrixProduct K p n) :
    MatrixProduct K p n :=
  chartEquiv φ (σ.rationalInvolution.baseChange (p.adicCompletion ℚ)
    ((chartEquiv φ).symm x))

variable (p n)

/-- A standard unramified chart: charts at the places above `p` in which the
transported involution has the standard antidiagonal form
`θ(x)_w = J · c_w(x_{w̄})ᵀ · J`, entrywise
`θ(x)_w k l = c_w (x_{w̄} (rev l) (rev k))`, for ring homomorphisms
`c_w : K_{w̄} → K_w` carrying integers to integers. -/
structure UnramifiedChart where
  charts : PlaceCharts K A p n
  conj : ∀ w : FinitePlacesAbove K p,
    (placeConj (E := E) p w).1.adicCompletion K →+* w.1.adicCompletion K
  conj_integer : ∀ w x, x ∈ (placeConj (E := E) p w).1.adicCompletionIntegers K →
    conj w x ∈ w.1.adicCompletionIntegers K
  involution_eq : ∀ (x : MatrixProduct K p n) (w : FinitePlacesAbove K p) (k l : Fin n),
    transportedInvolution σ charts x w k l =
      conj w (x (placeConj (E := E) p w) (Fin.rev l) (Fin.rev k))

section Points

variable {σ p n}

variable (σ p) in
/-- The local group `G(ℚ_p)`: the published similitude points over the completion. -/
abbrev LocalPoints := σ.rationalInvolution.Points (p.adicCompletion ℚ)

/-- The underlying unit of a point, in the matrix coordinates of the charts. -/
def pointUnit (φ : PlaceCharts K A p n) : LocalPoints σ p →* (MatrixProduct K p n)ˣ :=
  (Units.map (chartEquiv φ).toMonoidHom).comp
    (σ.rationalInvolution.baseChange (p.adicCompletion ℚ)).underlyingUnit

theorem pointUnit_val (φ : PlaceCharts K A p n) (g : LocalPoints σ p) :
    (pointUnit φ g : MatrixProduct K p n) = chartEquiv φ (g.1.1 : p.adicCompletion ℚ ⊗[ℚ] A) :=
  rfl

variable (K p n) in
/-- The integral matrices `Π_{w ∣ p} M_n(O_w)`. -/
def integralMatrices : Subring (MatrixProduct K p n) where
  carrier := {x | ∀ w k l, x w k l ∈ w.1.adicCompletionIntegers K}
  mul_mem' {x y} hx hy w k l := by
    simp only [Pi.mul_apply, Matrix.mul_apply]
    exact sum_mem fun j _ => mul_mem (hx w k j) (hy w j l)
  one_mem' w k l := by
    simp only [Pi.one_apply, Matrix.one_apply]
    split
    · exact one_mem _
    · exact zero_mem _
  add_mem' {x y} hx hy w k l := add_mem (hx w k l) (hy w k l)
  zero_mem' w k l := zero_mem _
  neg_mem' {x} hx w k l := neg_mem (hx w k l)

theorem mem_integralMatrices (x : MatrixProduct K p n) :
    x ∈ integralMatrices K p n ↔ ∀ w k l, x w k l ∈ w.1.adicCompletionIntegers K :=
  Iff.rfl

/-- The level `K_p` of a chart: the points whose matrix coordinates and those of
their inverses are integral, that is, `Ψ(g) ∈ Π_w GL_n(O_w)`. -/
def UnramifiedChart.level (c : UnramifiedChart σ p n) : Subgroup (LocalPoints σ p) :=
  (integralMatrices K p n).toSubmonoid.units.comap (pointUnit c.charts)

theorem UnramifiedChart.mem_level (c : UnramifiedChart σ p n) (g : LocalPoints σ p) :
    g ∈ c.level ↔ (pointUnit c.charts g : MatrixProduct K p n) ∈ integralMatrices K p n ∧
      ((pointUnit c.charts g)⁻¹ : (MatrixProduct K p n)ˣ).val ∈ integralMatrices K p n :=
  Iff.rfl

end Points

end Chart

section Conditions

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
variable [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
variable {n : ℕ} (σ : CentralSimpleUnitaryData E K A n) (p : HeightOneSpectrum (𝓞 ℚ))

/-- Kottwitz's condition (a) at the place `p` of `ℚ`: `K` is unramified at `p` and
there is a standard unramified chart. -/
def IsKottwitzUnramifiedAt : Prop :=
  IsUnramifiedAt p K ∧ Nonempty (UnramifiedChart σ.toSecondKindInvolution p n)

/-- Kottwitz's condition (b) for the `p`-component `K_p` of a level: `K_p` is the
level of a standard unramified chart, at a place where `K` is unramified. -/
def IsHyperspecialLevel (Kp : Subgroup (LocalPoints σ.toSecondKindInvolution p)) : Prop :=
  IsUnramifiedAt p K ∧ ∃ c : UnramifiedChart σ.toSecondKindInvolution p n, c.level = Kp

theorem IsHyperspecialLevel.isKottwitzUnramifiedAt
    {Kp : Subgroup (LocalPoints σ.toSecondKindInvolution p)}
    (h : IsHyperspecialLevel σ p Kp) : IsKottwitzUnramifiedAt σ p :=
  ⟨h.1, ⟨h.2.choose⟩⟩

section Global

open Langlands.Global

variable [Module.Finite ℚ A]

/-- Kottwitz's conditions (a) and (b) at a rational prime `ℓ` for a level `Kf` of
`G(𝔸_f)`: at the place `v` of `ℚ` above `ℓ`, the group is unramified in the sense of
`IsKottwitzUnramifiedAt`, and under the published splitting
`G(𝔸_f) ≃ G(Π_{v ∣ ℓ} ℚ_v) × G(𝔸_f^ℓ)` the level is a product `K_ℓ × K^ℓ` whose
`ℓ`-component is a hyperspecial level `K_ℓ` of `G(ℚ_ℓ)`. -/
def IsKottwitzGoodPrime (Kf : Subgroup σ.rationalInvolution.FiniteAdelicPoints)
    (ℓ : ℕ) (hℓ : ℓ.Prime) : Prop :=
  ∃ v : {v : Global.FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal},
    IsKottwitzUnramifiedAt σ v.1 ∧
    ∃ (Kℓ : Subgroup (LocalPoints σ.toSecondKindInvolution v.1))
      (Kaway : Subgroup (σ.rationalInvolution.PrimeToPoints ℓ)),
      IsHyperspecialLevel σ v.1 Kℓ ∧
      Kf.map (σ.rationalInvolution.finiteAdelicPointsSplit ℓ hℓ.ne_zero).toMulEquiv.toMonoidHom =
        (Kℓ.comap (σ.rationalInvolution.dividingLocalMap ℓ v).toMonoidHom).prod Kaway

end Global

end Conditions

end Langlands.Shimura.KottwitzUnramified
