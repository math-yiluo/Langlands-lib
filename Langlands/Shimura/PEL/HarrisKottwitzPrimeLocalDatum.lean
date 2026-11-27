import Langlands.RingTheory.PrimeLocalIntegers
import Langlands.Shimura.PEL.HarrisReflexBase
import Langlands.Shimura.PEL.HarrisIntegralOrder
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Kottwitz's prime-local PEL datum for the Harris trace-pairing input -/

noncomputable section

open scoped TensorProduct
open NumberField

namespace Langlands.PrimeLocalIntegers

variable (p : ℕ) [Fact p.Prime]

/-- A rational algebra is a `ℤ_(p)`-algebra through `ℤ_(p) ⊆ ℚ`. -/
scoped instance algebraOfRat (A : Type*) [Ring A] [Algebra ℚ A] :
    Algebra (PrimeLocalIntegers p) A :=
  RingHom.toAlgebra' ((algebraMap ℚ A).comp (toRat p)) (fun _ x => Algebra.commutes _ x)

theorem algebraMap_eq_rat (A : Type*) [Ring A] [Algebra ℚ A] (r : PrimeLocalIntegers p) :
    algebraMap (PrimeLocalIntegers p) A r = algebraMap ℚ A (toRat p r) := rfl

/-- Scalar multiplication by `ℤ_(p)` on a rational algebra is multiplication by its image in
`ℚ`. -/
theorem smul_eq_toRat_smul {A : Type*} [Ring A] [Algebra ℚ A] (r : PrimeLocalIntegers p)
    (a : A) : r • a = toRat p r • a := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

end Langlands.PrimeLocalIntegers

namespace Langlands.Shimura

variable (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- `𝒪_K ⊗ ℤ_(p)`, realized as Mathlib's localization of the ring of integers `𝒪_K` at the
image of the integers prime to `p`. -/
abbrev PrimeLocalRingOfIntegers : Type :=
  Localization (Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl)

/-- Every element of the inverted submonoid is a unit of `K`. -/
theorem isUnit_algebraMap_of_mem_primeCompl
    (m : Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl) :
    IsUnit (algebraMap (𝓞 K) K m) := by
  obtain ⟨_, ⟨z, hz, rfl⟩⟩ := m
  rw [isUnit_iff_ne_zero, ← IsScalarTower.algebraMap_apply, eq_intCast, Int.cast_ne_zero]
  rintro rfl
  exact hz (Ideal.zero_mem _)

/-- The inclusion `𝒪_K ⊗ ℤ_(p) → K`. -/
def primeLocalRingOfIntegersToField : PrimeLocalRingOfIntegers K p →+* K :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl)
    (g := algebraMap (𝓞 K) K) (isUnit_algebraMap_of_mem_primeCompl K p)

/-- The inclusion `𝒪_K ⊗ ℤ_(p) → K` is injective. -/
theorem primeLocalRingOfIntegersToField_injective :
    Function.Injective (primeLocalRingOfIntegersToField K p) := by
  have hM : Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl ≤
      nonZeroDivisors (𝓞 K) := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    rw [eq_intCast]
    intro h
    apply hz
    have : (z : K) = 0 := by
      have h' := congrArg (algebraMap (𝓞 K) K) h
      rwa [map_intCast, map_zero] at h'
    rw [Int.cast_eq_zero.mp this]
    exact Ideal.zero_mem _
  rw [primeLocalRingOfIntegersToField, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (PrimeLocalRingOfIntegers K p) hM).eq_iff,
    (IsFractionRing.injective (𝓞 K) K).eq_iff]

/-! ## Kottwitz's unramified hypothesis at `p` -/

/-- A finite extension `F` of `ℚ_p` is unramified when the integral closure of `ℤ_p` in `F` is a
formally unramified `ℤ_p`-algebra: `p` generates its maximal ideal (the residue extension, of
finite fields, is separable). -/
def IsUnramifiedPadicExtension (F : Type) [Field F] [Algebra ℚ_[p] F] [Algebra ℤ_[p] F]
    [IsScalarTower ℤ_[p] ℚ_[p] F] : Prop :=
  FiniteDimensional ℚ_[p] F ∧ Algebra.FormallyUnramified ℤ_[p] (integralClosure ℤ_[p] F)

/-- `ℚ_p` is an unramified extension of itself. -/
theorem isUnramifiedPadicExtension_self : IsUnramifiedPadicExtension p ℚ_[p] := by
  refine ⟨inferInstance, ?_⟩
  rw [IsIntegrallyClosed.integralClosure_eq_bot ℤ_[p] ℚ_[p]]
  exact Algebra.FormallyUnramified.of_equiv
    (Algebra.botEquivOfInjective (IsFractionRing.injective ℤ_[p] ℚ_[p])).symm

/-- Kottwitz's hypothesis at `p` on the rational algebra `B` (§5, p. 389): `ℚ_p ⊗[ℚ] B` is
isomorphic, as a `ℚ_p`-algebra, to a finite product of matrix algebras over finite unramified
extensions of `ℚ_p`. -/
def IsUnramifiedMatrixProductAt (B : Type) [Ring B] [Algebra ℚ B] : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (F : ι → Type) (_ : ∀ i, Field (F i))
    (_ : ∀ i, Algebra ℚ_[p] (F i)) (_ : ∀ i, Algebra ℤ_[p] (F i))
    (_ : ∀ i, IsScalarTower ℤ_[p] ℚ_[p] (F i)) (n : ι → ℕ),
    (∀ i, IsUnramifiedPadicExtension p (F i)) ∧
      Nonempty ((ℚ_[p] ⊗[ℚ] B) ≃ₐ[ℚ_[p]] ((i : ι) → Matrix (Fin (n i)) (Fin (n i)) (F i)))

/-- An algebra split at `p`, `ℚ_p ⊗ B ≅ M_m(ℚ_p)`, satisfies the hypothesis. -/
theorem isUnramifiedMatrixProductAt_of_split {B : Type} [Ring B] [Algebra ℚ B] {m : ℕ}
    (e : (ℚ_[p] ⊗[ℚ] B) ≃ₐ[ℚ_[p]] Matrix (Fin m) (Fin m) ℚ_[p]) :
    IsUnramifiedMatrixProductAt p B :=
  ⟨Unit, inferInstance, fun _ => ℚ_[p], fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => m,
    fun _ => isUnramifiedPadicExtension_self p,
    ⟨e.trans
      (AlgEquiv.funUnique (R := ℚ_[p]) (ι := Unit) (S := Matrix (Fin m) (Fin m) ℚ_[p])).symm⟩⟩

end Langlands.Shimura

namespace Langlands.Shimura.CentralSimpleUnitaryData

open Langlands.PrimeLocalIntegers

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [Algebra.IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [Algebra.IsQuadraticExtension ℚ L]
    {j : L →+* K} {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E j τ₀))
    (p : ℕ) [Fact p.Prime]

/-- Kottwitz's prime-local PEL datum for the Harris input `(D, C)` at the prime `p`.

The algebra `B` is `A` with the positive left involution `τ` of `harrisHodgePELAlgebra`; the
module `V` is `A` with left multiplication and the trace form `harrisHodgePELForm`. The datum
consists of the hypothesis that `ℚ_p ⊗ A` is a product of matrix algebras over unramified
extensions of `ℚ_p`, a `ℤ_(p)`-order of `A` with a basis, stable under `τ` and spanning `A`, a
lattice of `ℚ_p ⊗ V` preserved by the order and self-dual for the form, maximality of the
`p`-adic completion of the order, and the integral coefficients of the determinant polynomial of
the reference Hodge eigenspace in the order basis. -/
structure HarrisKottwitzPrimeLocalDatum where
  /-- Kottwitz's hypothesis that `B_{ℚ_p} = ℚ_p ⊗ A` is a product of matrix algebras over finite
  unramified extensions of `ℚ_p`. -/
  unramified : IsUnramifiedMatrixProductAt p A
  /-- The `ℤ_(p)`-order `𝒪_B`. -/
  order : Subalgebra (PrimeLocalIntegers p) A
  /-- The rank of the order. -/
  rank : ℕ
  /-- A basis `α₁, …, α_t` of the free `ℤ_(p)`-module `𝒪_B`. -/
  basis : Module.Basis (Fin rank) (PrimeLocalIntegers p) order
  /-- The order spans `A` over `ℚ`. -/
  span_order : Submodule.span ℚ (order : Set A) = ⊤
  /-- The positive left involution preserves the order. -/
  involution_mem : ∀ a ∈ order, (D.harrisHodgePELAlgebra C).involution a ∈ order
  /-- The lattice `Λ₀` in `ℚ_p ⊗ V`. -/
  lattice : Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] A)
  lattice_fg : lattice.FG
  lattice_span : Submodule.span ℚ_[p] (lattice : Set (ℚ_[p] ⊗[ℚ] A)) = ⊤
  /-- The order preserves the lattice. -/
  order_mul_mem_lattice :
    ∀ a ∈ order, ∀ x ∈ lattice, ((1 : ℚ_[p]) ⊗ₜ[ℚ] a) * x ∈ lattice
  /-- The lattice is self-dual for the trace form extended to `ℚ_p`. -/
  lattice_selfDual : ∀ x : ℚ_[p] ⊗[ℚ] A, x ∈ lattice ↔
    ∀ y ∈ lattice, D.harrisHodgePELFormBaseChange C ℚ_[p] x y ∈ (algebraMap ℤ_[p] ℚ_[p]).range
  /-- The `p`-adic completion of the order is a maximal order: every finitely generated
  `ℤ_p`-subalgebra of `ℚ_p ⊗ A` containing the order lies in its `ℤ_p`-span. -/
  order_maximal : ∀ O' : Subalgebra ℤ_[p] (ℚ_[p] ⊗[ℚ] A),
    (∀ a ∈ order, (1 : ℚ_[p]) ⊗ₜ[ℚ] a ∈ O') → O'.toSubmodule.FG →
      ∀ x ∈ O', x ∈ Submodule.span ℤ_[p]
        ((fun a : A => (1 : ℚ_[p]) ⊗ₜ[ℚ] a) '' (order : Set A))
  /-- The determinant polynomial `f(X₁, …, X_t)` with coefficients in `𝒪_K ⊗ ℤ_(p)`. -/
  determinant : MvPolynomial (Fin rank) (PrimeLocalRingOfIntegers K p)
  /-- Its image in `K` is the reflex determinant of the order basis transported to `K`. -/
  determinant_map : MvPolynomial.map (primeLocalRingOfIntegersToField K p) determinant =
    D.kottwitzReflexDeterminantBaseChange C (isCMSection_harrisCMSection E j τ₀)
      (fun i => (basis i : A)) (D.harrisReflexToCM C).toRingHom

namespace HarrisKottwitzPrimeLocalDatum

variable {D C p} (Dat : HarrisKottwitzPrimeLocalDatum D C p)

/-- The positive left involution restricted to the order. -/
def orderInvolution (b : Dat.order) : Dat.order :=
  ⟨(D.harrisHodgePELAlgebra C).involution b, Dat.involution_mem b b.2⟩

@[simp] theorem coe_orderInvolution (b : Dat.order) :
    (Dat.orderInvolution b : A) = (D.harrisHodgePELAlgebra C).involution b := rfl

/-- The order acts on `V = A` by left multiplication with adjoint the positive involution. -/
theorem form_left (b : Dat.order) (x y : A) :
    D.harrisHodgePELForm C ((b : A) * x) y =
      D.harrisHodgePELForm C x ((Dat.orderInvolution b : A) * y) :=
  D.harrisHodgePELForm_left C b x y

omit [IsScalarTower ℚ K A] in
/-- Right multiplication, i.e. the action of `C = End_B(V)`, has adjoint the original
Harris involution, which defines the Shimura group. -/
theorem form_right (c x y : A) :
    D.harrisHodgePELForm C (x * c) y = D.harrisHodgePELForm C x (y * D.involution c) :=
  D.harrisHodgePELForm_right C c x y

/-- `ℤ_(p)`-scalars act on elements of the order through `ℚ`. -/
theorem coe_smul (r : PrimeLocalIntegers p) (x : Dat.order) :
    ((r • x : Dat.order) : A) = toRat p r • (x : A) :=
  smul_eq_toRat_smul p r (x : A)

/-- The integral determinant polynomial is determined by its image in `K`. -/
theorem determinant_eq_iff (f : MvPolynomial (Fin Dat.rank) (PrimeLocalRingOfIntegers K p)) :
    f = Dat.determinant ↔ MvPolynomial.map (primeLocalRingOfIntegersToField K p) f =
      D.kottwitzReflexDeterminantBaseChange C (isCMSection_harrisCMSection E j τ₀)
        (fun i => (Dat.basis i : A)) (D.harrisReflexToCM C).toRingHom := by
  rw [← Dat.determinant_map]
  exact ⟨fun h => h ▸ rfl,
    fun h => MvPolynomial.map_injective _ (primeLocalRingOfIntegersToField_injective K p) h⟩

/-- The order basis is linearly independent over `ℚ` in `A`. -/
theorem linearIndependent_rat : LinearIndependent ℚ (fun i => (Dat.basis i : A)) := by
  rw [Fintype.linearIndependent_iff]
  intro q hq i
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ q
  choose z hz using fun k => hb k (Finset.mem_univ k)
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hsum : ∑ k, (z k : PrimeLocalIntegers p) • Dat.basis k = 0 := by
    apply Subtype.val_injective
    have hcoe : ∀ k, ((z k : PrimeLocalIntegers p) • (Dat.basis k : A)) =
        ((b : ℤ) : ℚ) • (q k • (Dat.basis k : A)) := by
      intro k
      rw [smul_eq_toRat_smul, map_intCast, smul_smul]
      congr 1
      have := hz k
      simp only [Algebra.smul_def, eq_intCast] at this
      exact this
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [SetLike.val_smul, hcoe]
    rw [← Finset.smul_sum, hq, smul_zero]
    rfl
  have hzk := Fintype.linearIndependent_iff.mp Dat.basis.linearIndependent _ hsum i
  have hzk' : (z i : ℚ) = 0 := by
    have := congrArg (toRat p) hzk
    rwa [map_intCast, map_zero] at this
  have := hz i
  simp only [Algebra.smul_def, eq_intCast, hzk'] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hb0

/-- The order basis spans `A` over `ℚ`. -/
theorem span_rat : ⊤ ≤ Submodule.span ℚ (Set.range fun i => (Dat.basis i : A)) := by
  rw [← Dat.span_order, Submodule.span_le]
  intro x hx
  have hx'' : (∑ k, ((Dat.basis.repr ⟨x, hx⟩ k • Dat.basis k : Dat.order) : A)) = x := by
    rw [← AddSubmonoidClass.coe_finsetSum, Dat.basis.sum_repr]
  rw [← hx'']
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Dat.coe_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The order basis, as a basis of `A` over `ℚ`. -/
def ratBasis : Module.Basis (Fin Dat.rank) ℚ A :=
  Module.Basis.mk Dat.linearIndependent_rat Dat.span_rat

@[simp] theorem ratBasis_apply (i : Fin Dat.rank) : Dat.ratBasis i = (Dat.basis i : A) :=
  Module.Basis.mk_apply _ _ i

end HarrisKottwitzPrimeLocalDatum

end Langlands.Shimura.CentralSimpleUnitaryData
