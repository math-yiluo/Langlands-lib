import Langlands.Algebra.CentralSimpleTensor
import Langlands.Algebra.UnitaryInvolutionStatements
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-! # Unitary involutions in the universe of the base field -/

noncomputable section

universe u v

namespace Langlands.UnitaryDiscriminant

open _root_.Algebra

variable (F : Type u) {K : Type v} [Field F] [Field K] [Algebra F K]

/-- A central simple algebra with its center presented in the base field's universe. -/
structure BaseUniversePair (A : CSA.{v, v} K) where
  (center : Type u)
  [centerField : Field center]
  [baseAlgebra : Algebra F center]
  algebra : CSA.{u, u} center
  centerEquiv : center ≃ₐ[F] K
  algebraEquiv : algebra ≃+* A
  scalar_eq (x : center) : algebraEquiv (algebraMap center algebra x) =
    algebraMap K A (centerEquiv x)

attribute [instance] BaseUniversePair.centerField BaseUniversePair.baseAlgebra

variable {F} {A : CSA.{v, v} K}

namespace BaseUniversePair

variable (R : BaseUniversePair F A)

/-- Present the supplied finite extension and central simple algebra in the base universe. -/
def ofFinite [FiniteDimensional F K] (A : CSA.{v, v} K) : BaseUniversePair F A := by
  let : Algebra F A := Algebra.compHom A (algebraMap F K)
  let : IsScalarTower F K A := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite F A := Module.Finite.trans K A
  let : Small.{u} K := Module.Finite.small F K
  let : Small.{u} A := Module.Finite.small F A
  let L := Shrink.{u} K
  let B := Shrink.{u} A
  let i : L ≃ₐ[F] K := Shrink.algEquiv F K
  let : Algebra L A := Algebra.compHom A i.toRingHom
  let e : B ≃ₐ[L] A := Shrink.algEquiv L A
  have he (x : L) : e (algebraMap L B x) = algebraMap K A (i x) := e.commutes x
  have hdim : Module.finrank L B = Module.finrank K A :=
    Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv e.toRingEquiv (RingHom.ext fun x => (he x).symm)
  let : Module.Finite L B := Module.finite_of_finrank_pos (hdim ▸ Module.finrank_pos)
  let : IsSimpleRing B := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
  let : Algebra.IsCentral L B := ⟨fun b hb => by
    have hb' : e b ∈ Subalgebra.center K A := (MulEquivClass.apply_mem_center_iff e).mpr hb
    obtain ⟨x, hx⟩ := (Algebra.IsCentral.mem_center_iff K).mp hb'
    rw [Algebra.mem_bot]
    refine ⟨i.symm x, e.injective ?_⟩
    rw [he, i.apply_symm_apply]
    exact hx.symm⟩
  exact ⟨L, ⟨AlgCat.of L B⟩, i, e.toRingEquiv, he⟩

/-- The relabeled center has the same degree over the given base. -/
theorem center_finrank :
    Module.finrank F R.center = Module.finrank F K := R.centerEquiv.toLinearEquiv.finrank_eq

/-- The central simple algebra has the same degree in its relabeled presentation. -/
theorem algebra_finrank : Module.finrank R.center R.algebra = Module.finrank K A :=
  Algebra.finrank_eq_of_equiv_equiv R.centerEquiv.toRingEquiv R.algebraEquiv
    (RingHom.ext fun x => (R.scalar_eq x).symm)

/-- Transport an automorphism of the given center to its presentation. -/
def centerAutomorphism (ι : K ≃ₐ[F] K) : R.center ≃ₐ[F] R.center :=
  R.centerEquiv.trans (ι.trans R.centerEquiv.symm)

@[simp] theorem centerAutomorphism_equiv (ι : K ≃ₐ[F] K) (x : R.center) :
    R.centerEquiv (R.centerAutomorphism ι x) = ι (R.centerEquiv x) :=
  R.centerEquiv.apply_symm_apply _

theorem centerAutomorphism_ne_one {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) :
    R.centerAutomorphism ι ≠ 1 := by
  intro h
  apply hι
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := R.centerEquiv.surjective x
  rw [← R.centerAutomorphism_equiv, h]
  rfl

/-- Transport an involution to the presented algebra. -/
def involution (τ : A → A) (x : R.algebra) : R.algebra :=
  R.algebraEquiv.symm (τ (R.algebraEquiv x))

@[simp] theorem involution_equiv (τ : A → A) (x : R.algebra) :
    R.algebraEquiv (R.involution τ x) = τ (R.algebraEquiv x) :=
  R.algebraEquiv.apply_symm_apply _

theorem isUnitaryInvolution {ι : K ≃ₐ[F] K} {τ : A → A} (hτ : IsUnitaryInvolution ι τ) :
    IsUnitaryInvolution (R.centerAutomorphism ι) (R.involution τ) := by
  refine ⟨fun x y => R.algebraEquiv.injective ?_, fun x y => R.algebraEquiv.injective ?_,
    fun x => R.algebraEquiv.injective ?_, fun x => R.algebraEquiv.injective ?_⟩
  · simp only [involution_equiv, map_add, hτ.1]
  · simp only [involution_equiv, map_mul, hτ.2.1]
  · simp only [involution_equiv, hτ.2.2.1]
  · simp only [involution_equiv, scalar_eq, centerAutomorphism_equiv, hτ.2.2.2]

end BaseUniversePair

end Langlands.UnitaryDiscriminant
