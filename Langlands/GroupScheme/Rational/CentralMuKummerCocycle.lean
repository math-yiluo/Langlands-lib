import Langlands.GroupScheme.Rational.CentralMuCocycleLift
import Langlands.GroupScheme.Rational.KummerCocycleUnits

/-! # Natural Kummer cocycles with values in an actual central kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped IntermediateField CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (hf : IsCentralIsogeny f)
  (n : ℕ) (e : kernel f ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)

local notation "χ" => (Iso.hom e ≫ Additive.toMul (mu.incl (Spec (CommRingCat.of F)) n))

/-- The roots-of-unity inclusion detects all kernel coefficients. -/
theorem kernelUnitMap_mu_injective : Function.Injective (hf.kernelUnitMap (χ) E) := by
  intro x y hxy
  apply (hf.kernelRootsEquiv n e E).injective
  apply Subtype.ext
  simpa only [hf.kernelRootsEquiv_val] using hxy

/-- The correcting kernel coefficient has the given root of unity as its unit coordinate. -/
theorem kernelUnitMap_kernelRootsEquiv_symm (t : rootsOfUnity n E) :
    hf.kernelUnitMap (χ) E ((hf.kernelRootsEquiv n e E).symm t) = (t : Eˣ) := by
  rw [← hf.kernelRootsEquiv_val, MulEquiv.apply_symm_apply]

variable [FiniteDimensional F E] [IsGalois F E]

/-- Form the natural cocycle of a global Kummer radical, with coefficients in the actual
kernel of the isogeny. -/
def kummerKernelCocycle (a : Fˣ) {z : Eˣ} (hz : z ^ n = Units.map (algebraMap F E) a) :
    Cocycle (kernel f) (GaloisCocycle.cover F E) := by
  let d (σ : E ≃ₐ[F] E) : GaloisCocycle.cover F E ⟶ (kernel f).X :=
    (hf.kernelRootsEquiv n e E).symm (KummerCocycle.rootValue n a hz σ)
  have hd (σ : E ≃ₐ[F] E) : hf.kernelUnitMap (χ) E (d σ) = KummerCocycle.value z σ :=
    hf.kernelUnitMap_kernelRootsEquiv_symm n e _
  refine GaloisCocycle.ofValues d (fun σ τ => ?_)
  apply hf.kernelUnitMap_mu_injective n e
  have hσ : hf.kernelUnitMap (χ) E (GaloisPoint.conjugate F E (kernel f) σ (d τ)) =
      σ • hf.kernelUnitMap (χ) E (d τ) :=
    hf.kernelUnitMap_naturality (χ) σ.toAlgHom (d τ)
  rw [map_mul, hσ, hd, hd, hd, mul_comm]
  exact KummerCocycle.value_isMulCocycle z σ τ

/-- The actual values of the Kummer kernel cocycle have the prescribed unit coordinates. -/
theorem kernelUnitMap_value_kummerKernelCocycle (a : Fˣ) {z : Eˣ}
    (hz : z ^ n = Units.map (algebraMap F E) a) (σ : E ≃ₐ[F] E) :
    hf.kernelUnitMap (χ) E (GaloisCocycle.value (hf.kummerKernelCocycle n e a hz) σ) =
      KummerCocycle.value z σ := by
  unfold kummerKernelCocycle
  rw [GaloisCocycle.value_ofValues]
  exact hf.kernelUnitMap_kernelRootsEquiv_symm n e _

end Langlands.GroupScheme.IsCentralIsogeny

namespace Langlands.GroupScheme.KummerCocycle

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [CharZero F]

/-- A unit of the base has an `n`-th root after a finite Galois refinement of a
given finite covering field, in characteristic zero. -/
theorem exists_unit_radical_in_finiteGalois_refinement (n : ℕ) (hn : 0 < n) (a : Fˣ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E) (z : Eˣ),
      z ^ n = Units.map (algebraMap F E) a := by
  let Ω := AlgebraicClosure L
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (a : F)) hn
  let D := L⟮r⟯
  let r₀ : D := ⟨r, IntermediateField.mem_adjoin_simple_self L r⟩
  let : FiniteDimensional L D := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := L) r)
  let : FiniteDimensional F D := FiniteDimensional.trans F L D
  have hr₀ : r₀ ^ n = algebraMap F D (a : F) := by
    apply Subtype.ext
    change r ^ n = algebraMap L Ω (algebraMap F L (a : F))
    rw [← IsScalarTower.algebraMap_apply F L Ω, hr]
  obtain ⟨E, hd, hg, ⟨φ⟩⟩ := exists_finite_galois_algHom F D
  let i := φ.comp (IsScalarTower.toAlgHom F L D)
  let : Algebra L E := i.toRingHom.toAlgebra
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => (i.commutes x).symm
  have hz : (φ r₀) ^ n = algebraMap F E (a : F) := by rw [← map_pow, hr₀, φ.commutes]
  have hz₀ : φ r₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hz
    exact a.ne_zero ((algebraMap F E).injective (hz.symm.trans (map_zero _).symm))
  exact ⟨E, inferInstance, inferInstance, hd, hg, inferInstance, inferInstance,
    Units.mk0 (φ r₀) hz₀, Units.ext hz⟩

end Langlands.GroupScheme.KummerCocycle
