import Langlands.Geometry.Analytic.AffineAnalytificationJointSurjectivity
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Etale.Basic

/-! # Points of an analytification over a point with a prescribed center

For an étale algebra map `f : A → D`, a point `z` of `Spec(A)ᵃⁿ` and a prime `𝔓` of `D` over
the center of `z`, some point of `Spec(D)ᵃⁿ` maps to `z` and has center `𝔓`. -/

noncomputable section

universe u

namespace Langlands.Analytic.AffineAnalytification

open Set

namespace CenterLift

/-- A ring map from `A` to an algebraically closed field extends along an essentially finite
type formally unramified `A`-algebra `D`, with kernel any prescribed prime of `D` over its
kernel. -/
theorem exists_ringHom_ker_eq {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.EssFiniteType A D] [Algebra.FormallyUnramified A D]
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (g : A →+* Ω) (𝔓 : PrimeSpectrum D)
    (h : 𝔓.asIdeal.comap (algebraMap A D) = RingHom.ker g) :
    ∃ g' : D →+* Ω, g'.comp (algebraMap A D) = g ∧ RingHom.ker g' = 𝔓.asIdeal := by
  classical
  let p := RingHom.ker g
  have : p.IsPrime := RingHom.ker_isPrime g
  let q := 𝔓.asIdeal
  have : q.LiesOver p := ⟨h.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Module.Finite p.ResidueField q.ResidueField := inferInstance
  have : Algebra.IsAlgebraic p.ResidueField q.ResidueField := Algebra.IsAlgebraic.of_finite _ _
  let gk : p.ResidueField →+* Ω := Ideal.ResidueField.lift p g le_rfl (by
    intro a ha
    exact isUnit_iff_ne_zero.mpr fun h0 => ha (RingHom.mem_ker.mpr h0))
  let : Algebra p.ResidueField Ω := gk.toAlgebra
  let χ : q.ResidueField →ₐ[p.ResidueField] Ω := IsAlgClosed.lift
  refine ⟨χ.toRingHom.comp (algebraMap D q.ResidueField), ?_, ?_⟩
  · ext a
    have h1 : algebraMap D q.ResidueField (algebraMap A D a) =
        algebraMap p.ResidueField q.ResidueField (algebraMap A p.ResidueField a) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    rw [h1, AlgHom.commutes]
    change gk (algebraMap A p.ResidueField a) = g a
    exact Ideal.ResidueField.lift_algebraMap _ _ _ _ _
  · ext d
    rw [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, map_eq_zero_iff χ χ.toRingHom.injective,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

end CenterLift

section Points

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A] {D : Type u} [CommRing D] [Algebra K D]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K D)
  (f : A →ₐ[K] D)

/-- For an étale algebra map `f`, a point of `Spec(A)ᵃⁿ` and a prime `𝔓` of `D` over its
center, some point of `Spec(D)ᵃⁿ` with center `𝔓` maps to the given point. -/
theorem exists_baseMap_eq_center (hf : f.toRingHom.Etale) (z : Space K P)
    (𝔓 : PrimeSpectrum D) (h𝔓 : PrimeSpectrum.comap (f : A →+* D) 𝔓 = center K P z) :
    ∃ y : Space K Q, baseMap K P Q f y = z ∧ center K Q y = 𝔓 := by
  classical
  obtain ⟨H, _, _, _, _, f₀, hf₀⟩ :=
    BaseChangeComparison.normedRealization (pointSeminorm K P z)
      (pointSeminorm_extendsNorm K P z)
  let Ω := ValuedField.CompleteAlgebraicClosure H
  let g : A →+* Ω := (algebraMap H Ω).comp f₀.toRingHom
  have hg (a : A) : ‖g a‖ = pointSeminorm K P z a := by
    change ‖algebraMap H Ω (f₀ a)‖ = _
    rw [ValuedField.CompleteAlgebraicClosure.norm_algebraMap, hf₀]
  have hker : RingHom.ker g = kernel K P z := by
    ext a
    rw [RingHom.mem_ker, mem_kernel, ← hg, norm_eq_zero]
  let : Algebra A D := f.toRingHom.toAlgebra
  have : IsScalarTower K A D := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  have : Algebra.FiniteType K D := Algebra.FiniteType.of_surjective Q.map Q.surjective
  have : Algebra.FiniteType A D := Algebra.FiniteType.of_restrictScalars_finiteType K A D
  have : Algebra.Etale A D := (RingHom.etale_algebraMap (R := A) (S := D)).mp hf
  obtain ⟨g', hg', hker'⟩ := CenterLift.exists_ringHom_ker_eq g 𝔓 (by
    rw [hker, ← center_asIdeal, ← h𝔓]
    rfl)
  let μ : MulRingSeminorm D :=
    BaseChangeComparison.pullback (NormedField.toMulRingNorm Ω).toMulRingSeminorm g'
  have hμ (b : D) : μ b = ‖g' b‖ := rfl
  have hμf (a : A) : μ (f a) = pointSeminorm K P z a := by
    rw [hμ, ← hg, ← hg']
    rfl
  have hμK : ExtendsNorm K μ := by
    intro c
    rw [← f.commutes c, hμf]
    exact pointSeminorm_extendsNorm K P z c
  have hmem : μ ∈ Set.range (pointSeminorm K Q) := by
    rw [SeminormComparison.range_pointSeminorm]
    exact hμK
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, SeminormComparison.pointSeminorm_injective K P ?_, ?_⟩
  · ext a
    rw [pointSeminorm_baseMap, hy, hμf]
  · apply PrimeSpectrum.ext
    rw [center_asIdeal, ← hker']
    ext b
    rw [mem_kernel, hy, RingHom.mem_ker, hμ, norm_eq_zero]

end Points

end Langlands.Analytic.AffineAnalytification
