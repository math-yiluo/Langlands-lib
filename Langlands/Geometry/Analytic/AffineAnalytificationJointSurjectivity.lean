import Langlands.Geometry.Analytic.AffineAnalytificationBaseChangeProof
import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.ValuedField.CompleteAlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.FiniteStability

/-! # Analytification of a Spec-surjective family is surjective on points -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set
open scoped TensorProduct

namespace JointSurjectivity

/-- A ring map from `A` to an algebraically closed field extends along a finite type
`A`-algebra `B` when its kernel lies in the image of `Spec B → Spec A`. -/
theorem exists_ringHom_comp_algebraMap {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (g : A →+* Ω)
    (h : ∃ 𝔮 : PrimeSpectrum B, 𝔮.asIdeal.comap (algebraMap A B) = RingHom.ker g) :
    ∃ g' : B →+* Ω, g'.comp (algebraMap A B) = g := by
  classical
  have : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  let 𝔭 : PrimeSpectrum A := ⟨RingHom.ker g, inferInstance⟩
  have hnt : Nontrivial ((RingHom.ker g).ResidueField ⊗[A] B) := by
    rw [PrimeSpectrum.nontrivial_iff_mem_rangeComap 𝔭]
    obtain ⟨𝔮, h𝔮⟩ := h
    exact ⟨𝔮, PrimeSpectrum.ext h𝔮⟩
  let k := (RingHom.ker g).ResidueField
  let gk : k →+* Ω := Ideal.ResidueField.lift (RingHom.ker g) g le_rfl (by
    intro a ha
    exact isUnit_iff_ne_zero.mpr fun h0 => ha (RingHom.mem_ker.mpr h0))
  let : Algebra k Ω := gk.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A] B)
  let := Ideal.Quotient.field m
  have : Module.Finite k ((k ⊗[A] B) ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k ((k ⊗[A] B) ⧸ m)
  let χ : ((k ⊗[A] B) ⧸ m) →ₐ[k] Ω := IsAlgClosed.lift
  refine ⟨(χ.toRingHom.comp (Ideal.Quotient.mk m)).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom, ?_⟩
  ext a
  have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B) (algebraMap A B a) =
      algebraMap k (k ⊗[A] B) (algebraMap A k a) := by
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have h2 : χ (Ideal.Quotient.mk m (algebraMap k (k ⊗[A] B) (algebraMap A k a))) =
      gk (algebraMap A k a) := by
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom]
  rw [h1, h2]
  exact Ideal.ResidueField.lift_algebraMap _ _ _ _ _

end JointSurjectivity

section Points

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- A point of `Spec(A)ᵃⁿ` whose center lies in the image of `Spec B → Spec A` is the image
of a point of `Spec(B)ᵃⁿ`. -/
theorem exists_baseMap_eq (z : Space K P)
    (hz : ∃ 𝔮 : PrimeSpectrum B, PrimeSpectrum.comap f.toRingHom 𝔮 = center K P z) :
    ∃ y : Space K Q, baseMap K P Q f y = z := by
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
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  have : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  obtain ⟨g', hg'⟩ := JointSurjectivity.exists_ringHom_comp_algebraMap g (by
    obtain ⟨𝔮, h𝔮⟩ := hz
    refine ⟨𝔮, ?_⟩
    rw [hker, ← center_asIdeal]
    exact congrArg PrimeSpectrum.asIdeal h𝔮)
  let μ : MulRingSeminorm B :=
    BaseChangeComparison.pullback (NormedField.toMulRingNorm Ω).toMulRingSeminorm g'
  have hμ (b : B) : μ b = ‖g' b‖ := rfl
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
  refine ⟨y, SeminormComparison.pointSeminorm_injective K P ?_⟩
  ext a
  rw [pointSeminorm_baseMap, hy, hμf]

end Points

section Localized

open SaturatedAtlasPresentation

/-- Analytification turns a family of algebra maps out of `A` whose prime spectrum maps are
jointly surjective into a family of localized morphisms that are jointly surjective on
underlying points. This is input 7 of `SpaceAnalytificationExistenceReductionStatement`. -/
theorem exists_mem_range_localizedHom (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) {ι : Type w} {B : ι → Type u}
    [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    (Q : ∀ i, FinitePolynomialPresentation K (B i)) (f : ∀ i, A →ₐ[K] B i)
    (hcov : ∀ 𝔭 : PrimeSpectrum A, ∃ i, ∃ 𝔮 : PrimeSpectrum (B i),
      PrimeSpectrum.comap (f i).toRingHom 𝔮 = 𝔭)
    (z : localizedSpaceFunctor.obj (localized K P)) :
    ∃ i, z ∈ Set.range (localizedSpaceFunctor.map (localizedHom K P (Q i) (f i))) := by
  obtain ⟨i, h⟩ := hcov (center K P z)
  obtain ⟨y, hy⟩ := exists_baseMap_eq K P (Q i) (f i) z h
  refine ⟨i, y, ?_⟩
  rw [localizedSpaceFunctor_map_localizedHom]
  exact hy

end Localized

end Langlands.Analytic.AffineAnalytification
