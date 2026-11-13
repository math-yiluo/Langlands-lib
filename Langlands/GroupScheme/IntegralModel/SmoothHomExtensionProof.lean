import Langlands.GroupScheme.IntegralModel.SmoothHomExtension
import Langlands.GroupScheme.IntegralModel.AffineHomExtension
import Langlands.GroupScheme.IntegralModel.LocalIntegralSeparation
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Mathlib.RingTheory.Localization.BaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj nonZeroDivisors

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.CommutativeAlgebra

private theorem nonempty_algHom_of_smooth
    (k A : Type u) [Field k] [IsSepClosed k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.Smooth k A] : Nonempty (A →ₐ[k] k) := by
  obtain ⟨p⟩ := nonempty_rationalPoint_of_smooth_algebra k (CommRingCat.of A)
  exact ⟨affineRingPointEquiv k A k (rationalPointEquiv k (ringTest k A) p)⟩

private theorem uniformizer_dvd_of_section_values
    (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    {π : R} (hπ : Irreducible π) (a : A)
    (ha : ∀ σ : A →ₐ[R] R, π ∣ σ a) : algebraMap R A π ∣ a := by
  let k := IsLocalRing.ResidueField R
  let B := k ⊗[R] A
  let b : B := 1 ⊗ₜ[R] a
  let I := IsLocalRing.maximalIdeal R
  let J := I.map (algebraMap R A)
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
  have hb : b = 0 := by
    by_contra hb
    have : IsReduced B :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain k B
    let D := Localization.Away b
    have : Nontrivial D := by
      apply not_subsingleton_iff_nontrivial.mp
      intro h
      have hz : (0 : B) ∈ Submonoid.powers b :=
        (IsLocalization.subsingleton_iff (M := Submonoid.powers b) (S := D)).mp h
      obtain ⟨n, hn⟩ := hz
      exact hb (IsNilpotent.eq_zero ⟨n, hn⟩)
    have : Algebra.Smooth k D := Algebra.Smooth.comp k B D
    obtain ⟨φ⟩ := nonempty_algHom_of_smooth k D
    let ψ : A →ₐ[R] k :=
      ((φ.comp (IsScalarTower.toAlgHom k B D)).restrictScalars R).comp
        Algebra.TensorProduct.includeRight
    obtain ⟨σ, hσ⟩ := HenselianSections.exists_lift_of_smooth
      (R := R) (K := k) IsLocalRing.residue_surjective ψ
    have hzπ : algebraMap R k π = 0 := by
      apply (IsLocalRing.residue_eq_zero_iff π).mpr
      rw [hπ.maximalIdeal_eq]
      exact Ideal.subset_span rfl
    have hzero : ψ a = 0 := by
      obtain ⟨r, hr⟩ := ha σ
      have heval := congrArg (fun f : A →ₐ[R] k => f a) hσ
      change algebraMap R k (σ a) = ψ a at heval
      rw [← heval, hr, map_mul, hzπ, zero_mul]
    have hu : IsUnit (ψ a) := by
      change IsUnit (φ (algebraMap B D b))
      exact (IsLocalization.Away.algebraMap_isUnit b).map φ
    exact hu.ne_zero hzero
  have hz : Ideal.Quotient.mk J a = 0 := by
    apply e.injective
    rw [map_zero]
    exact hb
  have hj : J = Ideal.span {algebraMap R A π} := by
    simp only [J, I, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [hj] at hm
  exact Ideal.mem_span_singleton.mp hm

private theorem tensor_mem_range_of_integral_evaluations
    (R K A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (z : K ⊗[R] A)
    (hz : ∀ σ : A →ₐ[R] R,
      AlgHom.liftEquiv R K A K ((Algebra.ofId R K).comp σ) z ∈
        Set.range (algebraMap R K)) :
    z ∈ Set.range (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let T := K ⊗[R] A
  let ev (σ : A →ₐ[R] R) : T →ₐ[R] K :=
    (AlgHom.liftEquiv R K A K ((Algebra.ofId R K).comp σ)).restrictScalars R
  have hπK : algebraMap R K π ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hπ.ne_zero
  have hu : IsUnit (algebraMap R T π) := by
    rw [IsScalarTower.algebraMap_apply R K T]
    exact (isUnit_iff_ne_zero.mpr hπK).map (algebraMap K T)
  have hpow : ∀ n (a : A), (π ^ n) • z = 1 ⊗ₜ[R] a →
      z ∈ Set.range (Algebra.TensorProduct.includeRight : A →ₐ[R] T) := by
    intro n
    induction n with
    | zero =>
        intro a ha
        exact ⟨a, (by simpa using ha.symm)⟩
    | succ n ih =>
        intro a ha
        have hd : algebraMap R A π ∣ a := by
          apply uniformizer_dvd_of_section_values R A hπ a
          intro σ
          obtain ⟨r, hr⟩ := hz σ
          have hev : ev σ (1 ⊗ₜ[R] a) = algebraMap R K (σ a) := by
            change (1 : K) • algebraMap R K (σ a) = _
            exact one_smul K _
          have hσ := congrArg (ev σ) ha
          rw [map_smul, hev] at hσ
          rw [Algebra.smul_def] at hσ
          have hr' : algebraMap R K r = ev σ z := hr
          rw [← hr'] at hσ
          have hval : algebraMap R K (σ a) = algebraMap R K (π * (π ^ n * r)) := by
            simpa only [map_mul, map_pow, pow_succ, mul_assoc, mul_comm,
              mul_left_comm] using hσ.symm
          exact ⟨π ^ n * r, (IsFractionRing.injective R K) hval⟩
        obtain ⟨a', ha'⟩ := hd
        apply ih a'
        apply hu.mul_left_cancel
        change algebraMap R T π * ((π ^ n) • z) =
          algebraMap R T π * (1 ⊗ₜ[R] a')
        rw [← Algebra.smul_def, ← Algebra.smul_def]
        calc
          π • ((π ^ n) • z) = (π ^ (n + 1)) • z := by
            rw [smul_smul, pow_succ, mul_comm]
          _ = 1 ⊗ₜ[R] a := ha
          _ = π • (1 ⊗ₜ[R] a') := by
            rw [ha', ← Algebra.smul_def, TensorProduct.tmul_smul]
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj
    (R⁰) (TensorProduct.mk R K A 1) z
  change (s : R) • z = 1 ⊗ₜ[R] a at hs
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero s.property) hπ
  apply hpow n ((↑(v⁻¹) : R) • a)
  calc
    (π ^ n) • z = (↑(v⁻¹) : R) • ((s : R) • z) := by
      rw [smul_smul, hv, ← mul_assoc]
      simp
    _ = (↑(v⁻¹) : R) • (1 ⊗ₜ[R] a) := by rw [hs]
    _ = 1 ⊗ₜ[R] ((↑(v⁻¹) : R) • a) := (TensorProduct.tmul_smul _ _ _).symm

/-- KP Lemma 2.10.9 over a strictly Henselian discrete valuation ring. -/
theorem genericCoordinate_mem_range_of_integral_values
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]
    (M : IntegralModel R K G) (hM : M.IsSmooth)
    (z : AffineCoordinateRing K G.X)
    (hz : ∀ g ∈ M.integralPoints,
      G.affinePointEvaluation (CommAlgCat.of K K)
        (GaloisPointComparison.rationalCoeffEquiv K G g) z ∈ Set.range (algebraMap R K)) :
    z ∈ Set.range M.genericCoordinate := by
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  have : Smooth M.group.X.hom := hM
  have : IsAffine ((Grp.forget _).obj G).left := inferInstanceAs (IsAffine G.X.left)
  have : IsAffine ((Grp.forget _).obj M.genericFibre).left := by
    change IsAffine (CategoryTheory.Limits.pullback M.group.X.hom (Spec.algebraMap R K))
    infer_instance
  let A := AffineCoordinateRing R M.group.X
  have hsm : Smooth (Spec.algebraMap R A) := by
    rw [affineCoordinateSpecMap]
    infer_instance
  have : Algebra.Smooth R A :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hsm)
  let e : (K ⊗[R] A) ≃ₐ[K] AffineCoordinateRing K G.X :=
    (ringBaseChangeCoordinateAlgEquiv R K M.group.X).trans
      (affineCoordinateAlgEquiv K ((Grp.forget _).mapIso M.genericIso.symm))
  have he (a : A) : e (1 ⊗ₜ[R] a) = M.genericCoordinate a := by
    change (affineCoordinateAlgEquiv K ((Grp.forget _).mapIso M.genericIso.symm))
      (ringBaseChangeCoordinateAlgEquiv R K M.group.X (1 ⊗ₜ[R] a)) = _
    rw [ringBaseChangeCoordinateAlgEquiv_one_tmul]
    rfl
  have ht : e.symm z ∈ Set.range
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) := by
    apply tensor_mem_range_of_integral_evaluations R K A (e.symm z)
    intro σ
    let s : M.integralSections :=
      (rationalPointEquiv R M.group.X).symm
        ((affineSchemePointEquiv R M.group.X R).symm (AlgPoint.ofAlgHom σ))
    let g := M.integralPointMap s
    let p := GaloisPointComparison.rationalCoeffEquiv K G g
    let φ := (affineSchemePointEquiv K G.X K p).toAlgHom
    have hs : affineSchemePointEquiv R M.group.X R
        (rationalPointEquiv R M.group.X s) = AlgPoint.ofAlgHom σ := by
      simp only [s, Equiv.apply_symm_apply]
    have hev : φ.comp e.toAlgHom =
        AlgHom.liftEquiv R K A K ((Algebra.ofId R K).comp σ) := by
      apply (AlgHom.liftEquiv R K A K).symm.injective
      rw [Equiv.symm_apply_apply]
      ext a
      change φ (e (1 ⊗ₜ[R] a)) = algebraMap R K (σ a)
      rw [he]
      change affineSchemePointEquiv K G.X K p (M.genericCoordinate a) = _
      rw [affineSchemePointEquiv_apply_eq_evaluation,
        ← M.genericModelPointEquiv_evaluation K p a]
      change affineSchemePointEquiv R M.group.X K
        (M.genericModelPointEquiv K
          (GaloisPointComparison.rationalCoeffEquiv K G (M.integralPointMap s))) a = _
      rw [genericModelPointEquiv_integralPointMap, affineSchemePointEquiv_changeRing, hs]
      rfl
    rw [← hev, AlgHom.comp_apply]
    change φ (e (e.symm z)) ∈ _
    rw [AlgEquiv.apply_symm_apply]
    change affineSchemePointEquiv K G.X K p z ∈ _
    rw [affineSchemePointEquiv_apply_eq_evaluation]
    exact hz g ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := ht
  refine ⟨a, ?_⟩
  change 1 ⊗ₜ[R] a = e.symm z at ha
  rw [← he, ha, AlgEquiv.apply_symm_apply]

/-- KP Corollary 2.10.10 and Remark 2.10.19 over a strictly Henselian DVR. -/
theorem smoothHomExtension : SmoothHomExtensionStatement.{u} := by
  intro R _ _ _ _ _ K _ _ _ G H f M N hM hf
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  have : IsAffine M.genericFibre.X.left := by
    change IsAffine (CategoryTheory.Limits.pullback M.group.X.hom (Spec.algebraMap R K))
    infer_instance
  have : IsAffine G.X.left := IsAffine.of_isIso M.genericIso.inv.hom.hom.left
  apply nonempty_hom_of_genericCoordinates M N f
  intro b
  apply genericCoordinate_mem_range_of_integral_values M hM
  intro g hg
  have h := (N.mem_integralPoints_iff_genericCoordinates (rationalPoints.map f g)).mp
    (hf g hg) b
  rw [GaloisPointComparison.rationalCoeffEquiv_map, G.affinePointsTarget_apply,
    GroupScheme.affinePointEvaluation_postcomp] at h
  exact h

end Langlands.GroupScheme.IntegralModel
