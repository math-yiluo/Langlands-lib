import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # An isomorphism criterion for smooth affine schemes over a strictly Henselian DVR -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct nonZeroDivisors

namespace Langlands.GroupScheme.IntegralModel.IntegralPointIsoCriterion

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.CommutativeAlgebra

/-- Over a domain, the generic coordinate inclusion of a flat algebra is injective. -/
theorem includeRight_injective (R K A : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A]
    [Module.Flat R A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) := by
  intro x y h
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    (Algebra.linearMap R K) (IsFractionRing.injective R K)
  apply (TensorProduct.lid R A).symm.injective
  apply hinj
  simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
    map_one]
  exact h

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Integral-point isomorphism criterion.** Over a strictly Henselian discrete
valuation ring `R` with fraction field `K`, let `f : X ⟶ Y` be a morphism of affine
schemes over `Spec R`, with `X` flat and `Y` smooth. If the base change of `f` to
`Spec K` is an isomorphism and every `R`-section of `Y` lifts through `f`, then `f`
is an isomorphism. -/
theorem isIso_of_isIso_baseChange_of_forall_exists_comp_eq
    {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]
    [Flat X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (hK : IsIso ((Over.pullback (Spec.algebraMap R K)).map f))
    (hpts : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Y, ∃ x, x ≫ f = y) :
    IsIso f := by
  let A := AffineCoordinateRing R X
  let B := AffineCoordinateRing R Y
  let φ : B →ₐ[R] A := affineCoordinatePullback R f
  have hsmB : Algebra.Smooth R B := by
    have hsm : Smooth (Spec.algebraMap R B) := by
      rw [affineCoordinateSpecMap]
      infer_instance
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hsm)
  have hflA : Module.Flat R A := by
    have hfl : Flat (Spec.algebraMap R A) := by
      rw [affineCoordinateSpecMap]
      infer_instance
    exact RingHom.flat_algebraMap_iff.mp (HasRingHomProperty.Spec_iff.mp hfl)
  let b := Spec.algebraMap R K
  have : IsAffine ((Over.pullback b).obj X).left := by
    change IsAffine (pullback X.hom b)
    infer_instance
  have : IsAffine ((Over.pullback b).obj Y).left := by
    change IsAffine (pullback Y.hom b)
    infer_instance
  let fK := (Over.pullback b).map f
  let eX := ringBaseChangeCoordinateAlgEquiv R K X
  let eY := ringBaseChangeCoordinateAlgEquiv R K Y
  let ψ : AffineCoordinateRing K ((Over.pullback b).obj Y) →ₐ[K]
      AffineCoordinateRing K ((Over.pullback b).obj X) :=
    affineCoordinatePullback K fK
  have hψ : Function.Bijective ψ := by
    have : IsIso fK := hK
    exact (affineCoordinateAlgEquiv K (asIso fK)).bijective
  let φK : K ⊗[R] B →ₐ[K] K ⊗[R] A := Algebra.TensorProduct.map (AlgHom.id K K) φ
  have hφK_tmul (c : B) : φK (1 ⊗ₜ[R] c) = 1 ⊗ₜ[R] φ c := by
    simp only [φK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hkey (c : B) : eX (φK (1 ⊗ₜ[R] c)) = ψ (eY (1 ⊗ₜ[R] c)) := by
    rw [hφK_tmul]
    change eX (1 ⊗ₜ[R] φ c) = ψ (eY (1 ⊗ₜ[R] c))
    rw [ringBaseChangeCoordinateAlgEquiv_one_tmul, ringBaseChangeCoordinateAlgEquiv_one_tmul]
    change (pullback.fst X.hom b).appTop.hom (f.left.appTop.hom c) =
      fK.left.appTop.hom ((pullback.fst Y.hom b).appTop.hom c)
    have hfst : fK.left ≫ pullback.fst Y.hom b = pullback.fst X.hom b ≫ f.left := by
      simp only [fK, Over.pullback_map_left, pullback.lift_fst]
    have h := congrArg (fun g => g.appTop.hom c) hfst
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h.symm
  have hsq : ∀ w, eX (φK w) = ψ (eY w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul k c =>
      have hkc : k ⊗ₜ[R] c = k • (1 ⊗ₜ[R] c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hkc, map_smul, map_smul, map_smul, map_smul, hkey c]
    | add w w' hw hw' => simp only [map_add, hw, hw']
  have hφK : Function.Bijective φK := by
    refine ⟨fun x y hxy => ?_, fun t => ?_⟩
    · apply eY.injective
      apply hψ.1
      rw [← hsq, ← hsq, hxy]
    · obtain ⟨s, hs⟩ := hψ.2 (eX t)
      obtain ⟨w, hw⟩ := eY.surjective s
      refine ⟨w, eX.injective ?_⟩
      rw [hsq, hw, hs]
  have hincA := includeRight_injective R K A
  have hφ_inj : Function.Injective φ := by
    intro c d hcd
    have : Module.Flat R B := by
      have hfl : Flat (Spec.algebraMap R B) := by
        rw [affineCoordinateSpecMap]
        infer_instance
      exact RingHom.flat_algebraMap_iff.mp (HasRingHomProperty.Spec_iff.mp hfl)
    apply includeRight_injective R K B
    apply hφK.1
    change φK (1 ⊗ₜ[R] c) = φK (1 ⊗ₜ[R] d)
    rw [hφK_tmul, hφK_tmul, hcd]
  have hφ_surj : Function.Surjective φ := by
    intro a
    obtain ⟨z, hz⟩ := hφK.2 (1 ⊗ₜ[R] a)
    have hzR : z ∈ Set.range
        (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B) := by
      apply tensor_mem_range_of_integral_evaluations R K B z
      intro σ
      let y : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Y :=
        (rationalPointEquiv R Y).symm ((affineSchemePointEquiv R Y R).symm (AlgPoint.ofAlgHom σ))
      obtain ⟨x, hx⟩ := hpts y
      let τ : A →ₐ[R] R := (affineSchemePointEquiv R X R (rationalPointEquiv R X x)).toAlgHom
      have hστ : σ = τ.comp φ := by
        have h1 : affineSchemePointEquiv R Y R (rationalPointEquiv R Y y) =
            AlgPoint.ofAlgHom σ := by
          simp only [y, Equiv.apply_symm_apply]
        have h2 : rationalPointEquiv R Y (x ≫ f) = rationalPointEquiv R X x ≫ f := by
          change (ringTestSelfIso R).symm.inv ≫ (x ≫ f) ≫ (Iso.refl Y).hom =
            ((ringTestSelfIso R).symm.inv ≫ x ≫ (Iso.refl X).hom) ≫ f
          simp only [Iso.refl_hom, Category.comp_id, Category.assoc]
        rw [← hx, h2, affineSchemePointEquiv_natural] at h1
        exact h1.symm
      have hev : AlgHom.liftEquiv R K B K ((Algebra.ofId R K).comp σ) =
          (AlgHom.liftEquiv R K A K ((Algebra.ofId R K).comp τ)).comp φK := by
        apply Algebra.TensorProduct.ext_ring
        ext c
        simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars',
          Algebra.TensorProduct.includeRight_apply]
        rw [hφK_tmul, AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul, hστ]
        rfl
      rw [hev, AlgHom.comp_apply, hz, AlgHom.liftEquiv_tmul, one_smul]
      exact ⟨τ a, rfl⟩
    obtain ⟨c, hc⟩ := hzR
    refine ⟨c, hincA ?_⟩
    change 1 ⊗ₜ[R] φ c = 1 ⊗ₜ[R] a
    rw [← hφK_tmul, ← hz]
    change φK (Algebra.TensorProduct.includeRight c) = φK z
    rw [hc]
  have happ : IsIso f.left.appTop := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hφ_inj, hφ_surj⟩
  have hleft : IsIso f.left := by
    have h : f.left = X.left.isoSpec.hom ≫ Spec.map f.left.appTop ≫ Y.left.isoSpec.inv := by
      rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [h]
    infer_instance
  have : IsIso ((Over.forget _).map f) := hleft
  exact isIso_of_reflects_iso f (Over.forget _)

end Langlands.GroupScheme.IntegralModel.IntegralPointIsoCriterion
