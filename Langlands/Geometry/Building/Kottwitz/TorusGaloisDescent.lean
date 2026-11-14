import Langlands.Geometry.Building.Kottwitz.TorusMapProof

/-! # Galois compatibility of torus norm squares -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.GaloisPoint Langlands.GroupScheme.TorusPointsTensorGalois

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building.Kottwitz

section RelativeAutomorphisms

variable (k K L : Type u) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Normal k K]

/-- Conjugation preserves the relative automorphism group of a normal subfield. -/
def conjugateRelativeAut (τ : L ≃ₐ[k] L) (g : L ≃ₐ[K] L) : L ≃ₐ[K] L where
  __ := (τ.symm.toRingEquiv.trans g.toRingEquiv).trans τ.toRingEquiv
  commutes' a := by
    change τ (g (τ.symm (algebraMap K L a))) = algebraMap K L a
    rw [← τ.symm.restrictNormal_commutes K a, g.commutes,
      τ.symm.restrictNormal_commutes, τ.apply_symm_apply]

/-- Conjugation permutes the relative automorphisms. -/
def conjugateRelativeAutEquiv (τ : L ≃ₐ[k] L) : (L ≃ₐ[K] L) ≃ (L ≃ₐ[K] L) where
  toFun := conjugateRelativeAut k K L τ
  invFun := conjugateRelativeAut k K L τ.symm
  left_inv g := by ext x; simp [conjugateRelativeAut]
  right_inv g := by ext x; simp [conjugateRelativeAut]

variable [FiniteDimensional K L] [IsGalois K L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- Relative point norms commute with automorphisms over the ground field. -/
theorem relativeNorm_conjugate (τ : L ≃ₐ[k] L)
    (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    relativeNorm k K L T (conjugate k L T.toGrp τ x) =
      conjugate k K T.toGrp (τ.restrictNormal K) (relativeNorm k K L T x) := by
  apply relativeExtend_injective k K L T.toGrp
  rw [relativeExtend_conjugate k K L T.toGrp (τ.restrictNormal K) τ
    (fun a => (τ.restrictNormal_commutes K a).symm), relativeExtend_norm,
    relativeExtend_norm, map_prod]
  symm
  apply Fintype.prod_equiv (conjugateRelativeAutEquiv k K L τ)
  intro g
  change conjugate k L T.toGrp τ (conjugate k L T.toGrp (g.restrictScalars k) x) =
    conjugate k L T.toGrp ((conjugateRelativeAut k K L τ g).restrictScalars k)
      (conjugate k L T.toGrp τ x)
  rw [← conjugate_mul, ← conjugate_mul]
  have heq : τ * g.restrictScalars k =
      (conjugateRelativeAut k K L τ g).restrictScalars k * τ := by
    ext a
    change τ (g a) = τ (g (τ.symm (τ a)))
    rw [τ.symm_apply_apply]
  exact congrArg (fun f => conjugate k L T.toGrp f x) heq

end RelativeAutomorphisms

section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp)

variable (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) L]

/-- The integer normalization is preserved by automorphisms over `F`. -/
theorem normalizedIntermediateValuation_groundAut (τ : L ≃ₐ[F] L) (x : L) :
    normalizedIntermediateValuation F L (τ x) = normalizedIntermediateValuation F L x := by
  have hval : intermediateValuation F L (τ x) = intermediateValuation F L x := by
    let : NontriviallyNormedField F := Langlands.LocalGalois.localNormedField F
    apply NNReal.eq
    change spectralNorm F (SeparableClosure F) (algebraMap L (SeparableClosure F) (τ x)) =
      spectralNorm F (SeparableClosure F) (algebraMap L (SeparableClosure F) x)
    rw [← τ.liftNormal_commutes (SeparableClosure F) x]
    exact (spectralNorm_eq_of_equiv (τ.liftNormal (SeparableClosure F)) _).symm
  exact (normalizedIntermediateValuation_spec' F L).1.eq_iff.mpr hval

/-- The source-positive integer order is preserved by ground-field automorphisms. -/
theorem orderUnits_groundAut (τ : L ≃ₐ[F] L) (a : Lˣ) :
    IntegerValuation.orderUnits (normalizedIntermediateValuation F L)
        (Units.map τ.toMonoidHom a) =
      IntegerValuation.orderUnits (normalizedIntermediateValuation F L) a := by
  apply Multiplicative.toAdd.injective
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd]
  exact congrArg (fun z => -WithZero.log z)
    (normalizedIntermediateValuation_groundAut F L τ (a : L))

variable [IsAffine T.X.left]

/-- The norm square on a pure evaluation intertwines compatible ground-field automorphisms. -/
theorem normLawValue_groundConjugate_tmul
    (hL : IsSplitTorus (baseChanged F L T).toGrp)
    (hE : IsSplitTorus (baseChanged F (SeparableClosure F) T).toGrp)
    (τ : L ≃ₐ[F] L) (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (h : ∀ a : L, σ (algebraMap L (SeparableClosure F) a) =
      algebraMap L (SeparableClosure F) (τ a))
    (w : Additive Lˣ) (ν : cocharacterLattice (baseChanged F L T)) :
    normLawValue F F T L hL (Additive.ofMul (conjugate F L T.toGrp τ
      (coefficientEvaluation F L T (w ⊗ₜ[ULift.{u} ℤ] ν)).toMul)) =
      torusGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F) T
        (σ.restrictNormal (UnramifiedClosure F))
        (normLawValue F F T L hL (coefficientEvaluation F L T (w ⊗ₜ[ULift.{u} ℤ] ν))) := by
  obtain ⟨a₀, ha₀⟩ := exists_not_isOfFinOrder F L
  rw [← coefficientEvaluation_galois_tmul, normLawValue_tmul, normLawValue_tmul, toMul_ofMul,
    orderUnits_groundAut F L τ, ← map_zsmul,
    extendGeometricCocharacters_galois F L (SeparableClosure F) T hE ha₀ τ σ h,
    ← inertiaGammaRepresentation_restrict]

/-- The norm square intertwines compatible ground-field automorphisms on all points. -/
theorem normLawValue_groundConjugate
    (hL : IsSplitTorus (baseChanged F L T).toGrp)
    (hE : IsSplitTorus (baseChanged F (SeparableClosure F) T).toGrp)
    (τ : L ≃ₐ[F] L) (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (h : ∀ a : L, σ (algebraMap L (SeparableClosure F) a) =
      algebraMap L (SeparableClosure F) (τ a))
    (x : affinePoints T.toGrp (CommAlgCat.of F L)) :
    normLawValue F F T L hL (Additive.ofMul (conjugate F L T.toGrp τ x)) =
      torusGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F) T
        (σ.restrictNormal (UnramifiedClosure F))
        (normLawValue F F T L hL (Additive.ofMul x)) := by
  have key := additive_ext_coefficientEvaluation F L T hL
    (φ := (normLawValue F F T L hL).comp (conjugate F L T.toGrp τ).toAdditive)
    (φ' := (torusGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F) T
      (σ.restrictNormal (UnramifiedClosure F))).toAddMonoidHom.comp (normLawValue F F T L hL))
    (fun w ν => normLawValue_groundConjugate_tmul F T L hL hE τ σ h w ν)
  exact DFunLike.congr_fun key (Additive.ofMul x)

variable [IsGalois (UnramifiedClosure F) L] [Normal F L]

/-- A splitting field normal over the ground field supplies equivariance of the selected map. -/
theorem torusKottwitzEquivariant_of_normal_splitting
    (hL : IsSplitTorus (baseChanged F L T).toGrp) :
    TorusKottwitzEquivariant F T hT := by
  have hκ := (torusNormLawAt_iff F F T L hL (torusKottwitz F F T hT)).mp
    ((torusKottwitzExistence F F T hT).2.1 L hL)
  have hE := IsSplitTorus.baseChange_fieldTower F L (SeparableClosure F) T.toGrp hL
  intro σ t
  obtain ⟨x, rfl⟩ := relativeNorm_unramifiedClosure_surjective F F T L hL t
  let ρ := σ.liftNormal (SeparableClosure F)
  let τ := ρ.restrictNormal L
  have hρ : ρ.restrictNormal (UnramifiedClosure F) = σ :=
    σ.restrict_liftNormal (SeparableClosure F)
  have hτ : τ.restrictNormal (UnramifiedClosure F) = σ := by
    change AlgEquiv.restrictNormalHom (UnramifiedClosure F)
      (AlgEquiv.restrictNormalHom L ρ) = σ
    rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
      (UnramifiedClosure F) L ρ]
    exact hρ
  rw [← hτ, ← relativeNorm_conjugate F (UnramifiedClosure F) L T τ x, hκ, hκ]
  simp only [toAdd_ofAdd]
  rw [hτ, ← hρ]
  exact normLawValue_groundConjugate F T L hL hE τ ρ
    (fun a => (ρ.restrictNormal_commutes L a).symm) x

end Local

end Langlands.Geometry.Building.Kottwitz
