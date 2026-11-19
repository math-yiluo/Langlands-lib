import Langlands.GroupScheme.CentralIsogeny.GaloisCocycleLifting
import Langlands.GroupScheme.GaloisCocycleRefinement

/-! # Restriction of the central defect along an extension of base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry groupCohomology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

set_option backward.isDefEq.respectTransparency false

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra L M] [Algebra K M]
  [IsScalarTower F L M] [IsScalarTower F K M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

private theorem relativeExtend_target {P Q : GroupScheme (Spec (CommRingCat.of F))}
    (g : P ⟶ Q) (x : P.affinePoints (CommAlgCat.of F L)) :
    GaloisPoint.relativeExtend F L M Q (P.affinePointsTarget g (CommAlgCat.of F L) x) =
      P.affinePointsTarget g (CommAlgCat.of F M) (GaloisPoint.relativeExtend F L M P x) := by
  change GaloisCocycle.coverMap F L M ≫ x ≫ g.hom.hom =
    (GaloisCocycle.coverMap F L M ≫ x) ≫ g.hom.hom
  exact (Category.assoc _ _ _).symm

variable [Normal F L]

private theorem relativeExtend_conjugate {P : GroupScheme (Spec (CommRingCat.of F))}
    (σ : M ≃ₐ[F] M) (x : P.affinePoints (CommAlgCat.of F L)) :
    GaloisPoint.relativeExtend F L M P (GaloisPoint.conjugate F L P (σ.restrictNormal L) x) =
      GaloisPoint.conjugate F M P σ (GaloisPoint.relativeExtend F L M P x) := by
  change GaloisCocycle.coverMap F L M ≫ GaloisCocycle.arrow F L (σ.restrictNormal L) ≫ x =
    GaloisCocycle.arrow F M σ ≫ GaloisCocycle.coverMap F L M ≫ x
  rw [← Category.assoc, ← Category.assoc, GaloisCocycle.arrow_coverMap]

/-- The actual coefficient extension and restriction of automorphisms send central lift
data to central lift data for the restricted Galois values. -/
def restrictGaloisLift (ξ : Cocycle H (GaloisCocycle.cover F L)) (d : hf.GaloisLift ξ) :
    letI : MulDistribMulAction (M ≃ₐ[K] M) (G.affinePoints (CommAlgCat.of F M)) :=
      MulDistribMulAction.compHom _ (AlgEquiv.restrictScalarsHom F)
    CentralCocycleLift (hf.kernelPointInclusion M)
      (G.affinePointsTarget f (CommAlgCat.of F M)) (fun σ : M ≃ₐ[K] M =>
        GaloisPoint.relativeExtend F L M H
          (GaloisCocycle.value ξ ((σ.restrictScalars F).restrictNormal L))) := by
  letI : MulDistribMulAction (M ≃ₐ[K] M) (G.affinePoints (CommAlgCat.of F M)) :=
    MulDistribMulAction.compHom _ (AlgEquiv.restrictScalarsHom F)
  let r : (M ≃ₐ[K] M) →* (L ≃ₐ[F] L) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom F)
  refine
    { value := fun σ => GaloisPoint.relativeExtend F L M G (d.value (r σ))
      project := fun σ => ?_
      defect := fun q => GaloisPoint.relativeExtend F L M hf.commutativeKernel.toGrp
        (d.defect (r q.1, r q.2))
      defect_spec := fun σ τ => ?_ }
  · rw [← relativeExtend_target, d.project]
    rfl
  · change hf.kernelPointInclusion M (GaloisPoint.relativeExtend F L M hf.commutativeKernel.toGrp
      (d.defect (r σ, r τ))) * GaloisPoint.relativeExtend F L M G (d.value (r (σ * τ))) =
      GaloisPoint.relativeExtend F L M G (d.value (r σ)) *
        GaloisPoint.conjugate F M G (σ.restrictScalars F)
          (GaloisPoint.relativeExtend F L M G (d.value (r τ)))
    have hk : GaloisPoint.relativeExtend F L M G (hf.kernelPointInclusion L (d.defect (r σ, r τ))) =
        hf.kernelPointInclusion M (GaloisPoint.relativeExtend F L M hf.commutativeKernel.toGrp
          (d.defect (r σ, r τ))) :=
      relativeExtend_target (M := M) (kernelι f) (d.defect (r σ, r τ))
    rw [map_mul r, ← hk, ← relativeExtend_conjugate,
      ← map_mul (GaloisPoint.relativeExtend F L M G), ← map_mul (GaloisPoint.relativeExtend F L M G)]
    exact congrArg (GaloisPoint.relativeExtend F L M G) (d.defect_spec (r σ) (r τ))

/-- Once a trivializing cochain lifts over the extended coefficient field, the restricted
central defect has a primitive there. -/
theorem exists_primitive_of_lifted_coboundary
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (d : hf.GaloisLift ξ)
    (b : G.affinePoints (CommAlgCat.of F M))
    (h : ∀ σ : M ≃ₐ[K] M,
      GaloisPoint.relativeExtend F L M H
          (GaloisCocycle.value ξ ((σ.restrictScalars F).restrictNormal L)) =
        G.affinePointsTarget f (CommAlgCat.of F M)
          (b * (GaloisPoint.relativeConjugate F K M G σ b)⁻¹)) :
    ∃ a : (M ≃ₐ[K] M) → GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M),
      ∀ σ τ, GaloisPoint.relativeConjugate F K M hf.commutativeKernel.toGrp σ (a τ) /
          a (σ * τ) * a σ =
        GaloisPoint.relativeExtend F L M hf.commutativeKernel.toGrp
          (d.defect ((σ.restrictScalars F).restrictNormal L, (τ.restrictScalars F).restrictNormal L)) := by
  let : MulDistribMulAction (M ≃ₐ[K] M) (G.affinePoints (CommAlgCat.of F M)) :=
    MulDistribMulAction.compHom _ (AlgEquiv.restrictScalarsHom F)
  let : MulDistribMulAction (M ≃ₐ[K] M)
      (GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M)) :=
    MulDistribMulAction.compHom _ (AlgEquiv.restrictScalarsHom F)
  let d' := hf.restrictGaloisLift (K := K) (M := M) ξ d
  have hcentre (a : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M))
      (x : G.affinePoints (CommAlgCat.of F M)) : Commute (hf.kernelPointInclusion M a) x :=
    commute_of_mem_center (hf.isCentral_kernelι _ a) x
  have hiact (σ : M ≃ₐ[K] M)
      (a : GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F M)) :
      hf.kernelPointInclusion M (σ • a) = σ • hf.kernelPointInclusion M a := by
    change (GaloisCocycle.arrow F M (σ.restrictScalars F) ≫ a) ≫ (kernelι f).hom.hom =
      GaloisCocycle.arrow F M (σ.restrictScalars F) ≫ a ≫ (kernelι f).hom.hom
    exact Category.assoc _ _ _
  have hi : Function.Injective (hf.kernelPointInclusion M) :=
    fun _ _ h => (cancel_mono (kernelι f).hom.hom).mp h
  have hexact (x : G.affinePoints (CommAlgCat.of F M)) :
      G.affinePointsTarget f (CommAlgCat.of F M) x = 1 ↔
        ∃ a, hf.kernelPointInclusion M a = x := (mem_range_kernelι_iff f x).symm
  have hcross (σ τ : M ≃ₐ[K] M) :
      b * ((σ * τ) • b)⁻¹ = (b * (σ • b)⁻¹) * σ • (b * (τ • b)⁻¹) := by
    rw [mul_smul, smul_mul', smul_inv']
    group
  exact d'.isMulCoboundary₂_of_cocycle_lift hcentre hiact hi hexact
    (fun σ => b * (σ • b)⁻¹) (fun σ => (h σ).symm) hcross

end Langlands.GroupScheme.IsCentralIsogeny
