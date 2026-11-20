import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.GaloisDefectRestriction
import Langlands.GroupScheme.GaloisCocycleScalarExtension

/-! # Central lift data on a scalar-extended Galois cover -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

local notation "b" => Spec.algebraMap F K
local notation "bc" => GroupScheme.baseChange b

/-- Affine points of the scalar-extended actual kernel identify with the original kernel
points over the same coefficient field. -/
def scalarExtensionKernelPointsEquiv :
    (GaloisCocycle.cover K M ⟶ (kernel ((bc).map f)).X) ≃*
      GroupScheme.affinePoints (kernel f) (CommAlgCat.of F M) :=
  (((yonedaGrp.mapIso (kernelBaseChangeIso b f).symm).app
    (op (GaloisCocycle.cover K M))).groupIsoToMulEquiv).trans
      (GaloisCocycle.scalarExtensionPointsEquiv (kernel f))

/-- The kernel point comparison is the actual kernel isomorphism followed by the coordinate
comparison for the original kernel. -/
theorem scalarExtensionKernelPointsEquiv_apply
    (x : GaloisCocycle.cover K M ⟶ (kernel ((bc).map f)).X) :
    scalarExtensionKernelPointsEquiv (f := f) x =
      GaloisCocycle.scalarExtensionPointsEquiv (kernel f)
        (x ≫ (kernelBaseChangeIso b f).inv.hom.hom) := rfl

private theorem scalarExtensionPointsEquiv_kernelInclusion
    (x : GaloisCocycle.cover K M ⟶ (kernel ((bc).map f)).X) :
    GaloisCocycle.scalarExtensionPointsEquiv G ((hf.baseChange b).kernelPointInclusion M x) =
      hf.kernelPointInclusion M (scalarExtensionKernelPointsEquiv (f := f) x) := by
  change GaloisCocycle.scalarExtensionPointsEquiv G (x ≫ (kernelι ((bc).map f)).hom.hom) = _
  have h := congrArg (fun k => k.hom.hom) (kernelBaseChangeIso_inv_ι b f)
  change (kernelBaseChangeIso b f).inv.hom.hom ≫ ((bc).map (kernelι f)).hom.hom =
    (kernelι ((bc).map f)).hom.hom at h
  rw [← h, ← Category.assoc, GaloisCocycle.scalarExtensionPointsEquiv_comp]
  rfl

variable [Normal F L]

/-- Scalar extension of the group and coefficient cover carries central lift data, with the
defect obtained by restricting automorphisms and extending the original kernel points. -/
def scalarExtensionGaloisLift {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    (hf.baseChange b).GaloisLift (GaloisCocycle.scalarExtension (K := K) (M := M) ξ) := by
  letI : MulDistribMulAction (M ≃ₐ[K] M) (G.affinePoints (CommAlgCat.of F M)) :=
    MulDistribMulAction.compHom _ (AlgEquiv.restrictScalarsHom F)
  let eG := GaloisCocycle.scalarExtensionPointsEquiv (K := K) (M := M) G
  let eH := GaloisCocycle.scalarExtensionPointsEquiv (K := K) (M := M) H
  let eZ := scalarExtensionKernelPointsEquiv (K := K) (M := M) (f := f)
  let d' := hf.restrictGaloisLift (K := K) (M := M) ξ d
  refine ⟨fun σ => eG.symm (d'.value σ), fun σ => ?_, fun q => eZ.symm (d'.defect q), fun σ τ => ?_⟩
  · apply eH.injective
    change GaloisCocycle.scalarExtensionPointsEquiv H
      (eG.symm (d'.value σ) ≫ ((bc).map f).hom.hom) = _
    rw [GaloisCocycle.scalarExtensionPointsEquiv_comp, show
      GaloisCocycle.scalarExtensionPointsEquiv G (eG.symm (d'.value σ)) = d'.value σ from
        eG.apply_symm_apply _, GaloisCocycle.value_scalarExtension]
    exact d'.project σ
  · apply eG.injective
    have hact : eG (σ • eG.symm (d'.value τ)) =
        GaloisPoint.relativeConjugate F K M G σ (d'.value τ) := by
      change GaloisCocycle.scalarExtensionPointsEquiv G
        (GaloisPoint.conjugate K M _ σ (eG.symm (d'.value τ))) = _
      rw [GaloisCocycle.scalarExtensionPointsEquiv_conjugate]
      exact congrArg (GaloisPoint.relativeConjugate F K M G σ) (eG.apply_symm_apply _)
    simp only [map_mul, eG.apply_symm_apply, hact]
    rw [show eG ((hf.baseChange b).kernelPointInclusion M (eZ.symm (d'.defect (σ, τ)))) =
      hf.kernelPointInclusion M (d'.defect (σ, τ)) from
        (hf.scalarExtensionPointsEquiv_kernelInclusion _).trans
          (congrArg (hf.kernelPointInclusion M) (eZ.apply_symm_apply _))]
    exact d'.defect_spec σ τ

/-- In the comparison of actual kernel points, the new defect is the coefficient extension
of the old defect at the restricted automorphisms. -/
theorem scalarExtensionGaloisLift_defect {ξ : Cocycle H (GaloisCocycle.cover F L)}
    (d : hf.GaloisLift ξ) (σ τ : M ≃ₐ[K] M) :
    scalarExtensionKernelPointsEquiv (f := f)
        ((hf.scalarExtensionGaloisLift d).defect (σ, τ)) =
      GaloisPoint.relativeExtend F L M (kernel f)
        (d.defect ((σ.restrictScalars F).restrictNormal L, (τ.restrictScalars F).restrictNormal L)) :=
  MulEquiv.apply_symm_apply _ _

end Langlands.GroupScheme.IsCentralIsogeny
