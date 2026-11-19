import Langlands.GroupScheme.AffineWeilUnit
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift
import Langlands.GroupScheme.CentralIsogeny.GaloisDefectRestriction
import Langlands.GroupScheme.GaloisCocycleLocalTrivialization

/-! # A primitive for the central defect after local Galois refinement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsCentralIsogeny

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {F K L M : Type u} [Field F] [Field K] [Field L] [Field M]
  [Algebra F K] [Algebra F L] [Algebra F M] [Algebra L M] [Algebra K M]
  [IsScalarTower F L M] [IsScalarTower F K M]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

private theorem baseChangeTarget_symm {N : Type u} [Field N]
    [Algebra F N] [Algebra K N] [IsScalarTower F K N]
    (y : ((GroupScheme.baseChange (Spec.algebraMap F K)).obj G).affinePoints (CommAlgCat.of K N)) :
    (affinePointsBaseChangeMulEquiv F K N H).symm
      (affinePointsTarget ((GroupScheme.baseChange (Spec.algebraMap F K)).obj G)
        ((GroupScheme.baseChange (Spec.algebraMap F K)).map f) (CommAlgCat.of K N) y) =
    G.affinePointsTarget f (CommAlgCat.of F N) ((affinePointsBaseChangeMulEquiv F K N G).symm y) := by
  apply Over.OverMorphism.ext
  simp only [affinePointsTarget_apply, affinePointsBaseChangeMulEquiv_symm_left, Over.comp_left]
  exact congrArg (fun p => p.left) (baseChangePointsEquiv_comp (Spec.algebraMap F K) f (ringTest K N) y)

/-- The restricted central defect has a kernel-valued primitive on a finite Galois
refinement of the coefficient field over the new base. -/
def HasPrimitiveAfterLocalRefinement [Normal F L]
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (d : hf.GaloisLift ξ) : Prop :=
    ∃ (N : Type u) (_ : Field N) (_ : Algebra K N) (_ : FiniteDimensional K N) (_ : IsGalois K N)
      (_ : Algebra M N) (_ : IsScalarTower K M N) (_ : Algebra F N) (_ : Algebra L N)
      (_ : IsScalarTower F K N) (_ : IsScalarTower F M N) (_ : IsScalarTower L M N)
      (_ : IsScalarTower F L N)
      (p : (N ≃ₐ[K] N) → GroupScheme.affinePoints hf.commutativeKernel.toGrp (CommAlgCat.of F N)),
      ∀ σ τ, GaloisPoint.relativeConjugate F K N hf.commutativeKernel.toGrp σ (p τ) /
          p (σ * τ) * p σ =
        GaloisPoint.relativeExtend F L N hf.commutativeKernel.toGrp
          (d.defect ((σ.restrictScalars F).restrictNormal L, (τ.restrictScalars F).restrictNormal L))

/-- A trivialization on the actual pullback cover implies that the restricted central defect
has a primitive after a finite Galois refinement over the new base. -/
theorem exists_primitive_of_baseChange_isTrivial [CharZero K] [Normal F L]
    [FiniteDimensional K M] [Normal K M]
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (d : hf.GaloisLift ξ)
    (h : let b := Spec.algebraMap F K
      (ξ.baseChange b ((Over.pullback b).obj (GaloisCocycle.cover F L))
        ((Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L))).IsTrivial) :
    hf.HasPrimitiveAfterLocalRefinement (K := K) (M := M) ξ d := by
  obtain ⟨a, ha⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial (M := M) ξ h
  let b := Spec.algebraMap F K
  let H' : GroupScheme (Spec (CommRingCat.of K)) := (GroupScheme.baseChange b).obj H
  let G' : GroupScheme (Spec (CommRingCat.of K)) := (GroupScheme.baseChange b).obj G
  let f' : G' ⟶ H' := (GroupScheme.baseChange b).map f
  let a' := affinePointsBaseChangeMulEquiv F K M H a
  obtain ⟨N, _, _, _, _, _, _, hlift⟩ := (hf.baseChange b).exists_finiteGalois_coefficient_lifts
    (fun _ : Unit => a')
  obtain ⟨y, hy⟩ := hlift ()
  let : Algebra F N := Algebra.compHom N (algebraMap F K)
  let : Algebra L N := Algebra.compHom N (algebraMap L M)
  let : IsScalarTower F K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower L M N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F M N := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap K N (algebraMap F K x) = algebraMap M N (algebraMap F M x)
    rw [IsScalarTower.algebraMap_apply F K M, ← IsScalarTower.algebraMap_apply K M N]
  let : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F M N, IsScalarTower.algebraMap_apply L M N,
      ← IsScalarTower.algebraMap_apply F L M]
  let z := (affinePointsBaseChangeMulEquiv F K N G).symm y
  have hz : G.affinePointsTarget f (CommAlgCat.of F N) z = GaloisPoint.relativeExtend F M N H a := by
    have hnat := affinePointsBaseChangeMulEquiv_naturality F K M N H
      (IsScalarTower.toAlgHom K M N) a
    change GaloisPoint.relativeExtend K M N H' a' =
      affinePointsBaseChangeMulEquiv F K N H (GaloisPoint.relativeExtend F M N H a) at hnat
    change G'.affinePointsTarget f' (CommAlgCat.of K N) y =
      GaloisPoint.relativeExtend K M N H' a' at hy
    have hx := congrArg (affinePointsBaseChangeMulEquiv F K N H).symm (hy.trans hnat)
    rw [baseChangeTarget_symm (f := f), MulEquiv.symm_apply_apply] at hx
    exact hx
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hf.exists_primitive_of_lifted_coboundary ξ d z fun σ => ?_⟩
  let s := σ.restrictNormal M
  have hres : (s.restrictScalars F).restrictNormal L = (σ.restrictScalars F).restrictNormal L := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L N).injective
    calc
      _ = algebraMap M N (algebraMap L M ((s.restrictScalars F).restrictNormal L x)) :=
        IsScalarTower.algebraMap_apply L M N _
      _ = algebraMap M N (s (algebraMap L M x)) :=
        congrArg (algebraMap M N) ((s.restrictScalars F).restrictNormal_commutes L x)
      _ = σ (algebraMap M N (algebraMap L M x)) := σ.restrictNormal_commutes M _
      _ = _ := by
        rw [← IsScalarTower.algebraMap_apply L M N]
        exact ((σ.restrictScalars F).restrictNormal_commutes L x).symm
  have hext (x : H.affinePoints (CommAlgCat.of F L)) :
      GaloisPoint.relativeExtend F M N H (GaloisPoint.relativeExtend F L M H x) =
        GaloisPoint.relativeExtend F L N H x := by
    change Lie.affineMap H (IsScalarTower.toAlgHom F M N)
        (Lie.affineMap H (IsScalarTower.toAlgHom F L M) x) =
      Lie.affineMap H (IsScalarTower.toAlgHom F L N) x
    rw [← Lie.affineMap_comp]
    congr 1
  have hact :
      GaloisPoint.relativeExtend F M N H (GaloisPoint.conjugate F M H (s.restrictScalars F) a) =
        GaloisPoint.relativeConjugate F K N H σ (GaloisPoint.relativeExtend F M N H a) := by
    change Lie.affineMap H (IsScalarTower.toAlgHom F M N)
        (Lie.affineMap H (s.restrictScalars F).toAlgHom a) =
      Lie.affineMap H (σ.restrictScalars F).toAlgHom
        (Lie.affineMap H (IsScalarTower.toAlgHom F M N) a)
    rw [← Lie.affineMap_comp, ← Lie.affineMap_comp]
    apply congrArg (fun g : M →ₐ[F] N => Lie.affineMap H g a)
    apply AlgHom.ext
    intro t
    exact σ.restrictNormal_commutes M t
  have hp : G.affinePointsTarget f (CommAlgCat.of F N) (GaloisPoint.relativeConjugate F K N G σ z) =
      GaloisPoint.relativeConjugate F K N H σ (G.affinePointsTarget f (CommAlgCat.of F N) z) :=
    (DFunLike.congr_fun (G.affinePointsTarget_naturality f
      (CommAlgCat.ofHom (σ.restrictScalars F).toAlgHom)) z).symm
  rw [← hres, ← hext, ha s, map_mul, map_inv, hact,
    map_mul, map_inv, hp, hz]

end Langlands.GroupScheme.IsCentralIsogeny
