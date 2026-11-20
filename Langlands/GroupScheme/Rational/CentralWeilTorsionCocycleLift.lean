import Langlands.GroupScheme.Rational.NumberFieldNormOneCocycleLift
import Langlands.GroupScheme.Rational.WeilTorsionAffinePoints

/-! # Finite Galois lifting through Weil torsion -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry groupCohomology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A lift after refining an intermediate coefficient cover is a lift after
refining the original cover. -/
theorem Cocycle.LiftsAfterFiniteGaloisRefinement.of_refinement
    {F L K : Type u} [Field F] [Field L] [Field K] [Algebra F L] [Algebra F K] [Algebra L K]
    [IsScalarTower F L K] {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
    {ξ : Cocycle H (GaloisCocycle.cover F L)}
    (h : (ξ.refine (GaloisCocycle.coverMap F L K)).LiftsAfterFiniteGaloisRefinement f) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  obtain ⟨E, _, _, _, _, _, _, ζ, hζ⟩ := h
  let : Algebra L E := Algebra.compHom E (algebraMap L K)
  let : IsScalarTower L K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K E, IsScalarTower.algebraMap_apply L K E,
      ← IsScalarTower.algebraMap_apply F L K]
  let r := GaloisCocycle.coverMap F L K
  let t := GaloisCocycle.coverMap F K E
  have ht : t ≫ r = GaloisCocycle.coverMap F L E := by
    change (algSpec (CommRingCat.of F)).map
          (CommAlgCat.ofHom (IsScalarTower.toAlgHom F K E)).op ≫
        (algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom F L K)).op = _
    rw [← Functor.map_comp]
    rfl
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ζ, hζ.trans ?_⟩
  rw [← ht]
  have hh {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ GaloisCocycle.cover F E) :
      ((ξ.refine r).refine t).toFun a b = (ξ.refine (t ≫ r)).toFun a b := by
    simp only [Cocycle.refine_toFun, Category.assoc]
  generalize ((ξ.refine r).refine t) = ξ₁ at hh ⊢
  generalize (ξ.refine (t ≫ r)) = ξ₂ at hh ⊢
  cases ξ₁
  cases ξ₂
  congr
  funext Z a b
  exact hh a b

open Langlands.ClassField.Global in
/-- A finite Galois coefficient cover of a number field has a finite Galois
refinement containing a specified finite extension of the base. -/
theorem exists_finiteGalois_refinement_with_algebra
    (F B L : Type u) [Field F] [Field B] [Field L] [NumberField F]
    [Algebra F B] [Algebra F L] [FiniteDimensional F B] [FiniteDimensional F L] [IsGalois F L] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : IsGalois F K)
      (_ : Algebra L K) (_ : IsScalarTower F L K) (_ : Algebra B K), IsScalarTower F B K := by
  let : NumberField L := NumberField.of_module_finite F L
  obtain ⟨D, _, _, ⟨i⟩⟩ := exists_finite_galois_algHom F B
  let : NumberField D := NumberField.of_module_finite F D
  obtain ⟨K, _, _, _, _, _, _, _, _⟩ := FundamentalClass.exists_galois_tower F L D
  let j := (IsScalarTower.toAlgHom F D K).comp i
  let : Algebra B K := j.toRingHom.toAlgebra
  let : IsScalarTower F B K := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

namespace IsCentralIsogeny

open Langlands.ClassField.Global.TensorUnitShapiro

variable {F B : Type u} [Field F] [Field B] [Algebra F B] [FiniteDimensional F B]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}
  (n : ℕ) (e : kernel f ≅ WeilGm.weilTorsion F B n)

/-- The kernel model's inclusion into the Weil multiplicative group. -/
abbrev kernelWeilTorsionToWeil : kernel f ⟶ WeilGm.groupScheme (CommRingCat.of F) B :=
  e.hom ≫ WeilGm.weilTorsionInclusion n

/-- An identification of the kernel with Weil torsion identifies its actual affine
points with the roots of unity of the coefficient tensor. -/
def kernelWeilTorsionEquiv (R : Type u) [CommRing R] [Algebra F R] :
    GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R) ≃* rootsOfUnity n (B ⊗[F] R) :=
  (((yonedaGrp.mapIso e).app (op ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F R))))).groupIsoToMulEquiv).trans
      (WeilGm.weilTorsionAffineEquiv n (CommAlgCat.of F R))

theorem kernelWeilTorsionEquiv_val (R : Type u) [CommRing R] [Algebra F R]
    (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R)) :
    (kernelWeilTorsionEquiv n e R x).val = kernelTensorUnitMap (kernelWeilTorsionToWeil n e) R x := by
  change (WeilGm.weilTorsionAffineEquiv n (CommAlgCat.of F R) (x ≫ e.hom.hom.hom)).val = _
  rw [WeilGm.weilTorsionAffineEquiv_val]
  change WeilGm.affineUnitsEquiv _ B _
    ((x ≫ e.hom.hom.hom) ≫ (WeilGm.weilTorsionInclusion n).hom.hom) =
      WeilGm.affineUnitsEquiv _ B _ (x ≫ (kernelWeilTorsionToWeil n e).hom.hom)
  rw [Grp.comp_hom_hom, Category.assoc]

theorem kernelTensorUnitMap_weilTorsion_injective (R : Type u) [CommRing R] [Algebra F R] :
    Function.Injective (kernelTensorUnitMap (kernelWeilTorsionToWeil n e) R) := by
  intro x y h
  apply (kernelWeilTorsionEquiv n e R).injective
  apply Subtype.ext
  simpa only [kernelWeilTorsionEquiv_val n e] using h

theorem kernelTensorUnitMap_weilTorsion_symm (R : Type u) [CommRing R] [Algebra F R]
    (x : rootsOfUnity n (B ⊗[F] R)) :
    kernelTensorUnitMap (kernelWeilTorsionToWeil n e) R ((kernelWeilTorsionEquiv n e R).symm x) = x.val := by
  rw [← kernelWeilTorsionEquiv_val n e, MulEquiv.apply_symm_apply]

theorem kernelTensorUnitMap_weilTorsion_pow_eq_one (R : Type u) [CommRing R] [Algebra F R]
    (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R)) :
    kernelTensorUnitMap (kernelWeilTorsionToWeil n e) R x ^ n = 1 := by
  rw [← kernelWeilTorsionEquiv_val n e]
  exact (mem_rootsOfUnity n _).mp (kernelWeilTorsionEquiv n e R x).property

variable [NumberField F] [NumberField B]
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (hf : IsCentralIsogeny f)

include e in
private theorem lifts_of_weilTorsion_galoisLift [NumberField L] [Algebra B L] [IsScalarTower F B L]
    (hn : 0 < n) {ξ : Cocycle H (GaloisCocycle.cover F L)}
    (d : hf.GaloisLift ξ) (h : ξ.LocallyTrivial) : ξ.LiftsAfterFiniteGaloisRefinement f := by
  let q := kernelWeilTorsionToWeil n e
  have hpow (p : Gal(L/F) × Gal(L/F)) : hf.kernelTensorDefect q d p ^ n = 1 :=
    kernelTensorUnitMap_weilTorsion_pow_eq_one n e L (d.defect p)
  obtain ⟨E, _, _, _, _, _, _, a, ha, hδ⟩ := tensorTorsionPrimitiveAfterRefinement_of_units
    n hn.ne' (hf.kernelTensorDefect q d) hpow
    (hf.exists_tensorPrimitive_of_obstruction_eq_zero q d (hf.kernelTensorObstruction_eq_zero q d h))
  let r := GaloisCocycle.coverMap F L E
  let rd := hf.restrictGaloisLift (K := F) (M := E) ξ d
  let d' : hf.GaloisLift (ξ.refine r) :=
    ⟨rd.value, fun σ => by rw [GaloisCocycle.value_refine]; exact rd.project σ,
      rd.defect, rd.defect_spec⟩
  let p (σ : Gal(E/F)) := (kernelWeilTorsionEquiv n e E).symm
    ⟨a σ, (mem_rootsOfUnity n (a σ)).mpr (ha σ)⟩
  let j := kernelTensorUnitMap q E
  have hp (σ : Gal(E/F)) : j (p σ) = a σ := kernelTensorUnitMap_weilTorsion_symm n e E _
  have hd : IsMulCoboundary₂ d'.defect := by
    refine ⟨p, fun σ τ => ?_⟩
    apply kernelTensorUnitMap_weilTorsion_injective n e
    change j ((σ • p τ) / p (σ * τ) * p σ) = j (d'.defect (σ, τ))
    have hact : j (σ • p τ) = tensorAction F B E σ (j (p τ)) :=
      kernelTensorUnitMap_naturality q σ.toAlgHom _
    have hr : j (d'.defect (σ, τ)) = extendTensorUnit E
        (hf.kernelTensorDefect q d (σ.restrictNormal L, τ.restrictNormal L)) :=
      kernelTensorUnitMap_naturality q (IsScalarTower.toAlgHom F L E) _
    rw [map_mul, map_div, hact, hp, hp, hp, hr]
    exact hδ σ τ
  obtain ⟨ζ, hζ⟩ := (hf.galoisLift_isMulCoboundary₂_iff _ d').mp hd
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ζ, hζ⟩

include e hf in
/-- Local triviality of the target supplies a global lift through a Weil torsion
kernel after finite Galois refinement. -/
theorem liftsAfterFiniteGaloisRefinement_of_weilTorsionKernel
    (hn : 0 < n) (ξ : Cocycle H (GaloisCocycle.cover F L)) (h : ξ.LocallyTrivial) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  obtain ⟨K, _, _, _, _, _, _, _, _⟩ := exists_finiteGalois_refinement_with_algebra F B L
  let r := GaloisCocycle.coverMap F L K
  obtain ⟨E, _, _, _, _, _, _, ⟨d⟩⟩ := hf.exists_finiteGalois_refine_galoisLift (ξ.refine r)
  let : NumberField E := NumberField.of_module_finite F E
  let : Algebra B E := Algebra.compHom E (algebraMap B K)
  let : IsScalarTower B K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower F B E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K E, IsScalarTower.algebraMap_apply B K E,
      ← IsScalarTower.algebraMap_apply F B K]
  exact (lifts_of_weilTorsion_galoisLift n e hf hn d
    ((h.refine r).refine (GaloisCocycle.coverMap F K E))).of_refinement.of_refinement

end IsCentralIsogeny

end Langlands.GroupScheme
