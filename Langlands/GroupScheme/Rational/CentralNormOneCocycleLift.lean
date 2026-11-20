import Langlands.ClassField.Global.TensorNormOnePrimitive
import Langlands.GroupScheme.Rational.CentralTensorDefectShapiro
import Langlands.GroupScheme.Rational.NormOneTorsionAffinePoints

/-! # Central cocycle lifting through a kernel of norm-one torsion -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry groupCohomology
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Langlands.Algebra Langlands.ClassField.Global.TensorUnitShapiro

variable {F B L : Type u} [Field F] [Field B] [Field L]
  [Algebra F B] [FiniteDimensional F B] [Algebra F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H}

/-- A cocycle lifts to the source on a finite Galois refinement of its coefficient cover. -/
def Cocycle.LiftsAfterFiniteGaloisRefinement (ξ : Cocycle H (GaloisCocycle.cover F L))
    (f : G ⟶ H) : Prop :=
  ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M) (_ : IsGalois F M)
    (_ : Algebra L M) (_ : IsScalarTower F L M)
    (ζ : Cocycle G (GaloisCocycle.cover F M)), ζ.map f = ξ.refine (GaloisCocycle.coverMap F L M)

namespace IsCentralIsogeny

variable (hf : IsCentralIsogeny f)

local notation "T" n => WeilGm.normOneTorsion F B n

/-- A given norm-one torsion model makes the kernel points the actual norm-one roots
of unity in each affine coefficient tensor. -/
def kernelNormOneEquiv (n : ℕ) (e : kernel f ≅ T n)
    (R : Type u) [CommRing R] [Algebra F R] :
    GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R) ≃*
      WeilGm.normOneTorsionUnits (B := B) n (CommAlgCat.of F R) :=
  (((yonedaGrp.mapIso e).app (op ((algSpec (CommRingCat.of F)).obj
    (op (CommAlgCat.of F R))))).groupIsoToMulEquiv).trans
      (WeilGm.normOneTorsionAffineEquiv n (CommAlgCat.of F R))

/-- The kernel model homomorphism to the affine Weil restriction of `Gₘ`. -/
abbrev kernelNormOneToWeil (n : ℕ) (e : kernel f ≅ T n) :
    kernel f ⟶ WeilGm.groupScheme (CommRingCat.of F) B :=
  e.hom ≫ WeilGm.normOneTorsionInclusion (F := F) (B := B) n

/-- The underlying tensor unit is the point map of the isomorphism followed by the
norm-one torsion inclusion in the Weil group. -/
theorem kernelNormOneEquiv_val (n : ℕ) (e : kernel f ≅ T n)
    (R : Type u) [CommRing R] [Algebra F R]
    (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R)) :
    (kernelNormOneEquiv n e R x).val = kernelTensorUnitMap (kernelNormOneToWeil n e) R x := by
  change (WeilGm.normOneTorsionAffineEquiv n (CommAlgCat.of F R) (x ≫ e.hom.hom.hom)).val = _
  rw [WeilGm.normOneTorsionAffineEquiv_val]
  change WeilGm.affineUnitsEquiv _ B _
    ((x ≫ e.hom.hom.hom) ≫ (WeilGm.normOneTorsionInclusion n).hom.hom) =
      WeilGm.affineUnitsEquiv _ B _ (x ≫ (kernelNormOneToWeil n e).hom.hom)
  rw [Grp.comp_hom_hom, Category.assoc]

/-- The tensor unit of a kernel point is killed by the indicated power. -/
theorem kernelTensorUnitMap_pow_eq_one (n : ℕ) (e : kernel f ≅ T n)
    (R : Type u) [CommRing R] [Algebra F R]
    (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R)) :
    kernelTensorUnitMap (kernelNormOneToWeil n e) R x ^ n = 1 := by
  rw [← kernelNormOneEquiv_val n e]
  exact (mem_rootsOfUnity n _).mp (kernelNormOneEquiv n e R x).property.1

/-- The tensor unit of a kernel point has determinant norm one. -/
theorem kernelTensorUnitMap_norm_eq_one (n : ℕ) (e : kernel f ≅ T n)
    (R : Type u) [CommRing R] [Algebra F R]
    (x : GroupScheme.affinePoints (kernel f) (CommAlgCat.of F R)) :
    tensorNormUnits F B R (kernelTensorUnitMap (kernelNormOneToWeil n e) R x) = 1 := by
  rw [← kernelNormOneEquiv_val n e]
  exact (kernelNormOneEquiv n e R x).property.2

private def refineLift [Normal F L]
    {M : Type u} [Field M] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) :
    hf.GaloisLift (ξ.refine (GaloisCocycle.coverMap F L M)) := by
  let rd := hf.restrictGaloisLift (K := F) (M := M) ξ d
  refine ⟨rd.value, fun σ => ?_, rd.defect, rd.defect_spec⟩
  rw [GaloisCocycle.value_refine]
  exact rd.project σ

variable [IsGalois F L]

/-- A norm-one torsion primitive for the tensor defect gives a lift of the whole
natural cocycle on the same Galois refinement. -/
theorem liftsAfterFiniteGaloisRefinement_of_normOnePrimitive
    (n : ℕ) (e : kernel f ≅ T n)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ)
    (h : TensorNormOnePrimitiveAfterRefinement n
      (hf.kernelTensorDefect (kernelNormOneToWeil n e) d)) :
    ξ.LiftsAfterFiniteGaloisRefinement f := by
  obtain ⟨M, _, _, _, _, _, _, a, ha, hN, hδ⟩ := h
  let p (σ : Gal(M/F)) := (kernelNormOneEquiv n e M).symm
    ⟨a σ, (mem_rootsOfUnity n (a σ)).mpr (ha σ), hN σ⟩
  let j := kernelTensorUnitMap (kernelNormOneToWeil n e) M
  have hp (σ : Gal(M/F)) : j (p σ) = a σ := by
    rw [← kernelNormOneEquiv_val n e]
    exact congrArg Subtype.val ((kernelNormOneEquiv n e M).apply_symm_apply _)
  have hj : Function.Injective j := fun _ _ he => (kernelNormOneEquiv n e M).injective
    (Subtype.ext ((kernelNormOneEquiv_val n e M _).trans (he.trans (kernelNormOneEquiv_val n e M _).symm)))
  let d' := hf.refineLift (M := M) d
  have hd : IsMulCoboundary₂ d'.defect := by
    refine ⟨p, fun σ τ => ?_⟩
    apply hj
    have hact : j (σ • p τ) = tensorAction F B M σ (j (p τ)) :=
      kernelTensorUnitMap_naturality (kernelNormOneToWeil n e) σ.toAlgHom _
    have hr : j (d'.defect (σ, τ)) = extendTensorUnit M
        (hf.kernelTensorDefect (kernelNormOneToWeil n e) d (σ.restrictNormal L, τ.restrictNormal L)) :=
      kernelTensorUnitMap_naturality (kernelNormOneToWeil n e) (IsScalarTower.toAlgHom F L M) _
    rw [map_mul, map_div, hact, hp, hp, hp, hr]
    exact hδ σ τ
  obtain ⟨ζ, hζ⟩ := (hf.galoisLift_isMulCoboundary₂_iff _ d').mp hd
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ζ, hζ⟩

variable [NumberField F] [NumberField B] [NumberField L] [FiniteDimensional F L]
  [Algebra B L] [IsScalarTower F B L]

/-- For an everywhere locally trivial cocycle the central defect is the differential of
a torsion tensor-unit cochain after one finite Galois refinement. -/
theorem tensorTorsionPrimitiveAfterRefinement_of_normOneKernel
    (n : ℕ) (hn : n ≠ 0) (e : kernel f ≅ T n)
    {ξ : Cocycle H (GaloisCocycle.cover F L)} (d : hf.GaloisLift ξ) (h : ξ.LocallyTrivial) :
    TensorTorsionPrimitiveAfterRefinement n (hf.kernelTensorDefect (kernelNormOneToWeil n e) d) := by
  apply tensorTorsionPrimitiveAfterRefinement_of_units n hn
  · intro v
    exact kernelTensorUnitMap_pow_eq_one n e L (d.defect v)
  · exact hf.exists_tensorPrimitive_of_obstruction_eq_zero (kernelNormOneToWeil n e) d
      (hf.kernelTensorObstruction_eq_zero (kernelNormOneToWeil n e) d h)

end IsCentralIsogeny
end Langlands.GroupScheme
