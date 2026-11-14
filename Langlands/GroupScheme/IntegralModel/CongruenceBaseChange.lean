import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.OpenCongruence
import Langlands.GroupScheme.Rational.RingEquivBaseChange
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Congruence kernels under local coefficient extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

open GaloisPointComparison

section LocalBaseChange

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

/-- A section reducing to the identity remains so after a local coefficient extension. -/
theorem baseChange_mem_congruenceKernel {x : M.integralSections}
    (hx : x ∈ M.congruenceKernel) :
    baseChangeSectionHom (Spec.algebraMap R A) M.group x ∈
      (M.baseChange A L).congruenceKernel := by
  have hs : residueBaseMap A ≫ Spec.algebraMap R A =
      Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap R A))) ≫
        residueBaseMap R := by
    simp only [residueBaseMap, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalRing.ResidueField.map_comp_residue (algebraMap R A)).symm
  have hx' : residueBaseMap R ≫ x.left =
      residueBaseMap R ≫ (1 : M.integralSections).left := by
    apply (baseChangeSectionHom_eq_iff (residueBaseMap R) M.group x 1).mp
    exact hx.trans (map_one M.reduction).symm
  change baseChangeSectionHom (residueBaseMap A) _
    (baseChangeSectionHom (Spec.algebraMap R A) M.group x) = 1
  rw [← map_one (baseChangeSectionHom (residueBaseMap A) _),
    ← map_one (baseChangeSectionHom (Spec.algebraMap R A) M.group),
    baseChangeSectionHom_eq_iff]
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSectionHom_fst]
    rw [← Category.assoc, hs, Category.assoc, hx', ← Category.assoc]
    rw [← hs, Category.assoc]
  · simp only [baseChangeSectionHom_left, Category.assoc, pullback.lift_snd]

/-- Local coefficient extension restricted to the actual congruence kernels. -/
def congruenceKernelBaseChange :
    M.congruenceKernel →* (M.baseChange A L).congruenceKernel where
  toFun x := ⟨baseChangeSectionHom (Spec.algebraMap R A) M.group x,
    M.baseChange_mem_congruenceKernel A L x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

@[simp] theorem congruenceKernelBaseChange_val (x : M.congruenceKernel) :
    (M.congruenceKernelBaseChange A L x).val =
      baseChangeSectionHom (Spec.algebraMap R A) M.group x := rfl

/-- The actual generic rational-point extension preserves the congruence subgroup. -/
theorem rationalExtend_mem_baseChange_congruenceSubgroup {g : rationalPoints G}
    (hg : g ∈ M.congruenceSubgroup) :
    rationalExtend K L G g ∈ (M.baseChange A L).congruenceSubgroup := by
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨baseChangeSectionHom (Spec.algebraMap R A) M.group x,
    M.baseChange_mem_congruenceKernel A L hx, ?_⟩
  rw [M.baseChange_integralPointMap A L]
  exact (rationalExtend_hom_eq_baseChangeSectionHom K L G ▸ rfl)

/-- Upstairs congruence containment descends when extended integral coefficients
meet the original fraction field in the original integral ring. -/
theorem congruenceSubgroup_le_integralPoints_of_baseChange
    (N : IntegralModel R K G)
    (hintersection : ∀ x : K,
      algebraMap K L x ∈ Set.range (algebraMap A L) ↔
        x ∈ Set.range (algebraMap R K))
    (hup : (M.baseChange A L).congruenceSubgroup ≤
      (N.baseChange A L).integralPoints) :
    M.congruenceSubgroup ≤ N.integralPoints := by
  intro g hg
  exact (N.mem_integralPoints_rationalExtend_iff A L hintersection g).mp
    (hup (M.rationalExtend_mem_baseChange_congruenceSubgroup A L hg))

end LocalBaseChange

section Unramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M N : IntegralModel ↥𝒪[F] F G)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- Containment of the reduction kernel in another model's integral image
descends from the actual maximal unramified extension. -/
theorem congruenceSubgroup_le_integralPoints_of_unramified
    (hup : M.baseChangeUnramified.congruenceSubgroup ≤
      N.baseChangeUnramified.integralPoints) :
    M.congruenceSubgroup ≤ N.integralPoints :=
  M.congruenceSubgroup_le_integralPoints_of_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) N
    unramifiedIntegerRange_intersection hup

end Unramified

end Langlands.GroupScheme.IntegralModel
