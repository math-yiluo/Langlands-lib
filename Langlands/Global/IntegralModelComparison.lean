import Langlands.Global.IntegralModelCompletions
import Langlands.GroupScheme.IntegralModel.BaseChangePoints
import Langlands.Global.FiniteTypeIntegralFamily

/-! # Comparing arithmetic model points with the fixed integral family -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Global.IntegralModelCompletions

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [NumberField F]
  (S : Finset (FinitePlace F))

section LocalComparison

variable (v : {v : FinitePlace F // v ∉ S})

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    (v.1.adicCompletionIntegers F) := (integerMap F S v).toAlgebra

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1) :=
  ((algebraMap F (FiniteCompletion F v.1)).comp
    (algebraMap ((S : Set (FinitePlace F)).integer F) F)).toAlgebra

local instance : SMul ((S : Set (FinitePlace F)).integer F) F :=
  (inferInstance : Algebra ((S : Set (FinitePlace F)).integer F) F).toSMul

local instance : SMul ((S : Set (FinitePlace F)).integer F) (FiniteCompletion F v.1) :=
  (inferInstance : Algebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1)).toSMul

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    (v.1.adicCompletionIntegers F) (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := v.1.adicCompletionIntegers F) (A := FiniteCompletion F v.1) fun _ => rfl

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    F (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := F) (A := FiniteCompletion F v.1) fun _ => rfl

/-- The canonical completed integers as an algebra over the supplied S-integers. -/
def integerSubalgebra : Subalgebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1) where
  __ := (v.1.adicCompletionIntegers F).toSubring
  algebraMap_mem' r := (integerMap F S v r).property

private instance : IsFractionRing (integerSubalgebra F S v) (FiniteCompletion F v.1) :=
  inferInstanceAs (IsFractionRing (v.1.adicCompletionIntegers F) (FiniteCompletion F v.1))

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)

/-- The actual local model subgroup is tested by original-model regular functions. -/
theorem mem_subgroup_iff (p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))) :
    p ∈ subgroup F S v M ↔
      ∀ a : AffineCoordinateRing ((S : Set (FinitePlace F)).integer F) M.group.X,
        G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v.1)) p
          (M.genericCoordinate a) ∈ v.1.adicCompletionIntegers F := by
  exact M.mem_baseChange_subalgebra_coefficientIntegralPoints_iff
    (FiniteCompletion F v.1) (integerSubalgebra F S v) p

/-- The fixed original-model finite test set also tests the local image subgroup. -/
theorem mem_subgroup_iff_testSet
    (p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))) :
    p ∈ subgroup F S v M ↔
      ∀ a ∈ integralPointTestSet ((S : Set (FinitePlace F)).integer F) M.group.X,
        G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v.1)) p
          (M.genericCoordinate a) ∈ v.1.adicCompletionIntegers F := by
  exact M.mem_baseChange_subalgebra_coefficientIntegralPoints_iff_testSet
    (FiniteCompletion F v.1) (integerSubalgebra F S v) p

end LocalComparison

section UniformIntegrality

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)

private def uniformlyIntegralSubalgebra :
    Subalgebra F (AffineCoordinateRing F G.X) where
  carrier := {a | ∀ᶠ v in cofinite, ∀ hv : v ∉ S,
    ∀ p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
      p ∈ subgroup F S ⟨v, hv⟩ M →
        GaloisPoint.coordinates F G (FiniteCompletion F v) p a ∈
          v.adicCompletionIntegers F}
  zero_mem' := by
    change ∀ᶠ (v : FinitePlace F) in cofinite, _
    filter_upwards [] with v hv p hp
    rw [map_zero]
    exact (v.adicCompletionIntegers F).toSubring.zero_mem
  one_mem' := by
    change ∀ᶠ (v : FinitePlace F) in cofinite, _
    filter_upwards [] with v hv p hp
    rw [map_one]
    exact (v.adicCompletionIntegers F).toSubring.one_mem
  add_mem' := by
    intro a b ha hb
    change ∀ᶠ (v : FinitePlace F) in cofinite, _ at ha hb ⊢
    filter_upwards [ha, hb] with v ha hb hv p hp
    rw [map_add]
    exact (v.adicCompletionIntegers F).toSubring.add_mem (ha hv p hp) (hb hv p hp)
  mul_mem' := by
    intro a b ha hb
    change ∀ᶠ (v : FinitePlace F) in cofinite, _ at ha hb ⊢
    filter_upwards [ha, hb] with v ha hb hv p hp
    rw [map_mul]
    exact (v.adicCompletionIntegers F).toSubring.mul_mem (ha hv p hp) (hb hv p hp)
  algebraMap_mem' := by
    intro c
    change ∀ᶠ (v : FinitePlace F) in cofinite, _
    filter_upwards [(algebraMap F (FiniteAdeles F) c).2] with v hv h p hp
    rw [AlgHom.commutes]
    exact hv

/-- Each generic regular function is integral on every local model point outside
one finite set depending on the function. -/
theorem eventually_uniform_integral (a : Γ(G.X.left, ⊤)) :
    ∀ᶠ v in cofinite, ∀ hv : v ∉ S,
      ∀ p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        p ∈ subgroup F S ⟨v, hv⟩ M →
          G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) p a ∈
            v.adicCompletionIntegers F := by
  have hle : Algebra.adjoin F (Set.range M.genericCoordinate) ≤
      uniformlyIntegralSubalgebra F S M := by
    apply Algebra.adjoin_le
    rintro _ ⟨b, rfl⟩
    change ∀ᶠ (v : FinitePlace F) in cofinite, _
    filter_upwards [] with v hv p hp
    rw [GaloisPoint.coordinates_apply]
    exact (mem_subgroup_iff F S ⟨v, hv⟩ M p).mp hp b
  rw [M.adjoin_range_genericCoordinate_eq_top] at hle
  have ha := hle (show (a : AffineCoordinateRing F G.X) ∈
    (⊤ : Subalgebra F (AffineCoordinateRing F G.X)) from trivial)
  change ∀ᶠ (v : FinitePlace F) in cofinite, _ at ha
  simpa only [GaloisPoint.coordinates_apply] using ha

/-- The model image is eventually contained in the integral subgroup of any
fixed matrix representation. -/
theorem eventually_subgroup_le_representation {N : ℕ}
    (ρ : MatrixRepresentation G (Fin N)) :
    ∀ᶠ v in cofinite, ∀ hv : v ∉ S,
      subgroup F S ⟨v, hv⟩ M ≤ LinearIntegralFamily.subgroup F G ρ v := by
  have h₁ : ∀ᶠ v in cofinite, ∀ i j : Fin N, ∀ hv : v ∉ S,
      ∀ p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        p ∈ subgroup F S ⟨v, hv⟩ M →
          ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) p i j ∈
            v.adicCompletionIntegers F := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    filter_upwards [eventually_uniform_integral F S M
      (ρ.hom.hom.left.appTop (GeneralLinear.entrySection (Fin N) (CommRingCat.of F) i j))]
      with v h hv p hp
    rw [MatrixRepresentation.affineMatrix_apply,
      GeneralLinear.affinePointsEquiv_entry_evaluation,
      GroupScheme.affinePointEvaluation_postcomp]
    exact h hv p hp
  have h₂ : ∀ᶠ v in cofinite, ∀ i j : Fin N, ∀ hv : v ∉ S,
      ∀ p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
        p ∈ subgroup F S ⟨v, hv⟩ M →
          (ρ.affineMatrix (CommAlgCat.of F (FiniteCompletion F v)) p)⁻¹ i j ∈
            v.adicCompletionIntegers F := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    filter_upwards [eventually_uniform_integral F S M
      (ρ.hom.hom.left.appTop
        (GeneralLinear.inverseEntrySection (Fin N) (CommRingCat.of F) i j))]
      with v h hv p hp
    rw [MatrixRepresentation.affineMatrix_apply,
      GeneralLinear.affinePointsEquiv_inverseEntry_evaluation,
      GroupScheme.affinePointEvaluation_postcomp]
    exact h hv p hp
  filter_upwards [h₁, h₂] with v h₁ h₂ hv p hp
  exact (LinearIntegralFamily.mem_subgroup F G ρ v p).mpr
    ⟨fun i j => h₁ i j hv p hp, fun i j => h₂ i j hv p hp⟩

end UniformIntegrality

section FamilyComparison

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)

/-- The fixed finite-type family is eventually contained in every supplied
integral model's local image, uniformly over its points. -/
theorem eventually_fixed_subgroup_le :
    ∀ᶠ v in cofinite, ∀ hv : v ∉ S,
      FiniteTypeIntegralFamily.subgroup F G v ≤ subgroup F S ⟨v, hv⟩ M := by
  have h : ∀ᶠ v in cofinite,
      ∀ a ∈ integralPointTestSet ((S : Set (FinitePlace F)).integer F) M.group.X,
        ∀ p : G.affinePoints (CommAlgCat.of F (FiniteCompletion F v)),
          p ∈ FiniteTypeIntegralFamily.subgroup F G v →
            G.affinePointEvaluation (CommAlgCat.of F (FiniteCompletion F v)) p
              (M.genericCoordinate a) ∈ v.adicCompletionIntegers F :=
    (eventually_all_finset _).mpr (fun a _ =>
      FiniteTypeIntegralFamily.eventually_uniform_integral F G (M.genericCoordinate a))
  filter_upwards [h] with v h hv p hp
  exact (mem_subgroup_iff_testSet F S ⟨v, hv⟩ M p).mpr (fun a ha => h a ha p hp)

/-- Every supplied integral model gives the same subgroup as the chosen
finite-type integral family outside one finite set. -/
theorem eventually_subgroup_eq :
    ∀ᶠ v in cofinite, ∀ hv : v ∉ S,
      FiniteTypeIntegralFamily.subgroup F G v = subgroup F S ⟨v, hv⟩ M := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  filter_upwards [eventually_fixed_subgroup_le F S M,
    eventually_subgroup_le_representation F S M (FiniteTypeIntegralFamily.representation F G)]
    with v h₁ h₂ hv
  exact le_antisymm (h₁ hv) (h₂ hv)

/-- Every actual finite adelic point lies in the local model image at almost all
places, with the original coefficient-map projection. -/
theorem eventually_projection_mem (x : FiniteAdelicGroupPoints F G) :
    ∀ᶠ v in cofinite, ∀ hv : v ∉ S,
      G.affinePointMap
        (CommAlgCat.ofHom
          ({ toRingHom := RestrictedProduct.evalRingHom (FiniteCompletion F) v
             commutes' _ := rfl } : FiniteAdeles F →ₐ[F] FiniteCompletion F v)) x ∈
        subgroup F S ⟨v, hv⟩ M := by
  filter_upwards [FiniteTypeIntegralFamily.eventually_projection_mem F G x,
    eventually_fixed_subgroup_le F S M] with v hmem hle hv
  exact hle hv hmem

end FamilyComparison

end Langlands.Global.IntegralModelCompletions
