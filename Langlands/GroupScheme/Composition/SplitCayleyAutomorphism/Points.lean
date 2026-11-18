import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Derivations
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Reductive.Basic

/-! # Points and Lie algebra of the split Cayley automorphism group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

variable {K : Type u} [Field K]

local instance isAffineHom_generalLinear :
    IsAffineHom (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom :=
  GeneralLinear.isAffineHom_groupScheme (Fin 8) (CommRingCat.of K)

/-- For the split datum, automorphism matrices are exactly the matrices fixing Zorn's unit and
preserving Zorn's product over the coefficient ring. -/
theorem isAutomorphismMatrix_split_iff {A : Type u} [CommRing A] (φ : K →+* A)
    (g : GL (Fin 8) A) :
    (CayleyDatum.split K).IsAutomorphismMatrix φ g ↔
      IsAutomorphism (g : Matrix (Fin 8) (Fin 8) A).mulVec := by
  unfold CayleyDatum.IsAutomorphismMatrix IsAutomorphism
  simp only [CayleyDatum.split_unitOver, CayleyDatum.split_multiplicationOver, mul_apply]

theorem mem_automorphismSubgroup_split_iff {A : Type u} [CommRing A] (φ : K →+* A)
    (g : GL (Fin 8) A) :
    g ∈ (CayleyDatum.split K).automorphismSubgroup φ ↔
      IsAutomorphism (g : Matrix (Fin 8) (Fin 8) A).mulVec :=
  isAutomorphismMatrix_split_iff φ g

/-! ### Points -/

section Points

variable (K)

/-- Scheme points over every test scheme are automorphism matrices over its global sections. -/
def pointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (CayleyDatum.split K).automorphismGroup.X) ≃*
      (CayleyDatum.split K).automorphismSubgroup (scalarMap T) :=
  Corepresented.pointsEquiv _ _ T

variable {K}

/-- Restriction of scheme points applies the pullback on global sections entrywise. -/
theorem pointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (CayleyDatum.split K).automorphismGroup.X) :
    ((pointsEquiv K T' (a ≫ x) : GL (Fin 8) Γ(T'.left, ⊤)) : Matrix (Fin 8) (Fin 8) _) =
      ((pointsEquiv K T x : GL (Fin 8) Γ(T.left, ⊤)) : Matrix (Fin 8) (Fin 8) _).map
        a.left.appTop.hom := by
  have h := Corepresented.pointsEquiv_naturality _ _ a x
  exact congrArg (fun g : (CayleyDatum.split K).automorphismSubgroup (scalarMap T') =>
    Units.val (g : GL (Fin 8) Γ(T'.left, ⊤))) h

/-- The inclusion into `GL₈` is the inclusion of automorphism matrices on every test scheme. -/
theorem pointsEquiv_inclusion (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (CayleyDatum.split K).automorphismGroup.X) :
    GeneralLinear.pointsEquiv (Fin 8) _ T
        (x ≫ (CayleyDatum.split K).automorphismInclusion.hom.hom) =
      (pointsEquiv K T x : GL (Fin 8) Γ(T.left, ⊤)) :=
  Corepresented.groupSchemeMap_points _ _ _ x

/-- The inclusion of the automorphism group scheme into `GL₈` is a monomorphism. -/
instance mono_automorphismInclusion :
    Mono (CayleyDatum.split K).automorphismInclusion.hom.hom :=
  Corepresented.mono_cutHom _

variable (K) in
/-- Points on affine test schemes are automorphism matrices over the test algebra. -/
def affinePointsEquiv (S : CommAlgCat.{u} (CommRingCat.of K)) :
    ((algSpec (CommRingCat.of K)).obj (op S) ⟶ (CayleyDatum.split K).automorphismGroup.X) ≃*
      (CayleyDatum.split K).automorphismSubgroup (algebraMap (CommRingCat.of K) S) :=
  Corepresented.affinePointsEquiv _ _ S

/-- On affine points, the inclusion into `GL₈` is the inclusion of matrices. -/
theorem affinePointsEquiv_inclusion (S : CommAlgCat.{u} (CommRingCat.of K))
    (f : (algSpec (CommRingCat.of K)).obj (op S) ⟶
      (CayleyDatum.split K).automorphismGroup.X) :
    GeneralLinear.affinePointsEquiv (Fin 8) _ S
        (f ≫ (CayleyDatum.split K).automorphismInclusion.hom.hom) =
      (affinePointsEquiv K S f : GL (Fin 8) S) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

end Points

/-! ### Lie coordinates -/

section Lie

open GeneralLinear.DualNumber

variable {A : Type u} [CommRing A] [Algebra (CommRingCat.of K) A]

/-- The matrix coordinates of the Lie algebra of the automorphism group scheme, through the
inclusion into `GL₈` and the published coordinates of the Lie algebra of `GL₈`. -/
def lieMatrix :
    Additive (lieKernel (CayleyDatum.split K).automorphismGroup A) →ₗ[A]
      Matrix (Fin 8) (Fin 8) A :=
  (pointKernelLinearEquiv (n := Fin 8) (R := CommRingCat.of K) (A := A)).symm.toLinearMap ∘ₗ
    Lie.targetMapLinear (CayleyDatum.split K).automorphismInclusion A

theorem pointKernelLinearEquiv_lieMatrix
    (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup A)) :
    pointKernelLinearEquiv (lieMatrix X) =
      Lie.targetMapLinear (CayleyDatum.split K).automorphismInclusion A X :=
  LinearEquiv.apply_symm_apply _ _

theorem lieMatrix_injective :
    Function.Injective (lieMatrix (K := K) (A := A)) :=
  (pointKernelLinearEquiv (n := Fin 8) (R := CommRingCat.of K) (A := A)).symm.injective.comp
    (Lie.targetMapLinear_injective (CayleyDatum.split K).automorphismInclusion A)

/-- The affine dual-number matrix of an element of the Lie kernel is `1 + εY` for its coordinate
matrix `Y`. -/
theorem affinePointsEquiv_lieKernel
    (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup A)) :
    (((affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber A)) X.toMul.val :
        GL (Fin 8) (DualNumber A))) : Matrix (Fin 8) (Fin 8) (DualNumber A)) =
      1 + epsilonMatrix (lieMatrix X) := by
  have h1 := pointKernelLinearEquiv_lieMatrix X
  have h2 := congrArg (fun x : Additive (lieKernel
      (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)) A) =>
    GeneralLinear.affinePointsEquiv (Fin 8) (CommRingCat.of K)
      (CommAlgCat.of (CommRingCat.of K) (DualNumber A)) x.toMul.val) h1
  simp only [pointKernelLinearEquiv_toMul, pointKernelEquiv_val, lieKernelHomLinear_val] at h2
  have h4 := affinePointsEquiv_inclusion (K := K)
    (CommAlgCat.of (CommRingCat.of K) (DualNumber A)) X.toMul.val
  have h5 := pointUnit_matrix (R := CommRingCat.of K) (lieMatrix X)
  have h6 := h4.symm.trans (h2.symm.trans h5)
  exact congrArg (fun g : GL (Fin 8) (DualNumber A) => g.val) h6

/-- The Lie algebra of the automorphism group consists of derivation matrices killing the
unit. -/
theorem lieMatrix_mulVec_unit_and_isDerivation
    (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup A)) :
    lieMatrix X *ᵥ unit A = 0 ∧ IsDerivation (fun x => lieMatrix X *ᵥ x) := by
  rw [← isAutomorphism_one_add_epsilonMatrix_iff, ← affinePointsEquiv_lieKernel]
  exact (mem_automorphismSubgroup_split_iff _ _).mp
    (affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber A)) X.toMul.val).property

/-- Conversely every derivation matrix killing the unit is the coordinate matrix of an element
of the Lie algebra. -/
theorem exists_lieMatrix_eq (Y : Matrix (Fin 8) (Fin 8) A) (hu : Y *ᵥ unit A = 0)
    (hY : IsDerivation (fun x => Y *ᵥ x)) :
    ∃ X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup A), lieMatrix X = Y := by
  let g0 : GL (Fin 8) (DualNumber A) :=
    GeneralLinear.affinePointsEquiv (Fin 8) (CommRingCat.of K)
      (CommAlgCat.of (CommRingCat.of K) (DualNumber A)) (pointUnit (R := CommRingCat.of K) Y)
  have hg0 : (g0 : Matrix (Fin 8) (Fin 8) (DualNumber A)) = 1 + epsilonMatrix Y := by
    simp only [g0, pointUnit_matrix, matrixUnit_val]
  let g : (CayleyDatum.split K).automorphismSubgroup
      (algebraMap (CommRingCat.of K) (CommAlgCat.of (CommRingCat.of K) (DualNumber A))) :=
    ⟨g0, by
      rw [mem_automorphismSubgroup_split_iff, hg0]
      exact (isAutomorphism_one_add_epsilonMatrix_iff Y).mpr ⟨hu, hY⟩⟩
  let p := (affinePointsEquiv K (CommAlgCat.of (CommRingCat.of K) (DualNumber A))).symm g
  have hp : p ≫ (CayleyDatum.split K).automorphismInclusion.hom.hom =
      (pointUnit (R := CommRingCat.of K) Y : GeneralLinear.DualNumber.AffinePoints
        (Fin 8) (CommRingCat.of K) (DualNumber A)) := by
    apply (GeneralLinear.affinePointsEquiv (Fin 8) (CommRingCat.of K)
      (CommAlgCat.of (CommRingCat.of K) (DualNumber A))).injective
    rw [affinePointsEquiv_inclusion]
    change ((affinePointsEquiv K _ p : GL (Fin 8) (DualNumber A))) = g0
    rw [MulEquiv.apply_symm_apply]
  have hred : Lie.reduction (CayleyDatum.split K).automorphismGroup p = 1 := by
    apply (cancel_mono (CayleyDatum.split K).automorphismInclusion.hom.hom).mp
    rw [MonObj.one_comp]
    have h : Lie.reduction (CayleyDatum.split K).automorphismGroup p ≫
          (CayleyDatum.split K).automorphismInclusion.hom.hom =
        Lie.reduction (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K))
          (p ≫ (CayleyDatum.split K).automorphismInclusion.hom.hom) :=
      Category.assoc _ _ _
    rw [h, hp]
    exact pointReduction_pointUnit Y
  refine ⟨Additive.ofMul ⟨p, hred⟩, ?_⟩
  apply (pointKernelLinearEquiv (n := Fin 8) (R := CommRingCat.of K) (A := A)).injective
  rw [pointKernelLinearEquiv_lieMatrix]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hp

end Lie

end SplitCayley

end Langlands.GroupScheme
