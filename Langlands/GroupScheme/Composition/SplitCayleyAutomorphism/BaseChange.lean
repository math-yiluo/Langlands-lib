import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Points
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Multiplicative

/-! # Base change of the split Cayley automorphism group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

variable {K K' : Type u} [Field K] [Field K']

/-- For the split datum the automorphism subgroup of `GL₈(A)` does not depend on the base field
or on the structure map: it is the subgroup of matrices fixing Zorn's unit and preserving Zorn's
product. -/
theorem automorphismSubgroup_split_eq {A : Type u} [CommRing A] (φ : K →+* A) (ψ : K' →+* A) :
    (CayleyDatum.split K).automorphismSubgroup φ =
      (CayleyDatum.split K').automorphismSubgroup ψ := by
  ext g
  rw [mem_automorphismSubgroup_split_iff, mem_automorphismSubgroup_split_iff]

variable (b : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))

/-- On every test scheme over `K'`, the points of the base change of the automorphism group
scheme over `K` are the points of the automorphism group scheme over `K'`: both are the
automorphism matrices of Zorn's algebra over the global sections. -/
def baseChangeModelPointsEquiv (T : Over (Spec (CommRingCat.of K'))) :
    (T ⟶ ((GroupScheme.baseChange b).obj (CayleyDatum.split K).automorphismGroup).X) ≃*
      (T ⟶ (CayleyDatum.split K').automorphismGroup.X) :=
  (((baseChangePointsEquiv b (CayleyDatum.split K).automorphismGroup T).trans
    (pointsEquiv K ((Over.map b).obj T))).trans
      (MulEquiv.subgroupCongr (automorphismSubgroup_split_eq (A := Γ(T.left, ⊤))
        (scalarMap ((Over.map b).obj T)) (scalarMap T)))).trans
    (pointsEquiv K' T).symm

theorem pointsEquiv_baseChangeModelPointsEquiv (T : Over (Spec (CommRingCat.of K')))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (CayleyDatum.split K).automorphismGroup).X) :
    ((pointsEquiv K' T (baseChangeModelPointsEquiv b T x) : GL (Fin 8) Γ(T.left, ⊤)) :
        Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)) =
      (pointsEquiv K ((Over.map b).obj T)
        (baseChangePointsEquiv b (CayleyDatum.split K).automorphismGroup T x)).val.val := by
  rw [baseChangeModelPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem baseChangeModelPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of K'))}
    (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange b).obj (CayleyDatum.split K).automorphismGroup).X) :
    baseChangeModelPointsEquiv b T' (a ≫ x) = a ≫ baseChangeModelPointsEquiv b T x := by
  apply (pointsEquiv K' T').injective
  apply Subtype.ext
  apply Units.ext
  rw [pointsEquiv_baseChangeModelPointsEquiv, pointsEquiv_naturality,
    pointsEquiv_baseChangeModelPointsEquiv, baseChangePointsEquiv_naturality,
    pointsEquiv_naturality]
  rfl

/-- **Base change.** The base change of the automorphism group scheme of Zorn's algebra over `K`
along `Spec K' ⟶ Spec K` is the automorphism group scheme of Zorn's algebra over `K'`. -/
def baseChangeModelIso :
    (GroupScheme.baseChange b).obj (CayleyDatum.split K).automorphismGroup ≅
      (CayleyDatum.split K').automorphismGroup :=
  isoOfPoints (baseChangeModelPointsEquiv b) (baseChangeModelPointsEquiv_naturality b)

/-- The base-change comparison preserves the automorphism matrix on every test scheme. -/
theorem pointsEquiv_baseChangeModelIso_hom (T : Over (Spec (CommRingCat.of K')))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (CayleyDatum.split K).automorphismGroup).X) :
    ((pointsEquiv K' T (x ≫ (baseChangeModelIso b).hom.hom.hom) : GL (Fin 8) Γ(T.left, ⊤)) :
        Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)) =
      (pointsEquiv K ((Over.map b).obj T)
        (baseChangePointsEquiv b (CayleyDatum.split K).automorphismGroup T x)).val.val := by
  rw [baseChangeModelIso, comp_isoOfPoints_hom, pointsEquiv_baseChangeModelPointsEquiv]

end SplitCayley

end Langlands.GroupScheme
