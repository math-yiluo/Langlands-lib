import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelEnumeration
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # The actual scheme of ordered torsion tuples in a supplied family -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' : Scheme.{u}} (A : AbelianScheme S) (g n : ℕ)

/-- The finite relative power of the actual multiplication kernel. -/
abbrev torsionTupleScheme : Over S :=
  ∏ᶜ fun _ : Fin (2 * g) =>
    (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X

/-- Maps to the relative power are exactly ordered tuples of actual torsion points. -/
def torsionTupleHomEquiv (T : Over S) :
    (T ⟶ torsionTupleScheme A g n) ≃
      (Fin (2 * g) → Level A.toGrp T n) where
  toFun f i := kernelLevelEquiv A.toGrp T n
    (Additive.ofMul (f ≫ Pi.π _ i))
  invFun v := Pi.lift fun i =>
    Additive.toMul ((kernelLevelEquiv A.toGrp T n).symm (v i))
  left_inv f := by
    apply Pi.hom_ext
    intro i
    simp only [Pi.lift_comp_π, AddEquiv.symm_apply_apply, toMul_ofMul]
  right_inv v := by
    funext i
    simp only [Pi.lift_comp_π, ofMul_toMul, AddEquiv.apply_symm_apply]

/-- The Hom equivalence commutes with every actual map of test schemes over S. -/
theorem torsionTupleHomEquiv_comp {T T' : Over S} (a : T' ⟶ T)
    (f : T ⟶ torsionTupleScheme A g n) (i : Fin (2 * g)) :
    torsionTupleHomEquiv A g n T' (a ≫ f) i =
      levelRestrict A.toGrp a n (torsionTupleHomEquiv A g n T f i) := by
  exact (levelRestrict_kernelLevelEquiv A.toGrp a n
    (Additive.ofMul (f ≫ Pi.π _ i))).symm

/-- Actual global tuples on the pulled-back family are tuples of original
actual torsion points at the specified base map. -/
def sectionTupleBaseChangeEquiv (b : S' ⟶ S) :
    SectionTuple ((baseChange b).obj A) g n ≃
      (Fin (2 * g) → Level A.toGrp (Over.mk b) n) where
  toFun v i := fibreTorsionLinearEquiv A.toGrp b n (v i)
  invFun v i := (fibreTorsionLinearEquiv A.toGrp b n).symm (v i)
  left_inv v := by
    funext i
    exact (fibreTorsionLinearEquiv A.toGrp b n).symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact (fibreTorsionLinearEquiv A.toGrp b n).apply_symm_apply (v i)

/-- The tuple parameter scheme classifies the original ordered global tuples
on the actual base-changed family, on every scheme over S. -/
def torsionTupleSectionEquiv (b : S' ⟶ S) :
    (Over.mk b ⟶ torsionTupleScheme A g n) ≃
      SectionTuple ((baseChange b).obj A) g n :=
  (torsionTupleHomEquiv A g n (Over.mk b)).trans
    (sectionTupleBaseChangeEquiv A g n b).symm

/-- The tautological ordered tuple on the family over the actual parameter scheme. -/
def tautologicalTorsionTuple :
    SectionTuple ((baseChange (torsionTupleScheme A g n).hom).obj A) g n :=
  torsionTupleSectionEquiv A g n (torsionTupleScheme A g n).hom
    (𝟙 (torsionTupleScheme A g n))

/-- Decoding the tautological tuple recovers each actual product projection. -/
@[simp]
theorem sectionTupleBaseChangeEquiv_tautological (i : Fin (2 * g)) :
    sectionTupleBaseChangeEquiv A g n (torsionTupleScheme A g n).hom
      (tautologicalTorsionTuple A g n) i =
      kernelLevelEquiv A.toGrp (torsionTupleScheme A g n) n
        (Additive.ofMul (Pi.π _ i)) := by
  change (sectionTupleBaseChangeEquiv A g n (torsionTupleScheme A g n).hom)
    ((sectionTupleBaseChangeEquiv A g n (torsionTupleScheme A g n).hom).symm
      (torsionTupleHomEquiv A g n (torsionTupleScheme A g n)
        (𝟙 (torsionTupleScheme A g n)))) i = _
  rw [Equiv.apply_symm_apply]
  change kernelLevelEquiv A.toGrp (torsionTupleScheme A g n) n
    (Additive.ofMul (𝟙 _ ≫ Pi.π _ i)) = _
  rw [Category.id_comp]

end Langlands.AbelianScheme.PolarizedFiniteLevel
