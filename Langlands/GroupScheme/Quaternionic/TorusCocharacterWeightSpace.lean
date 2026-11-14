import Langlands.GroupScheme.Quaternionic.CocharacterWeightSpace
import Langlands.GroupScheme.Torus.FiniteMatrixRowWeightCocharacter

/-! # Grouping full-torus row weights in quaternionic cocharacter weight spaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits FiniteMatrixAlgebraTorusWeights

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]
  {I : Type u} [Fintype I] [DecidableEq I]

/-- The full-torus row weight space induced by a split torus of the isometry group. -/
def torusRowWeightSpace (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (m : I → ℤ) : Submodule D (n → D) :=
  rowWeightSpace (i ≫ σ.isometryGroupι q) m

omit [DecidableEq I] in
/-- The published cocharacter equation is the generic inverse-right row equation. -/
theorem mem_cocharacterWeightSpace_iff_rowActionOver (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (c : ℤ) (v : n → D) :
    v ∈ σ.cocharacterWeightSpace q (CommGroupScheme.groupHom ν ≫ i) c ↔
      ∀ (R : CommAlgCat.{u} (CommRingCat.of K))
        (t : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R),
        rowActionOver (i ≫ σ.isometryGroupι q) R
            (t ≫ (CommGroupScheme.groupHom ν).hom.hom)
            (fun a => (1 : R) ⊗ₜ[K] v a) =
          fun a => ((Gm.affineUnitsEquiv (CommRingCat.of K) R t ^ c : Rˣ) : R) ⊗ₜ[K] v a := by
  change (∀ R t, _) ↔ _
  simp only [rowActionOver, isometryAffineUnitsOver, MonoidHom.comp_apply,
    Grp.comp_hom_hom, Category.assoc]
  rfl

/-- Restriction to a cocharacter groups exactly the occurring full-torus row weights
with the specified lattice pairing. -/
theorem cocharacterWeightSpace_eq_iSup_torusRowWeightSpace (q : σ.QuadraticForms n)
    (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ σ.isometryGroup q)
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I))
    (c : ℤ) :
    σ.cocharacterWeightSpace q (CommGroupScheme.groupHom ν ≫ i) c =
      ⨆ m ∈ cocharacterWeightSupport (i ≫ σ.isometryGroupι q) ν c,
        σ.torusRowWeightSpace q i m := by
  apply le_antisymm
  · intro v hv
    exact mem_iSup_rowWeightSpace_of_cocharacter (i ≫ σ.isometryGroupι q) ν c v
      ((σ.mem_cocharacterWeightSpace_iff_rowActionOver q i ν c v).mp hv)
  · refine iSup_le fun m => iSup_le fun hm => ?_
    intro v hv
    apply (σ.mem_cocharacterWeightSpace_iff_rowActionOver q i ν c v).mpr
    intro R t
    have h := rowActionOver_cocharacter_of_mem (i ≫ σ.isometryGroupι q) m hv ν R t
    rw [(mem_cocharacterWeightSupport (i ≫ σ.isometryGroupι q) ν c m).mp hm |>.2] at h
    exact h

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
