import Langlands.GroupScheme.OddOrthogonalMatrix.ReducedTriviality
import Langlands.GroupScheme.OddOrthogonalMatrix.InvariantSubspaces

/-! # Connected elementary images and fixed-vector stability -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- A constant even orthogonal point viewed in the actual odd group. -/
def evenConstantPoint (T : Over (Spec (CommRingCat.of K)))
    (g : OrthogonalMatrix.orthogonalGroup l K) : T ⟶ (groupScheme l K).X :=
  OrthogonalMatrix.constantPoint T g ≫ (evenMap K).hom.hom

/-- A short subgroup point with parameter one on every test scheme. -/
def shortOnePoint (a : l ⊕ l) (T : Over (Spec (CommRingCat.of K))) :
    T ⟶ (groupScheme l K).X :=
  OrthogonalMatrix.onePoint T ≫ (shortMap K a).hom.hom

/-- The all-test constant-even matrix is exactly scalar extension of its
base-field determinant-corrected block matrix. -/
theorem pointMatrix_evenConstantPoint (T : Over (Spec (CommRingCat.of K)))
    (g : OrthogonalMatrix.orthogonalGroup l K) :
    (pointMatrix K T (evenConstantPoint K T g)).val = (evenBlock g).map (scalarMap T) := by
  rw [pointMatrix_val, evenConstantPoint, Category.assoc, ← Grp.comp_hom_hom,
    evenMap_comp, ambientMatrix_ambientEvenMap, OrthogonalMatrix.pointsEquiv_constantPoint,
    ← evenBlock_map]

/-- The all-test short parameter is one. -/
theorem pointMatrix_shortOnePoint (a : l ⊕ l) (T : Over (Spec (CommRingCat.of K))) :
    (pointMatrix K T (shortOnePoint K a T)).val = shortMatrix a 1 := by
  rw [pointMatrix_val, shortOnePoint, Category.assoc, ← Grp.comp_hom_hom,
    shortMap_comp, ambientMatrix_ambientShortMap, OrthogonalMatrix.onePoint_coord]

/-- An even constant point in the even identity component remains in the odd
identity component. -/
theorem evenConstantPoint_mem (T : Over (Spec (CommRingCat.of K)))
    (g : OrthogonalMatrix.orthogonalGroup l K)
    (hg : OrthogonalMatrix.constantPoint T g ∈
      (SubgroupFunctor.range (identityComponentι
        (OrthogonalMatrix.groupScheme l (CommRingCat.of K)))).carrier T) :
    evenConstantPoint K T g ∈ (SubgroupFunctor.range (identityComponentι (groupScheme l K))).carrier T := by
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp hg
  rw [evenConstantPoint, ← hc, Category.assoc, ← Grp.comp_hom_hom]
  exact SymplecticMatrix.comp_mem_range_identityComponentι _ c

/-- The short parameter-one point belongs to the actual odd identity component. -/
theorem shortOnePoint_mem (a : l ⊕ l) (T : Over (Spec (CommRingCat.of K))) :
    shortOnePoint K a T ∈ (SubgroupFunctor.range (identityComponentι (groupScheme l K))).carrier T :=
  SymplecticMatrix.comp_mem_range_identityComponentι (shortMap K a) _

/-- Every even Levi matrix has determinant one. -/
theorem det_evenLevi (g : GL l K) : (SymplecticMatrix.levi g).det = 1 := by
  rw [SymplecticMatrix.levi, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

/-- The determinant correction is trivial on even Levi generators. -/
theorem evenBlock_levi (g : GL l K) :
    evenBlock (OrthogonalMatrix.leviHom K g) = evenAction (SymplecticMatrix.levi g) := by
  simp only [evenBlock, evenAction, OrthogonalMatrix.coe_leviHom, det_evenLevi]
  congr 1

/-- The determinant correction is trivial on alternating upper generators. -/
theorem evenBlock_upper {A : Matrix l l K} (hA : OrthogonalMatrix.IsAlt A) :
    evenBlock ⟨SymplecticMatrix.upper A, OrthogonalMatrix.upper_mem hA⟩ =
      evenAction (SymplecticMatrix.upper A) := by
  have hd : (SymplecticMatrix.upper A).det = 1 := by
    simp [SymplecticMatrix.upper]
  simp only [evenBlock, evenAction, hd]
  congr 1

/-- The determinant correction is trivial on alternating lower generators. -/
theorem evenBlock_lower {A : Matrix l l K} (hA : OrthogonalMatrix.IsAlt A) :
    evenBlock ⟨SymplecticMatrix.lower A, OrthogonalMatrix.lower_mem hA⟩ =
      evenAction (SymplecticMatrix.lower A) := by
  have hd : (SymplecticMatrix.lower A).det = 1 := by
    simp [SymplecticMatrix.lower]
  simp only [evenBlock, evenAction, hd]
  congr 1

/-- A conjugating family of actual points with prescribed constant matrices
preserves the fixed subspace of any subgroup it normalizes. -/
theorem mulVec_mem_fixedSubmodule {H : GroupScheme (Spec (CommRingCat.of K))}
    (j : H ⟶ groupScheme l K) (g : GL (Index l) K)
    (c : ∀ T : Over (Spec (CommRingCat.of K)), T ⟶ (groupScheme l K).X)
    (hc : ∀ T, (pointMatrix K T (c T)).val = g.val.map (scalarMap T))
    (hN : ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X), ∃ h' : T ⟶ H.X,
      h' ≫ j.hom.hom = (c T)⁻¹ * (h ≫ j.hom.hom) * c T)
    {v : Index l → K} (hv : v ∈ MatrixRepresentation.fixedSubmodule (j ≫ inclusion K)) :
    g.val *ᵥ v ∈ MatrixRepresentation.fixedSubmodule (j ≫ inclusion K) := by
  intro T h
  obtain ⟨h', hh'⟩ := hN T h
  have key := hv T h'
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, hh'] at key
  simp only [_root_.map_mul, _root_.map_inv] at key
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion]
  have hg : (fun i => scalarMap T ((g.val *ᵥ v) i)) =
      (pointMatrix K T (c T)).val *ᵥ (fun i => scalarMap T (v i)) := by
    rw [hc]
    funext i
    rw [RingHom.map_mulVec]
    rfl
  rw [hg]
  set G := pointMatrix K T (c T)
  set M := pointMatrix K T (h ≫ j.hom.hom)
  have he : M.val *ᵥ (G.val *ᵥ (fun i => scalarMap T (v i))) =
      G.val *ᵥ ((G⁻¹ * M * G).val *ᵥ (fun i => scalarMap T (v i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  change M.val *ᵥ (G.val *ᵥ (fun i => scalarMap T (v i))) = G.val *ᵥ (fun i => scalarMap T (v i))
  rw [he, key]

end Langlands.GroupScheme.OddOrthogonalMatrix
