import Langlands.GroupScheme.ChevalleyIntegral.AmbientProductCell
import Langlands.GroupScheme.SplitExistence.NegGroup
import Langlands.GroupScheme.Absolute.TripleCellGeneration
import Langlands.GroupScheme.ImageGenerationDominant

/-! # Field Chevalley cells factor through the ordered parameter product -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  [Fintype J] [DecidableEq J] (k : Type u) [Field k]

/-- The old field coefficient recovery, with codomain the positive parameter algebra. -/
def fieldOrderedRootSection :
    D.orderedRootAlgebra (CommRingCat.of k) D.posList →ₐ[k] D.coordAlg k :=
  MvPolynomial.aeval fun j : {j : J // j ∈ D.posList} =>
    D.retr k (D.univMatrix k : Matrix (Fin D.n) (Fin D.n) (D.coordAlg k)) j

/-- The field coefficient-recovery map to the positive ordered-root parameter space. -/
def fieldOrderedRootRetraction :
    (D.GLk k).X ⟶ D.orderedRootSpace (CommRingCat.of k) D.posList :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (D.fieldOrderedRootSection k)).op

/-- Its ordered-root composite is the published field retraction endomorphism. -/
theorem fieldOrderedRootRetraction_comp :
    D.fieldOrderedRootRetraction k ≫
        D.orderedRootMapOver (CommRingCat.of k) D.posList = D.retrMor k := by
  apply (GeneralLinear.affinePointsEquiv (Fin D.n) (CommRingCat.of k) (D.coordAlg k)).injective
  rw [fieldOrderedRootRetraction, affinePointsEquiv_orderedRootMapOver,
    retrMor, MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [D.coe_opmGL, D.coe_opmGL]
  apply D.opm_congr
  intro j hj
  simp only [CommAlgCat.hom_ofHom, fieldOrderedRootSection, orderedRootVariables,
    dite_eq_left hj, MvPolynomial.aeval_X]

namespace ChevGroup

variable {D k} (G : D.ChevGroup k)

local instance chevAffineHom : IsAffineHom G.H.X.hom := G.affine
local instance chevAffine : IsAffine G.H.X.left := isAffine_of_isAffineHom G.H.X.hom
local instance chevSmooth : Smooth G.H.X.hom := G.smooth
local instance chevConnected : ConnectedSpace G.H.X.left := G.connected

/-- The dynamic positive unipotent subgroup mapped to the ordered root parameters. -/
def unipotentToOrderedRoots :
    (Dynamic.Affine.unipotentScheme G.cochar).X ⟶
      D.orderedRootSpace (CommRingCat.of k) D.posList :=
  (Dynamic.Affine.unipotentHom G.cochar).hom.hom ≫
    G.i.hom.hom ≫ D.fieldOrderedRootRetraction k

/-- The recovered ordered product equals the dynamic positive unipotent inclusion. -/
theorem unipotentToOrderedRoots_comp [P.IsReduced] :
    G.unipotentToOrderedRoots ≫
        D.orderedRootMapOver (CommRingCat.of k) D.posList =
      (Dynamic.Affine.unipotentHom G.cochar).hom.hom ≫ G.i.hom.hom := by
  rw [unipotentToOrderedRoots, Category.assoc, Category.assoc,
    D.fieldOrderedRootRetraction_comp, G.unipotent_retr]

omit [Fintype J] [DecidableEq J] in
/-- The opposite regular cocharacter is obtained by precomposing with inversion. -/
theorem neg_cochar :
    G.neg.cochar =
      CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ G.cochar := by
  apply Grp.hom_ext
  have := G.mono_i
  apply (cancel_mono G.i.hom.hom).mp
  change (G.neg.cochar ≫ G.i).hom.hom =
    ((CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      G.cochar) ≫ G.i).hom.hom
  have hn : G.neg.cochar ≫ G.i =
      GeneralLinear.diagonalCocharacter (Fin D.n) (CommRingCat.of k) D.neg.ellWeights :=
    G.neg.cochar_comp_i
  rw [hn, Category.assoc, G.cochar_comp_i,
    GeneralLinear.inv_comp_diagonalCocharacter_overRing]
  rfl

omit [DecidableEq J] in
private theorem exists_centralizerToTorus [P.IsReduced] [Module.Finite ℤ X] :
    ∃ z : (Dynamic.Affine.centralizerScheme G.cochar).X ⟶ (TR (X := X) (CommRingCat.of k)).toGrp.X,
      z ≫ G.t.hom.hom = (Dynamic.Affine.centralizerHom G.cochar).hom.hom := by
  apply SubgroupFunctor.mem_range.mp
  apply G.centralizer_le
  rw [← (Dynamic.Affine.isRepresentedBy_centralizerHom G.cochar).2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- The dynamic centralizer of the regular cocharacter mapped to the full-lattice torus. -/
def centralizerToTorus [P.IsReduced] [Module.Finite ℤ X] :
    (Dynamic.Affine.centralizerScheme G.cochar).X ⟶ (TR (X := X) (CommRingCat.of k)).toGrp.X :=
  G.exists_centralizerToTorus.choose

omit [DecidableEq J] in
@[simp] theorem centralizerToTorus_comp [P.IsReduced] [Module.Finite ℤ X] :
    G.centralizerToTorus ≫ (D.torusToGLOver (CommRingCat.of k)).hom.hom =
      (Dynamic.Affine.centralizerHom G.cochar).hom.hom ≫ G.i.hom.hom := by
  rw [D.torusToGLOver_eq, ← G.t_comp, Grp.comp_hom_hom, ← Category.assoc,
    centralizerToTorus, G.exists_centralizerToTorus.choose_spec]

/-- The actual intrinsic dynamic triple-cell source in the field Chevalley group. -/
def intrinsicCellSpace : Over (Spec (CommRingCat.of k)) :=
  (Dynamic.Affine.unipotentScheme G.neg.cochar).X ⊗
    ((Dynamic.Affine.centralizerScheme G.cochar).X ⊗
      (Dynamic.Affine.unipotentScheme G.cochar).X)

/-- Multiplication of the negative dynamic unipotent, centralizer, and positive unipotent. -/
def intrinsicCellMap : G.intrinsicCellSpace ⟶ G.H.X :=
  Dynamic.tripleCellMultiplication
    (Dynamic.Affine.unipotentHom G.neg.cochar)
    (Dynamic.Affine.centralizerHom G.cochar)
    (Dynamic.Affine.unipotentHom G.cochar)

omit [Fintype J] [DecidableEq J] in
/-- This intrinsic cell is schematically dense in the field Chevalley group. -/
theorem intrinsicCellMap_schematic :
    IsSchemeTheoreticallyDominant G.intrinsicCellMap.left := by
  apply Dynamic.isSchemeTheoreticallyDominant_tripleCellMultiplication G.cochar
  · rw [← G.neg_cochar]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom G.neg.cochar
  · exact Dynamic.Affine.isRepresentedBy_centralizerHom G.cochar
  · exact Dynamic.Affine.isRepresentedBy_unipotentHom G.cochar

/-- The intrinsic dynamic cell mapped to the ordered product parameters. -/
def intrinsicCellToOrdered [P.IsReduced] [Module.Finite ℤ X] :
    G.intrinsicCellSpace ⟶
      D.orderedCellSpace (CommRingCat.of k) D.neg.posList D.posList :=
  G.neg.unipotentToOrderedRoots ⊗ₘ (G.centralizerToTorus ⊗ₘ G.unipotentToOrderedRoots)

/-- The ordered parameter map reproduces the actual intrinsic cell in matrices. -/
theorem intrinsicCellToOrdered_comp [P.IsReduced] [Module.Finite ℤ X] :
    G.intrinsicCellToOrdered ≫
        D.orderedCellMap (CommRingCat.of k) D.neg.posList D.posList =
      G.intrinsicCellMap ≫ G.i.hom.hom := by
  simp only [intrinsicCellToOrdered, orderedCellMap, intrinsicCellMap,
    Dynamic.tripleCellMultiplication, SubgroupFunctor.cellMultiplication,
    MonObj.comp_mul, MonObj.mul_comp, tensorHom_fst_assoc, tensorHom_snd_assoc,
    Category.assoc, unipotentToOrderedRoots_comp, centralizerToTorus_comp]
  rfl

end ChevGroup

end Langlands.GroupScheme.SplitExistence.ChevalleyData
