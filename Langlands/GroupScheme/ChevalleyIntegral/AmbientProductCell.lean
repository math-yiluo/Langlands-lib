import Langlands.GroupScheme.ChevalleyIntegral.IntegralProductEmbedding
import Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability
import Langlands.GroupScheme.Dynamic.BaseTripleCell
import Langlands.GroupScheme.ImageGenerationSubgroup
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Chevalley product parameters in the ambient matrix cell -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

/-- Inversion negates the weights of the diagonal cocharacter over any ring. -/
theorem inv_comp_diagonalCocharacter_overRing
    (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ) :
    CommGroupScheme.groupHom (Gm.powerHom (Spec R) (-1)) ≫ diagonalCocharacter n R e =
      diagonalCocharacter n R (-e) := by
  refine hom_ext_points fun T x => ?_
  apply (pointsEquiv n R T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, Gm.powerHom_apply, Gm.comp_zsmul_id,
    pointsEquiv_diagonalCocharacter, pointsEquiv_diagonalCocharacter, map_zpow,
    _root_.zpow_neg_one]
  ext i j
  simp only [coe_diagonalUnits, Matrix.diagonal_apply, Pi.neg_apply, _root_.inv_zpow']

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  [DecidableEq J] (R : CommRingCat.{u})

omit [DecidableEq J] in
/-- Every ordered product of positive roots is block unipotent for the height weights. -/
theorem opmGL_mem_blockUnipotent {A : Type u} [CommRing A] (l : List J)
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) (c : J → A) :
    D.opmGL l c ∈ GeneralLinear.blockUnipotentSubgroup A D.ellWeights := by
  have h := D.isSUnip_opm l hpos l (fun _ hj => hj) c
  intro p q hpq
  rw [D.coe_opmGL]
  by_cases heq : p = q
  · subst heq
    exact (h.1 p).trans (Matrix.one_apply_eq p).symm
  · rw [Matrix.one_apply_ne heq]
    by_contra hne
    have hlt := (h.2 p q heq hne).2
    rw [map_sub] at hlt
    change D.ℓ (D.wt p) ≤ D.ℓ (D.wt q) at hpq
    omega

/-- The universal ordered-product point belongs to the ambient block unipotent functor. -/
theorem orderedRootMapOver_mem_blockUnipotent (l : List J)
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    D.orderedRootMapOver R l ∈
      (GeneralLinear.blockUnipotent (Fin D.n) R D.ellWeights).carrier
        (D.orderedRootSpace R l) := by
  change GeneralLinear.pointsEquiv (Fin D.n) R (D.orderedRootSpace R l)
    (D.orderedRootMapOver R l) ∈
      GeneralLinear.blockUnipotentSubgroup Γ((D.orderedRootSpace R l).left, ⊤) D.ellWeights
  rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv]
  have hm : GeneralLinear.affinePointsEquiv (Fin D.n) R (D.orderedRootAlgebra R l)
      (D.orderedRootMapOver R l) = D.opmGL l (D.orderedRootVariables R l) := by
    rw [orderedRootMapOver, GeneralLinear.affinePointsEquiv_map, orderedRootClassify,
      CommAlgCat.hom_ofHom, GeneralLinear.point_classify]
  rw [hm]
  exact GeneralLinear.map_mem_blockUnipotentSubgroup _ _ (D.opmGL_mem_blockUnipotent l hpos _)

private theorem exists_orderedRootToBlock (l : List J)
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    ∃ f : D.orderedRootSpace R l ⟶
        (GeneralLinear.blockUnipotentScheme (Fin D.n) R D.ellWeights).X,
      f ≫ (GeneralLinear.blockUnipotentHom (Fin D.n) R D.ellWeights).hom.hom =
        D.orderedRootMapOver R l := by
  apply SubgroupFunctor.mem_range.mp
  rw [(GeneralLinear.isRepresentedBy_blockUnipotent (Fin D.n) R D.ellWeights).2]
  exact D.orderedRootMapOver_mem_blockUnipotent R l hpos

/-- The ordered root product factored through the ambient block unipotent scheme. -/
def orderedRootToBlock (l : List J) (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    D.orderedRootSpace R l ⟶
      (GeneralLinear.blockUnipotentScheme (Fin D.n) R D.ellWeights).X :=
  (D.exists_orderedRootToBlock R l hpos).choose

@[simp] theorem orderedRootToBlock_comp (l : List J)
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    D.orderedRootToBlock R l hpos ≫
        (GeneralLinear.blockUnipotentHom (Fin D.n) R D.ellWeights).hom.hom =
      D.orderedRootMapOver R l :=
  (D.exists_orderedRootToBlock R l hpos).choose_spec

/-- The factor into the block unipotent scheme is itself a closed immersion. -/
theorem isClosedImmersion_orderedRootToBlock (l : List J) (hnd : l.Nodup)
    (hsort : l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hpos : ∀ j ∈ l, 0 < D.ℓ (P.root j)) :
    IsClosedImmersion (D.orderedRootToBlock R l hpos).left := by
  have : IsClosedImmersion ((D.orderedRootToBlock R l hpos).left ≫
      (GeneralLinear.blockUnipotentHom (Fin D.n) R D.ellWeights).hom.hom.left) := by
    rw [← Over.comp_left, D.orderedRootToBlock_comp R l hpos]
    exact D.isClosedImmersion_orderedRootMapOver R l hnd hsort hpos
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (D.orderedRootToBlock R l hpos).left
    (GeneralLinear.blockUnipotentHom (Fin D.n) R D.ellWeights).hom.hom.left

omit [DecidableEq J] in
/-- The full-lattice torus lies in the block Levi subgroup on every test scheme. -/
theorem torusToGLOver_mem_blockLevi :
    (D.torusToGLOver R).hom.hom ∈
      (GeneralLinear.blockLevi (Fin D.n) R D.ellWeights).carrier (TR (X := X) R).toGrp.X := by
  rw [GeneralLinear.mem_blockLevi]
  have ht := D.pointsEquiv_torusToGLOver R (TR (X := X) R).toGrp.X (𝟙 _)
  rw [Category.id_comp] at ht
  rw [ht]
  intro p q hpq
  rw [coe_torusHom, Matrix.diagonal_apply_ne]
  exact fun h => hpq (congrArg D.ellWeights h)

omit [DecidableEq J] in
private theorem exists_torusToBlockLevi :
    ∃ f : (TR (X := X) R).toGrp.X ⟶
        (GeneralLinear.blockLeviScheme (Fin D.n) R D.ellWeights).X,
      f ≫ (GeneralLinear.blockLeviHom (Fin D.n) R D.ellWeights).hom.hom =
        (D.torusToGLOver R).hom.hom := by
  apply SubgroupFunctor.mem_range.mp
  rw [(GeneralLinear.isRepresentedBy_blockLevi (Fin D.n) R D.ellWeights).2]
  exact D.torusToGLOver_mem_blockLevi R

/-- The full-lattice torus factored through the ambient block Levi scheme. -/
def torusToBlockLevi : (TR (X := X) R).toGrp.X ⟶
    (GeneralLinear.blockLeviScheme (Fin D.n) R D.ellWeights).X :=
  (D.exists_torusToBlockLevi R).choose

omit [DecidableEq J] in
@[simp] theorem torusToBlockLevi_comp :
    D.torusToBlockLevi R ≫
        (GeneralLinear.blockLeviHom (Fin D.n) R D.ellWeights).hom.hom =
      (D.torusToGLOver R).hom.hom :=
  (D.exists_torusToBlockLevi R).choose_spec

omit [DecidableEq J] in
/-- The torus factor into the block Levi scheme is a closed immersion. -/
theorem isClosedImmersion_torusToBlockLevi : IsClosedImmersion (D.torusToBlockLevi R).left := by
  have : IsClosedImmersion ((D.torusToBlockLevi R).left ≫
      (GeneralLinear.blockLeviHom (Fin D.n) R D.ellWeights).hom.hom.left) := by
    rw [← Over.comp_left, D.torusToBlockLevi_comp R]
    exact D.isClosedSubgroup_torusToGLOver R
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (D.torusToBlockLevi R).left
    (GeneralLinear.blockLeviHom (Fin D.n) R D.ellWeights).hom.hom.left

/-- The ambient matrix three-factor cell with its negative, Levi and positive factors. -/
def ambientCellSpace : Over (Spec R) :=
  (GeneralLinear.blockUnipotentScheme (Fin D.n) R D.neg.ellWeights).X ⊗
    ((GeneralLinear.blockLeviScheme (Fin D.n) R D.ellWeights).X ⊗
      (GeneralLinear.blockUnipotentScheme (Fin D.n) R D.ellWeights).X)

/-- Multiplication of the three ambient block factors. -/
def ambientCellMap : D.ambientCellSpace R ⟶ (D.GLR R).X :=
  Dynamic.tripleCellMultiplication
    (GeneralLinear.blockUnipotentHom (Fin D.n) R D.neg.ellWeights)
    (GeneralLinear.blockLeviHom (Fin D.n) R D.ellWeights)
    (GeneralLinear.blockUnipotentHom (Fin D.n) R D.ellWeights)

omit [DecidableEq J] in
/-- The ambient matrix cell is open over the arbitrary commutative base ring. -/
theorem isOpenImmersion_ambientCellMap : IsOpenImmersion (D.ambientCellMap R).left := by
  have : Smooth (D.GLR R).X.hom := GeneralLinear.smoothStatement (Fin D.n) R
  apply Dynamic.isOpenImmersion_tripleCellMultiplication_overBase
    (GeneralLinear.diagonalCocharacter (Fin D.n) R D.ellWeights)
  · rw [GeneralLinear.inv_comp_diagonalCocharacter_overRing]
    exact GeneralLinear.isRepresentedBy_unipotent_diagonalCocharacter
      (Fin D.n) R D.neg.ellWeights
  · exact GeneralLinear.isRepresentedBy_centralizer_diagonalCocharacter
      (Fin D.n) R D.ellWeights
  · exact GeneralLinear.isRepresentedBy_unipotent_diagonalCocharacter
      (Fin D.n) R D.ellWeights

/-- The negative-root, torus and positive-root parameter space. -/
def orderedCellSpace (lm lp : List J) : Over (Spec R) :=
  D.neg.orderedRootSpace R lm ⊗ ((TR (X := X) R).toGrp.X ⊗ D.orderedRootSpace R lp)

/-- The parameter product mapped into the three-factor ambient matrix cell. -/
def orderedCellToAmbient (lm lp : List J)
    (hneg : ∀ j ∈ lm, 0 < D.neg.ℓ (P.root j))
    (hpos : ∀ j ∈ lp, 0 < D.ℓ (P.root j)) :
    D.orderedCellSpace R lm lp ⟶ D.ambientCellSpace R :=
  D.neg.orderedRootToBlock R lm hneg ⊗ₘ
    (D.torusToBlockLevi R ⊗ₘ D.orderedRootToBlock R lp hpos)

/-- Distinct height-sorted parameter lists give a closed immersion into the ambient cell. -/
theorem isClosedImmersion_orderedCellToAmbient (lm lp : List J)
    (hmnd : lm.Nodup) (hpnd : lp.Nodup)
    (hmsort : lm.Pairwise (fun a c => D.neg.ℓ (P.root a) ≤ D.neg.ℓ (P.root c)))
    (hpsort : lp.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hneg : ∀ j ∈ lm, 0 < D.neg.ℓ (P.root j))
    (hpos : ∀ j ∈ lp, 0 < D.ℓ (P.root j)) :
    IsClosedImmersion (D.orderedCellToAmbient R lm lp hneg hpos).left := by
  have := D.neg.isClosedImmersion_orderedRootToBlock R lm hmnd hmsort hneg
  have := D.isClosedImmersion_torusToBlockLevi R
  have := D.isClosedImmersion_orderedRootToBlock R lp hpnd hpsort hpos
  have := ImageGeneration.isClosedImmersion_tensorHom_left
    (D.torusToBlockLevi R) (D.orderedRootToBlock R lp hpos)
  exact ImageGeneration.isClosedImmersion_tensorHom_left
    (D.neg.orderedRootToBlock R lm hneg)
    (D.torusToBlockLevi R ⊗ₘ D.orderedRootToBlock R lp hpos)

/-- Multiplication of the ordered negative product, torus and ordered positive product. -/
def orderedCellMap (lm lp : List J) :
    D.orderedCellSpace R lm lp ⟶ (D.GLR R).X :=
  (fst _ _ ≫ D.neg.orderedRootMapOver R lm) *
    ((snd _ _ ≫ fst _ _ ≫ (D.torusToGLOver R).hom.hom) *
      (snd _ _ ≫ snd _ _ ≫ D.orderedRootMapOver R lp))

@[simp] theorem orderedCellToAmbient_comp (lm lp : List J)
    (hneg : ∀ j ∈ lm, 0 < D.neg.ℓ (P.root j))
    (hpos : ∀ j ∈ lp, 0 < D.ℓ (P.root j)) :
    D.orderedCellToAmbient R lm lp hneg hpos ≫ D.ambientCellMap R =
      D.orderedCellMap R lm lp := by
  simp only [orderedCellToAmbient, ambientCellMap, Dynamic.tripleCellMultiplication,
    SubgroupFunctor.cellMultiplication, MonObj.comp_mul, tensorHom_fst_assoc,
    tensorHom_snd_assoc, orderedRootToBlock_comp, torusToBlockLevi_comp]
  rfl

/-- The ordered triple product is a locally closed immersion into the matrix group. -/
theorem isImmersion_orderedCellMap (lm lp : List J)
    (hmnd : lm.Nodup) (hpnd : lp.Nodup)
    (hmsort : lm.Pairwise (fun a c => D.neg.ℓ (P.root a) ≤ D.neg.ℓ (P.root c)))
    (hpsort : lp.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)))
    (hneg : ∀ j ∈ lm, 0 < D.neg.ℓ (P.root j))
    (hpos : ∀ j ∈ lp, 0 < D.ℓ (P.root j)) :
    IsImmersion (D.orderedCellMap R lm lp).left := by
  have := D.isClosedImmersion_orderedCellToAmbient R lm lp hmnd hpnd hmsort hpsort hneg hpos
  have := D.isOpenImmersion_ambientCellMap R
  rw [← D.orderedCellToAmbient_comp R lm lp hneg hpos, Over.comp_left]
  infer_instance

end Langlands.GroupScheme.SplitExistence.ChevalleyData
