import Langlands.AlgebraicGeometry.DvrStableNormalizationStatement
import Langlands.CategoryTheory.GroupObjectLift
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Group operations on a stable normal model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.DvrStableGroup

open Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsDomain R]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  (M : DvrStableNormalization.Model G.X)

theorem flat_power (n : ℕ) : Flat (DvrStableNormalization.positivePower M.source n).hom := by
  let := M.flat
  induction n with
  | zero => exact M.flat
  | succ n ih =>
    let := ih
    change Flat (pullback.fst _ _ ≫ _)
    infer_instance

/-- The unique lift of a map from a flat normal test scheme. -/
def normalLift (T : Over (Spec (CommRingCat.of R)))
    (hflat : Flat T.hom) (hnormal : HasNormalStalks T.left) (f : T ⟶ G.X) :
    T ⟶ M.source :=
  Classical.choose ((M.normal_lift T hflat hnormal).surjective f)

@[reassoc]
theorem normalLift_fac (T : Over (Spec (CommRingCat.of R)))
    (hflat : Flat T.hom) (hnormal : HasNormalStalks T.left) (f : T ⟶ G.X) :
    normalLift G M T hflat hnormal f ≫ M.map = f :=
  Classical.choose_spec ((M.normal_lift T hflat hnormal).surjective f)

variable [IsDiscreteValuationRing R]

/-- The identity operation lifted from the DVR base. -/
def one : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ M.source :=
  normalLift G M _ (by change Flat (𝟙 _); infer_instance)
    (valuation_spec_hasNormalStalks (CommRingCat.of R)) η[G.X]

/-- The multiplication lifted from the normal square. -/
def mul : M.source ⊗ M.source ⟶ M.source :=
  normalLift G M _ (flat_power G M 1) (M.normal_powers 1)
    ((M.map ⊗ₘ M.map) ≫ μ[G.X])

/-- The inverse lifted from the normal source. -/
def inv : M.source ⟶ M.source :=
  normalLift G M _ M.flat (M.normal_powers 0) (M.map ≫ ι[G.X])

@[reassoc]
theorem one_fac : one G M ≫ M.map = η[G.X] :=
  normalLift_fac G M _ _ _ _

omit [IsDiscreteValuationRing R] in
@[reassoc]
theorem mul_fac : mul G M ≫ M.map = (M.map ⊗ₘ M.map) ≫ μ[G.X] :=
  normalLift_fac G M _ _ _ _

omit [IsDiscreteValuationRing R] in
@[reassoc]
theorem inv_fac : inv G M ≫ M.map = M.map ≫ ι[G.X] :=
  normalLift_fac G M _ _ _ _

/-- The actual group structure on the normal model. -/
@[instance_reducible]
def grpObj : GrpObj M.source :=
  Langlands.CategoryTheory.GroupObjectLift.grpObjOfInjective M.map
    (M.normal_lift M.source M.flat (M.normal_powers 0)).injective
    (M.normal_lift _ (flat_power G M 2) (M.normal_powers 2)).injective
    (one G M) (mul G M) (inv G M)
    (one_fac G M) (mul_fac G M) (inv_fac G M)

/-- The model as an actual group scheme. -/
def group : GroupScheme (Spec (CommRingCat.of R)) :=
  { X := M.source, grp := grpObj G M }

/-- Its finite surjective comparison with the original group. -/
def map : group G M ⟶ G :=
  Grp.homMk'' M.map (one_fac G M) (mul_fac G M)

@[simp]
theorem map_hom : (map G M).hom.hom = M.map := rfl


/-- The model group is smooth by flatness and geometric reducedness of its group fibres. -/
theorem smooth [LocallyOfFiniteType G.X.hom] : Smooth (group G M).X.hom := by
  let := M.finite
  have hft : LocallyOfFiniteType M.source.hom := by
    rw [← M.map.w]
    infer_instance
  let := M.flat
  let := M.geometricallyReduced
  let : GrpObj (Over.mk M.source.hom) := grpObj G M
  change Smooth M.source.hom
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  let : GrpObj (Over.mk (pullback.snd M.source.hom
      ((Spec (CommRingCat.of R)).fromSpecResidueField y))) :=
    Over.grpObjMkPullbackSnd
  change Smooth (pullback.snd M.source.hom _)
  have : LocallyOfFiniteType
      (pullback.snd M.source.hom ((Spec (CommRingCat.of R)).fromSpecResidueField y)) :=
    MorphismProperty.pullback_snd _ _ hft
  exact AlgebraicGeometry.smooth_of_grpObj _

theorem quasiCompact [QuasiCompact G.X.hom] : QuasiCompact (group G M).X.hom := by
  let := M.finite
  change QuasiCompact M.source.hom
  rw [← M.map.w]
  infer_instance

theorem separated [IsSeparated G.X.hom] : IsSeparated (group G M).X.hom := by
  let := M.finite
  change IsSeparated M.source.hom
  rw [← M.map.w]
  infer_instance

/-- Affineness of a coefficient fibre passes through the finite comparison. -/
theorem affine_baseChange {T : Scheme.{u}} (b : T ⟶ Spec (CommRingCat.of R))
    [IsAffineHom ((baseChange b).obj G).X.hom] :
    IsAffineHom ((baseChange b).obj (group G M)).X.hom := by
  let f := (Over.pullback b).map M.map
  have : IsFinite f.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) b M.map M.finite
  have : IsAffineHom ((Over.pullback b).obj G.X).hom :=
    inferInstanceAs (IsAffineHom ((baseChange b).obj G).X.hom)
  change IsAffineHom ((Over.pullback b).obj M.source).hom
  rw [← f.w]
  infer_instance

theorem finite_map : IsFinite (map G M).hom.hom.left := M.finite

theorem surjective_map : Surjective (map G M).hom.hom.left := M.surjective


end Langlands.GroupScheme.DvrStableGroup
