import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Dynamic.BaseChange

/-! # Actual character-orbit root subgroups and arbitrary base change -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B B' : Scheme.{u}} (b : B' ⟶ B)
  {S : CommGroupScheme B} {G : GroupScheme B}
  (i : S.toGrp ⟶ G) (a : characterLattice S)

local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" => characterLattice.baseChange b S a

-- The explicit source type avoids expanding the full pulled-back group object
-- during inference of the product comparison. The map is the published one.
private def tensorComparison (T' : Over B') :
    (Over.map b).obj (T' ⊗ (S_K).X) ≅ (Over.map b).obj T' ⊗ S.X :=
  Dynamic.mapTensorPullbackIso b T' S.X

private theorem tensorComparison_hom_fst (T' : Over B') :
    (tensorComparison b (S := S) T').hom ≫ fst _ S.X =
      (Over.map b).map (fst T' (S_K).X) :=
  Dynamic.mapTensorPullbackIso_hom_fst b T' S.X

attribute [reassoc] tensorComparison_hom_fst

@[reassoc] theorem baseChangePointsEquiv_tensor_snd (T' : Over B') :
    (tensorComparison b (S := S) T').hom ≫ snd _ S.X =
      baseChangePointsEquiv b S.toGrp _ (snd T' (S_K).X) := by
  apply Over.OverMorphism.ext
  rw [tensorComparison, Dynamic.mapTensorPullbackIso_hom_snd_left,
    baseChangePointsEquiv_left]
  rfl

/-- The pulled-back character has the same unit coordinate on every test. -/
theorem characterValue_baseChange (T' : Over B') (s : T' ⟶ (S_K).X) :
    Gm.pointsEquiv B' T' (s ≫ (CommGroupScheme.groupHom a_K).hom.hom) =
      Gm.pointsEquiv B ((Over.map b).obj T')
        (baseChangePointsEquiv b S.toGrp T' s ≫ (CommGroupScheme.groupHom a).hom.hom) := by
  change Gm.pointsEquiv B' T'
    (s ≫ ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom a) ≫
      (Gm.baseChangeIso b).hom).hom.hom) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.baseChangeUnitsEquiv_apply, baseChangePointsEquiv_comp]

/-- Character values also agree as points of the original multiplicative group. -/
theorem baseChangePointsEquiv_character (T' : Over B') (s : T' ⟶ (S_K).X) :
    baseChangePointsEquiv b (Gm B).toGrp T'
      ((s ≫ (CommGroupScheme.groupHom a_K).hom.hom) ≫
        (Gm.baseChangeIso b).inv.hom.hom) =
      baseChangePointsEquiv b S.toGrp T' s ≫ (CommGroupScheme.groupHom a).hom.hom := by
  apply (Gm.pointsEquiv B _).injective
  rw [← Gm.baseChangeUnitsEquiv_apply,
    Gm.baseChangeUnitsEquiv_baseChangeIso_inv, characterValue_baseChange]

private theorem mapTensorPullbackIso_characterToGm (T' : Over B') :
    (Over.map b).map (T' ◁ (CommGroupScheme.groupHom a_K).hom.hom) ≫
      (Gm.mapTensorIso b T').hom =
    (tensorComparison b (S := S) T').hom ≫
      (Over.map b).obj T' ◁ (CommGroupScheme.groupHom a).hom.hom := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, Gm.mapTensorIso,
      Dynamic.mapTensorIso_hom_fst, whiskerLeft_fst,
      tensorComparison_hom_fst, ← Functor.map_comp, whiskerLeft_fst]
  · rw [Category.assoc, Gm.mapTensorIso_hom_snd,
      ← baseChangePointsEquiv_naturality, ← Category.assoc, whiskerLeft_snd,
      baseChangePointsEquiv_character, Category.assoc, whiskerLeft_snd,
      baseChangePointsEquiv_tensor_snd_assoc]

/-- Compatibility of the character parameter and the affine-line comparison. -/
@[reassoc]
theorem mapTensorPullbackIso_character (T' : Over B') :
    (Over.map b).map (T' ◁ ((CommGroupScheme.groupHom a_K).hom.hom ≫
      AffineLine.unitInclusion B')) ≫ (AffineLine.mapTensorIso b T').hom =
    (tensorComparison b (S := S) T').hom ≫
      (Over.map b).obj T' ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
        AffineLine.unitInclusion B) := by
  simp only [whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [Dynamic.mapTensorIso_unitInclusion, ← Category.assoc,
    mapTensorPullbackIso_characterToGm, Category.assoc]

/-- Actual conjugation orbits correspond under the projection formula. -/
theorem baseChangePointsEquiv_orbit {T' : Over B'}
    (x : T' ⟶ ((GroupScheme.baseChange b).obj G).X) :
    baseChangePointsEquiv b G _ (orbit i_K x) =
      (tensorComparison b (S := S) T').hom ≫
        orbit i (baseChangePointsEquiv b G T' x) := by
  have hs : baseChangePointsEquiv b G _
      (snd T' (S_K).X ≫ (i_K).hom.hom) =
      (tensorComparison b (S := S) T').hom ≫
        snd _ S.X ≫ i.hom.hom := by
    rw [baseChangePointsEquiv_comp, ← baseChangePointsEquiv_tensor_snd,
      Category.assoc]
  have hx : baseChangePointsEquiv b G _ (fst T' (S_K).X ≫ x) =
      (tensorComparison b (S := S) T').hom ≫
        fst _ S.X ≫ baseChangePointsEquiv b G T' x := by
    rw [baseChangePointsEquiv_naturality, ← tensorComparison_hom_fst_assoc]
  simp only [orbit, AutomorphicAction.conjugation_act, map_mul, map_inv, hs, hx,
    MonObj.comp_mul, GrpObj.comp_inv]

/-- The actual character-orbit extension condition is preserved and reflected. -/
theorem isOrbitExtension_baseChange_iff {T' : Over B'}
    (x : T' ⟶ ((GroupScheme.baseChange b).obj G).X)
    (e : T' ⊗ AffineLine.scheme B' ⟶ ((GroupScheme.baseChange b).obj G).X) :
    IsOrbitExtension (S := S_K) i_K a_K x e ↔
      IsOrbitExtension i a (baseChangePointsEquiv b G T' x)
        ((AffineLine.mapTensorIso b T').inv ≫ baseChangePointsEquiv b G _ e) := by
  have hι : (Over.map b).map (T' ◁ ((CommGroupScheme.groupHom a_K).hom.hom ≫
      AffineLine.unitInclusion B')) =
      (tensorComparison b (S := S) T').hom ≫
        (Over.map b).obj T' ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
          AffineLine.unitInclusion B) ≫ (AffineLine.mapTensorIso b T').inv := by
    rw [← mapTensorPullbackIso_character_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [IsOrbitExtension, IsOrbitExtension, ← (baseChangePointsEquiv b G _).injective.eq_iff,
    baseChangePointsEquiv_naturality, baseChangePointsEquiv_orbit, hι,
    Category.assoc, Category.assoc, cancel_epi]

/-- The intrinsic relative root subgroup functor commutes with arbitrary base change. -/
theorem subgroup_baseChange :
    subgroup (S := S_K) i_K a_K = (subgroup i a).baseChange b := by
  ext T' x
  rw [SubgroupFunctor.mem_baseChange, mem_subgroup, mem_subgroup]
  constructor
  · rintro ⟨e, he, he0⟩
    refine ⟨_, (isOrbitExtension_baseChange_iff b i a x e).mp he, ?_⟩
    rw [← Dynamic.baseChangePointsEquiv_evalZero, he0, map_one]
  · rintro ⟨e, he, he0⟩
    refine ⟨(baseChangePointsEquiv b G _).symm ((AffineLine.mapTensorIso b T').hom ≫ e),
      (isOrbitExtension_baseChange_iff b i a x _).mpr ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply, Iso.inv_hom_id_assoc]
    · apply (baseChangePointsEquiv b G T').injective
      rw [Dynamic.baseChangePointsEquiv_evalZero, MulEquiv.apply_symm_apply,
        Iso.inv_hom_id_assoc, he0, map_one]

/-- Actual root subgroup points over a pulled-back test, compared with the original base. -/
def subgroupPointsBaseChangeEquiv (T' : Over B') :
    (subgroup (S := S_K) i_K a_K).carrier T' ≃*
      (subgroup i a).carrier ((Over.map b).obj T') where
  toFun x := ⟨baseChangePointsEquiv b G T' x.val, by
    simpa only [subgroup_baseChange, SubgroupFunctor.mem_baseChange] using x.property⟩
  invFun x := ⟨(baseChangePointsEquiv b G T').symm x.val, by
    rw [subgroup_baseChange, SubgroupFunctor.mem_baseChange, MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((baseChangePointsEquiv b G T').symm_apply_apply x.val)
  right_inv x := Subtype.ext ((baseChangePointsEquiv b G T').apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((baseChangePointsEquiv b G T').map_mul x.val y.val)

end Langlands.GroupScheme.RelativeRoot
