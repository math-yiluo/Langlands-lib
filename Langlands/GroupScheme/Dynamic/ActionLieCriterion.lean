import Langlands.GroupScheme.AutomorphicAction.SemidirectDynamic
import Langlands.GroupScheme.Dynamic.LieStatement
import Langlands.GroupScheme.Rational.ActionWeightFunctoriality
import Langlands.GroupScheme.MultiplicativeGeometry

/-! # Positive Lie weights of arbitrary multiplicative-group actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

open RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)

/-- The intrinsic sum of all strictly positive weights of an actual Gm-action. -/
def positiveWeightSpan : Submodule k (Additive (lieKernel G k)) :=
  ⨆ n : ℕ, actionWeightSpace a (Gm.powerHom _ (n + 1))

private instance gm_affine :
    IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
  isSplitTorus_gm.isAffineHom

omit [IsAffineHom G.X.hom] in
private theorem restrict_identity :
    a.restrict (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp) = a := by
  apply ext_act
  intro T t g
  simp only [restrict_act, Grp.id_hom_hom, Category.comp_id]

omit [IsAffineHom G.X.hom] in
private theorem inl_equivariant :
    a.IsEquivariant (cocharacterAction a.semidirectInr) a.semidirectInl := by
  intro T t g
  simpa only [restrict_identity, Category.id_comp] using
    a.semidirectInl_isEquivariant (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp) t g

omit [IsAffineHom G.X.hom] in
private theorem unipotent_comap :
    a.unipotent = (Dynamic.unipotent a.semidirectInr).comap a.semidirectInl := by
  simpa only [restrict_identity, Category.id_comp] using
    a.semidirect_unipotent_eq_comap (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp)

omit [IsAffineHom G.X.hom] in
private theorem ambient_unipotent_le_range :
    Dynamic.unipotent a.semidirectInr ≤ SubgroupFunctor.range a.semidirectInl := by
  simpa only [Category.id_comp] using
    a.semidirect_unipotent_le_range (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp)

variable [LocallyOfFiniteType G.X.hom]

private instance ambient_locallyOfFiniteType :
    LocallyOfFiniteType a.semidirectProduct.X.hom := by
  change LocallyOfFiniteType
    (pullback.fst G.X.hom (Gm (Spec (CommRingCat.of k))).X.hom ≫ G.X.hom)
  infer_instance

/-- In the semidirect group, every positive adjoint weight is in the
actual tangent image of the normal factor. -/
theorem positive_weightSpace_le_range (hLie : DynamicLieStatement.{u}) (n : ℕ) :
    weightSpace a.semidirectInr (Gm.powerHom _ (n + 1)) ≤
      LinearMap.range (Lie.targetMapLinear a.semidirectInl k) := by
  intro X hX
  rw [← tangentSubmodule_range a.semidirectInl]
  apply a.ambient_unipotent_le_range _
  exact ((hLie k a.semidirectProduct a.semidirectInr X.toMul).2.2).mpr
    ((le_iSup (fun m : ℕ =>
      weightSpace a.semidirectInr (Gm.powerHom _ (m + 1))) n) hX)

/-- The semidirect inclusion maps the entire positive intrinsic weight sum
onto the positive adjoint weight sum in the ambient group. -/
theorem map_positiveWeightSpan (hLie : DynamicLieStatement.{u}) :
    a.positiveWeightSpan.map (Lie.targetMapLinear a.semidirectInl k) =
      ⨆ n : ℕ, weightSpace a.semidirectInr (Gm.powerHom _ (n + 1)) := by
  rw [positiveWeightSpan, Submodule.map_iSup]
  apply iSup_congr
  intro n
  rw [IsEquivariant.map_actionWeightSpace_eq_inf_range (a.inl_equivariant),
    cocharacterAction_eq_conjugation, actionWeightSpace_conjugation]
  exact inf_eq_left.mpr (a.positive_weightSpace_le_range hLie n)

/-- Conditional on the published conjugation Lie criterion, the actual
identity-limit functor of any Gm-action has exactly the strictly positive
intrinsic Lie weights. -/
theorem mem_unipotent_iff_iSup_actionWeightSpace (hLie : DynamicLieStatement.{u})
    (X : lieKernel G k) :
    X.val ∈ a.unipotent.carrier _ ↔
      Additive.ofMul X ∈ ⨆ n : ℕ, actionWeightSpace a (Gm.powerHom _ (n + 1)) := by
  rw [a.unipotent_comap, SubgroupFunctor.mem_comap]
  change (Lie.targetMap a.semidirectInl k X).val ∈
    (Dynamic.unipotent a.semidirectInr).carrier _ ↔ _
  rw [(hLie k a.semidirectProduct a.semidirectInr
    (Lie.targetMap a.semidirectInl k X)).2.2, ← a.map_positiveWeightSpan hLie]
  change Lie.targetMapLinear a.semidirectInl k (Additive.ofMul X) ∈
    a.positiveWeightSpan.map (Lie.targetMapLinear a.semidirectInl k) ↔
      Additive.ofMul X ∈ a.positiveWeightSpan
  constructor
  · rintro ⟨Y, hY, hYX⟩
    exact Lie.targetMapLinear_injective a.semidirectInl k hYX ▸ hY
  · intro hX
    exact ⟨Additive.ofMul X, hX, rfl⟩

/-- The intrinsic tangent submodule of the identity-limit functor is its
positive weight span. -/
theorem tangentSubmodule_unipotent (hLie : DynamicLieStatement.{u}) :
    tangentSubmodule a.unipotent = a.positiveWeightSpan := by
  ext X
  exact a.mem_unipotent_iff_iSup_actionWeightSpace hLie X.toMul

/-- The positive intrinsic weight sum is the exact Lie image of the
all-test identity-limit subgroup functor. -/
theorem hasLieImage_unipotent (hLie : DynamicLieStatement.{u}) :
    HasLieImage a.unipotent a.positiveWeightSpan :=
  (hasLieImage_iff_tangentSubmodule_eq _ _).mpr (a.tangentSubmodule_unipotent hLie)

end Langlands.GroupScheme.AutomorphicAction
