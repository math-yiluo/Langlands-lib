import Langlands.GroupScheme.Rational.RootPointLieNaturality
import Langlands.GroupScheme.Rational.WeightVectorHom
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationProof
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.RootSubgroupTorusProduct

/-! # Intrinsic root-point Lie comparisons under torus restriction -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section WeightCoordinates

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction T.toGrp U} {β : characterLattice T} {n : ℕ}
    {e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))}

/-- Restricting a torus action restricts the weight of the same actual vector
coordinates. -/
theorem IsWeightVectorCoordinates.restrict
    (he : IsWeightVectorCoordinates b β e) (f : S ⟶ T) :
    IsWeightVectorCoordinates (b.restrict (CommGroupScheme.groupHom f)) (f ≫ β) e := by
  refine ⟨he.1, ?_⟩
  intro X s x
  rw [AutomorphicAction.restrict_act, he.2]
  rfl

end WeightCoordinates

section Inclusion

variable {B : Scheme.{u}} {S T : CommGroupScheme B} {G : GroupScheme B}
    (f : S ⟶ T) (j : T.toGrp ⟶ G) (β : characterLattice T)

/-- The actual inclusion from a root group into the root group of the
restricted character. -/
def rootGroupPointsTorusInclusion :
    (subgroup j β).carrier (Over.mk (𝟙 _)) →* (subgroup (CommGroupScheme.groupHom f ≫ j) (f ≫ β)).carrier (Over.mk (𝟙 _)) :=
  Subgroup.inclusion (subgroup_le_subgroup_comp_torusHom f j β (Over.mk (𝟙 _)))

@[simp]
theorem rootGroupPointsTorusInclusion_val (x : (subgroup j β).carrier (Over.mk (𝟙 _))) :
    (rootGroupPointsTorusInclusion f j β x).val = x.val := rfl

variable {U V : GroupScheme B} {q : U ⟶ G} {r : V ⟶ G}
    (hq : (subgroup j β).IsRepresentedBy q)
    (hr : (subgroup (CommGroupScheme.groupHom f ≫ j) (f ≫ β)).IsRepresentedBy r)

/-- The inclusion between actual representatives intertwines their actions
of the smaller torus. -/
theorem subgroupAction_torusInclusion
    (X : Over B) (s : X ⟶ S.X) (x : X ⟶ U.X) :
    ((subgroupAction j β q hq).restrict (CommGroupScheme.groupHom f)).act s x ≫
        (hq.inclusionHom hr (subgroup_le_subgroup_comp_torusHom f j β)).hom.hom =
      (subgroupAction (CommGroupScheme.groupHom f ≫ j) (f ≫ β) r hr).act s
        (x ≫ (hq.inclusionHom hr
          (subgroup_le_subgroup_comp_torusHom f j β)).hom.hom) := by
  let : Mono r.hom.hom := hr.1
  have hcomp :
      (hq.inclusionHom hr (subgroup_le_subgroup_comp_torusHom f j β)).hom.hom ≫
        r.hom.hom = q.hom.hom :=
    congrArg (fun z : U ⟶ G => z.hom.hom)
      (hq.inclusionHom_comp hr (subgroup_le_subgroup_comp_torusHom f j β))
  apply (cancel_mono r.hom.hom).mp
  rw [Category.assoc, hcomp, AutomorphicAction.restrict_act,
    subgroupAction_act_comp, subgroupAction_act_comp]
  simp only [Category.assoc, hcomp]
  rfl

end Inclusion

section LieComparison

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    {β : characterLattice T} (hβ : β ≠ 0) (hres : f ≫ β ≠ 0)
    (hhighβ : HasNoHigherRoots j β)
    (hhigh : HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) (f ≫ β))

/-- Mapping an actual root point to the restricted root group does not
change its intrinsic ambient Lie vector. -/
theorem rootPointLieEquiv_torusInclusion (x : (subgroup j β).carrier (Over.mk (𝟙 _))) :
    (rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) hres hhigh
        (Additive.ofMul (rootGroupPointsTorusInclusion f j β x)) :
        Additive (lieKernel G k)) =
      (rootPointLieEquiv hT j hβ hhighβ (Additive.ofMul x) :
        Additive (lieKernel G k)) := by
  obtain ⟨U, hU, q, hq, heq⟩ := rootPointLieEquiv_exists_representative hT j hβ hhighβ
  obtain ⟨V, hV, r, hr, her⟩ :=
    rootPointLieEquiv_exists_representative hS (CommGroupScheme.groupHom f ≫ j) hres hhigh
  let : IsAffineHom U.X.hom := hU
  let : IsAffineHom V.X.hom := hV
  let ψ := hq.inclusionHom hr (subgroup_le_subgroup_comp_torusHom f j β)
  have hcomp : ψ.hom.hom ≫ r.hom.hom = q.hom.hom :=
    congrArg (fun z : U ⟶ G => z.hom.hom)
      (hq.inclusionHom_comp hr (subgroup_le_subgroup_comp_torusHom f j β))
  let cU := weightVectorCoordinatesOfNoHigherRoots hT j hβ hhighβ hq
  let cV := weightVectorCoordinatesOfNoHigherRoots hS
    (CommGroupScheme.groupHom f ≫ j) hres hhigh hr
  let v := (hq.pointsEquiv _).symm x
  have hv : hq.pointsEquiv _ v = x := (hq.pointsEquiv _).apply_symm_apply _
  have hp : hr.pointsEquiv _ (rationalPoints.map ψ v) =
      rootGroupPointsTorusInclusion f j β (hq.pointsEquiv _ v) := by
    apply Subtype.ext
    change (v ≫ ψ.hom.hom) ≫ r.hom.hom = v ≫ q.hom.hom
    rw [Category.assoc, hcomp]
  have hnat := vectorPointLieEquiv_equivariantHom hS hres
    (cU.2.property.restrict f) cV.2.property ψ
    (subgroupAction_torusInclusion f j β hq hr) (CommAlgCat.of k k)
    (GaloisPointComparison.rationalCoeffEquiv k U v)
  have haff :
      GaloisPointComparison.rationalCoeffEquiv k V (rationalPoints.map ψ v) =
        GaloisPointComparison.rationalCoeffEquiv k U v ≫ ψ.hom.hom :=
    GaloisPointComparison.rationalCoeffEquiv_map k ψ v
  rw [heq, her, ← hv, ← hp,
    representedRootPointLieEquiv_apply, representedRootPointLieEquiv_apply]
  rw [haff, ← hnat]
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [lieKernelTargetLinear_val, Category.assoc, hcomp]
  rfl

end LieComparison

section Products

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- An ordered product of absolute root points with one restricted weight
has intrinsic relative Lie vector equal to the sum of their original vectors. -/
theorem rootPointLieEquiv_rootPointsProduct
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    {α : characterLattice S} (hα : α ≠ 0)
    (hhigh : HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) α)
    {n : ℕ} (a : Fin n → characterLattice T)
    (ha : ∀ l, a l ≠ 0) (hhigha : ∀ l, HasNoHigherRoots j (a l))
    (hres : ∀ l, f ≫ a l = α)
    (X : ∀ l, (subgroup j (a l)).carrier (Over.mk (𝟙 _)))
    (y : (subgroup (CommGroupScheme.groupHom f ≫ j) α).carrier (Over.mk (𝟙 _)))
    (hy : y.val = rootPointsProduct j a (Over.mk (𝟙 _)) X) :
    (rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) hα hhigh
        (Additive.ofMul y) : Additive (lieKernel G k)) =
      ∑ l, (rootPointLieEquiv hT j (ha l) (hhigha l)
        (Additive.ofMul (X l)) : Additive (lieKernel G k)) := by
  let Y : Fin n → (subgroup (CommGroupScheme.groupHom f ≫ j) α).carrier
      (Over.mk (𝟙 _)) := fun l => ⟨(X l).val, by
    have h := (rootGroupPointsTorusInclusion f j (a l) (X l)).property
    change (X l).val ∈ _ at h
    simpa only [hres l] using h⟩
  have hyp : y = (List.ofFn Y).prod := by
    apply Subtype.ext
    change y.val = ((subgroup (CommGroupScheme.groupHom f ≫ j) α).carrier
      (Over.mk (𝟙 _))).subtype (List.ofFn Y).prod
    rw [map_list_prod, List.map_ofFn]
    exact hy
  let Φ := ((weightSpace (CommGroupScheme.groupHom f ≫ j) α).subtype.toAddMonoidHom).comp
    (rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) hα hhigh).toAddMonoidHom
  have hsingle (l : Fin n) :
      Φ (Additive.ofMul (Y l)) =
        (rootPointLieEquiv hT j (ha l) (hhigha l) (Additive.ofMul (X l)) :
          Additive (lieKernel G k)) := by
    have hl := hres l
    subst α
    exact rootPointLieEquiv_torusInclusion hS hT f j (ha l) hα (hhigha l) hhigh (X l)
  change Φ (Additive.ofMul y) = _
  rw [hyp, ofMul_list_prod, map_list_sum, List.map_map, List.map_ofFn]
  simp only [Function.comp_apply, hsingle, List.sum_ofFn]

end Products

end Langlands.GroupScheme.RelativeRoot
