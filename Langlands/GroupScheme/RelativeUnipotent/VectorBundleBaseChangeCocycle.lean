import Langlands.GroupScheme.RelativeUnipotent.AffineVectorBundleCocycle
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Vector-bundle cocycles after arbitrary affine base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.GroupScheme.RelativeUnipotent

open Langlands.SchemeModule

variable {S T : Scheme.{u}} (b : T ⟶ S) (M : S.Modules)

/-- Composition of sheaf pullback identifies the two global-section modules. -/
def baseChangeSectionEquiv (Z : Over T) :
    GlobalSections ((Scheme.Modules.pullback Z.hom).obj
      ((Scheme.Modules.pullback b).obj M)) ≃+
      GlobalSections ((Scheme.Modules.pullback ((Over.map b).obj Z).hom).obj M) :=
  AddEquiv.ofBijective
    (((Scheme.Modules.pullbackComp Z.hom b).hom.app M).app ⊤).hom
    (ConcreteCategory.bijective_of_isIso _)

lemma baseChangeSectionEquiv_naturality {Z W : Over T} (a : W ⟶ Z)
    (s : GlobalSections ((Scheme.Modules.pullback Z.hom).obj
      ((Scheme.Modules.pullback b).obj M))) :
    baseChangeSectionEquiv b M W
        (sectionPullback ((Scheme.Modules.pullback b).obj M) a s) =
      sectionPullback M ((Over.map b).map a) (baseChangeSectionEquiv b M Z s) := by
  have hc := RigidifiedModule.compHom_assoc a.left Z.hom b W.hom (Z.hom ≫ b)
    (W.hom ≫ b) (Over.w a) rfl rfl
    (by rw [← Category.assoc, Over.w a]) M
  rw [RigidifiedModule.compHom_rfl, RigidifiedModule.compHom_rfl] at hc
  change (RigidifiedModule.compHom a.left Z.hom W.hom (Over.w a)
      ((Scheme.Modules.pullback b).obj M) ≫
      (Scheme.Modules.pullbackComp W.hom b).hom.app M).app ⊤
        (pullbackSection a.left
          ((Scheme.Modules.pullback Z.hom).obj ((Scheme.Modules.pullback b).obj M)) s) =
    (RigidifiedModule.compHom a.left (Z.hom ≫ b) (W.hom ≫ b) _ M).app ⊤
      (pullbackSection a.left ((Scheme.Modules.pullback (Z.hom ≫ b)).obj M)
        (((Scheme.Modules.pullbackComp Z.hom b).hom.app M).app ⊤ s))
  rw [hc, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  congr 1
  simp only [pullbackSection_eq_sectionPullback]
  exact (Langlands.Scheme.Modules.sectionPullback_naturality a.left
    ((Scheme.Modules.pullbackComp Z.hom b).hom.app M) ⊤ s).symm

lemma baseChangeSectionEquiv_symm_naturality {Z W : Over T} (a : W ⟶ Z)
    (s : GlobalSections
      ((Scheme.Modules.pullback ((Over.map b).obj Z).hom).obj M)) :
    (baseChangeSectionEquiv b M W).symm (sectionPullback M ((Over.map b).map a) s) =
      sectionPullback ((Scheme.Modules.pullback b).obj M) a
        ((baseChangeSectionEquiv b M Z).symm s) := by
  apply (baseChangeSectionEquiv b M W).injective
  rw [AddEquiv.apply_symm_apply, baseChangeSectionEquiv_naturality,
    AddEquiv.apply_symm_apply]

/-- Section coordinates for points of the base change of a represented additive group. -/
def baseChangeSectionPointsEquiv {V : GroupScheme S}
    (e : ∀ Z : Over S, (Z ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback Z.hom).obj M)))
    (Z : Over T) :
    (Z ⟶ ((GroupScheme.baseChange b).obj V).X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback Z.hom).obj
        ((Scheme.Modules.pullback b).obj M))) :=
  (baseChangePointsEquiv b V Z).trans
    ((e ((Over.map b).obj Z)).trans
      (AddEquiv.toMultiplicative (baseChangeSectionEquiv b M Z).symm))

lemma baseChangeSectionPointsEquiv_naturality {V : GroupScheme S}
    (e : ∀ Z : Over S, (Z ⟶ V.X) ≃*
      Multiplicative (GlobalSections ((Scheme.Modules.pullback Z.hom).obj M)))
    (he : ∀ (Z W : Over S) (a : W ⟶ Z) (x : Z ⟶ V.X),
      (e W (a ≫ x)).toAdd = sectionPullback M a (e Z x).toAdd)
    {Z W : Over T} (a : W ⟶ Z)
    (x : Z ⟶ ((GroupScheme.baseChange b).obj V).X) :
    (baseChangeSectionPointsEquiv b M e W (a ≫ x)).toAdd =
      sectionPullback ((Scheme.Modules.pullback b).obj M) a
        (baseChangeSectionPointsEquiv b M e Z x).toAdd := by
  change (baseChangeSectionEquiv b M W).symm
      (e ((Over.map b).obj W) (baseChangePointsEquiv b V W (a ≫ x))).toAdd = _
  rw [baseChangePointsEquiv_naturality, he, baseChangeSectionEquiv_symm_naturality]
  rfl

namespace AffineVectorBundleCocycle

/-- Vector-bundle group cocycles vanish after every base change to an affine scheme. -/
theorem cocycle_isTrivial_baseChange [IsAffine T] {V : GroupScheme S}
    (hV : IsVectorBundleAdditive V) {U : Over T}
    [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange b).obj V) U) : ξ.IsTrivial := by
  obtain ⟨_, _, M, ⟨q, hq, _⟩, e, he⟩ := hV
  let := hq
  let : M.IsLocallyFree := q.isLocallyFree
  let e' := baseChangeSectionPointsEquiv b M e
  let N := (Scheme.Modules.pullback b).obj M
  have he' : ∀ (Z W : Over T) (a : W ⟶ Z)
      (x : Z ⟶ ((GroupScheme.baseChange b).obj V).X),
      (e' W (a ≫ x)).toAdd = sectionPullback N a (e' Z x).toAdd :=
    fun _ _ a x => baseChangeSectionPointsEquiv_naturality b M e he a x
  let α : SectionCocycle N U :=
    { toFun := fun a c => (e' _ (ξ.toFun a c)).toAdd
      naturality := fun t a c => by
        rw [ξ.naturality]
        exact he' _ _ t _
      cocycle := fun a c d => by
        rw [ξ.cocycle a c d, map_mul, toAdd_mul] }
  obtain ⟨β, hβ⟩ := α.exists_coboundary N
  refine ⟨(e' U).symm (Multiplicative.ofAdd β), fun {Z} a c => ?_⟩
  apply (e' Z).injective
  apply Multiplicative.toAdd.injective
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
    he', he', MulEquiv.apply_symm_apply, toAdd_ofAdd, ← sub_eq_add_neg]
  exact hβ a c

end AffineVectorBundleCocycle

end Langlands.GroupScheme.RelativeUnipotent
