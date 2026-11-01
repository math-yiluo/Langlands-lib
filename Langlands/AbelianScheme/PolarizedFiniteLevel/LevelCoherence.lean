import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevel

/-! # Coherence of ordered actual finite-level pullback -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' S'' : Scheme.{u}} {A B : AbelianScheme S} {g n : ℕ}

/-- The actual pulled-back section has the defining first projection of a pullback. -/
theorem pullbackTuple_fst (b : S' ⟶ S) (v : SectionTuple A g n) (i : Fin (2 * g)) :
    (Additive.toMul (pullbackTuple b v i)).val.left ≫ pullback.fst A.X.hom b =
      b ≫ (Additive.toMul (v i)).val.left := by
  have h := (levelBaseChange b A.toGrp (Over.mk (𝟙 S')) n).apply_symm_apply
    (levelRestrict A.toGrp (Over.homMk b (by simp)) n (v i))
  exact congrArg (fun x => (Additive.toMul x).val.left) h

/-- Ordered-section pullback commutes with every actual abelian-scheme homomorphism. -/
theorem pullbackTuple_map (b : S' ⟶ S) (f : A ⟶ B) (v : SectionTuple A g n) :
    mapTuple ((baseChange b).map f) (pullbackTuple b v) =
      pullbackTuple b (mapTuple f v) := by
  funext i
  apply (levelBaseChange b B.toGrp (Over.mk (𝟙 S')) n).injective
  unfold mapTuple
  erw [levelBaseChange_map b (Over.mk (𝟙 S')) (groupHom f) n (pullbackTuple b v i)]
  unfold pullbackTuple
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  apply toSection_injective B.toGrp ((Over.map b).obj (Over.mk (𝟙 S'))) n
  exact Category.assoc (Over.homMk b (by simp) :
      (Over.map b).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S))
    (Additive.toMul (v i)).val (groupHom f).hom.hom

/-- Identity pullback preserves each ordered section through the canonical comparison. -/
theorem pullbackTuple_id (v : SectionTuple A g n) :
    mapTuple (baseChangeIdIso A).hom (pullbackTuple (𝟙 S) v) = v := by
  funext i
  apply toSection_injective A.toGrp (Over.mk (𝟙 S)) n
  apply Over.OverMorphism.ext
  change (Additive.toMul (pullbackTuple (𝟙 S) v i)).val.left ≫
    (GroupScheme.baseChangeIdIso A.toGrp).hom.hom.hom.left =
      (Additive.toMul (v i)).val.left
  rw [GroupScheme.baseChangeIdIso_hom_left, pullbackTuple_fst, Category.id_comp]

/-- Successive ordered-section pullback agrees with direct pullback through
the canonical direct-to-successive abelian-scheme comparison. -/
theorem pullbackTuple_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (v : SectionTuple A g n) :
    mapTuple (baseChangeCompIso b c A).hom (pullbackTuple (c ≫ b) v) =
      pullbackTuple c (pullbackTuple b v) := by
  funext i
  apply (levelIsoLinear (baseChangeCompIso b c A).symm (Over.mk (𝟙 S'')) n).injective
  change (levelIsoLinear (baseChangeCompIso b c A) (Over.mk (𝟙 S'')) n).symm
      ((levelIsoLinear (baseChangeCompIso b c A) (Over.mk (𝟙 S'')) n)
        (pullbackTuple (c ≫ b) v i)) =
    levelIsoLinear (baseChangeCompIso b c A).symm (Over.mk (𝟙 S'')) n
      (pullbackTuple c (pullbackTuple b v) i)
  rw [LinearEquiv.symm_apply_apply]
  apply toSection_injective ((baseChange (c ≫ b)).obj A).toGrp (Over.mk (𝟙 S'')) n
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (Additive.toMul (pullbackTuple (c ≫ b) v i)).val.left ≫
      pullback.fst A.X.hom (c ≫ b) =
    ((Additive.toMul (pullbackTuple c (pullbackTuple b v) i)).val.left ≫
      (GroupScheme.baseChangeCompIso b c A.toGrp).inv.hom.hom.left) ≫
        pullback.fst A.X.hom (c ≫ b)
    rw [Category.assoc, GroupScheme.baseChangeCompIso_inv_fst,
      pullbackTuple_fst, ← Category.assoc]
    erw [pullbackTuple_fst c (pullbackTuple b v) i]
    simp only [Category.assoc]
    erw [pullbackTuple_fst b v i]
  · exact ((Additive.toMul (pullbackTuple (c ≫ b) v i)).val.w).trans
      ((Additive.toMul (levelIsoLinear (baseChangeCompIso b c A).symm
        (Over.mk (𝟙 S'')) n (pullbackTuple c (pullbackTuple b v) i))).val.w).symm

end Langlands.AbelianScheme.PolarizedFiniteLevel
