import Langlands.AlgebraicGeometry.Modules.CechResolution.BaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Pushforward of the augmented inverse-image Čech complex -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  {M : X.Modules} {N : Y.Modules}
  (a : M ⟶ (Scheme.Modules.pushforward g).obj N)

/-- For a full inverse-image open, an invertible coefficient map gives an
invertible actual factor map. -/
lemma isIso_sheafOnPushforward_of_isIso [IsIso a]
    {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W)
    (he : W' = g ⁻¹ᵁ W) :
    IsIso (sheafOnPushforward g a hW) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  rw [sheafOnPushforward_app]
  have hEq : W'.ι ''ᵁ (W'.ι ⁻¹ᵁ (g ⁻¹ᵁ V)) =
      g ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) := by
    rw [image_preimage_eq, image_preimage_eq, Scheme.Hom.preimage_inf, he]
  have hmap : homOfLE (sheafOnPushforward_le g hW V) = eqToHom hEq :=
    Subsingleton.elim _ _
  rw [hmap]
  have ha : IsIso (a.app (W.ι ''ᵁ (W.ι ⁻¹ᵁ V))) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance _
  have hi : IsIso (eqToHom hEq).op := inferInstance
  exact IsIso.comp_isIso' ha (Functor.map_isIso N.presheaf _)

section Cover

attribute [local instance] preservesBiproduct_of_preservesProduct

variable [IsAffineHom g] (𝒰 : X.OrderedAffineCover)

/-- The actual degree map followed by the pushforward-biproduct comparison
is the biproduct of its factor maps. -/
lemma cechTermPushforward_comp_mapBiproduct (p : ℕ) :
    cechTermPushforward g a 𝒰 p ≫
        ((Scheme.Modules.pushforward g).mapBiproduct
          (fun s : 𝒰.Idx p => sheafOn N ((inverseImageCover g 𝒰).inter s))).hom =
      biproduct.map (fun s : 𝒰.Idx p =>
        sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s)) := by
  apply biproduct.hom_ext
  intro s
  have hc :
      ((Scheme.Modules.pushforward g).mapBiproduct
          (fun s : 𝒰.Idx p => sheafOn N ((inverseImageCover g 𝒰).inter s))).hom ≫
        biproduct.π (fun s : 𝒰.Idx p =>
          (Scheme.Modules.pushforward g).obj (sheafOn N ((inverseImageCover g 𝒰).inter s))) s =
      (Scheme.Modules.pushforward g).map
        (biproduct.π (fun s : 𝒰.Idx p =>
          sheafOn N ((inverseImageCover g 𝒰).inter s)) s) :=
    biproduct.lift_π _ _
  have hπ := cechTermPushforward_π g a 𝒰 p s
  have hb := biproduct.map_π
    (fun s : 𝒰.Idx p => sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s)) s
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => cechTermPushforward g a 𝒰 p ≫ k) hc).trans (hπ.trans hb.symm))

/-- An invertible coefficient map makes every degree of the actual
inverse-image-cover comparison invertible. -/
lemma isIso_cechTermPushforward_of_isIso [IsIso a] (p : ℕ) :
    IsIso (cechTermPushforward g a 𝒰 p) := by
  let (s : 𝒰.Idx p) :
      IsIso (sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s)) :=
    isIso_sheafOnPushforward_of_isIso g a _
      (inverseImageCover_inter g 𝒰 s)
  let e := biproduct.mapIso (fun s : 𝒰.Idx p =>
    asIso (sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s)))
  have : IsIso (biproduct.map (fun s : 𝒰.Idx p =>
      sheafOnPushforward g a (inverseImageCover_inter_le g 𝒰 s))) :=
    e.isIso_hom
  have : IsIso (cechTermPushforward g a 𝒰 p ≫
      ((Scheme.Modules.pushforward g).mapBiproduct
        (fun s : 𝒰.Idx p => sheafOn N ((inverseImageCover g 𝒰).inter s))).hom) := by
    rw [cechTermPushforward_comp_mapBiproduct]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.pushforward g).mapBiproduct
      (fun s : 𝒰.Idx p => sheafOn N ((inverseImageCover g 𝒰).inter s))).hom

/-- An invertible coefficient map gives an isomorphism of the specified
Čech complexes. -/
lemma isIso_cechPushforward_of_isIso [IsIso a] :
    IsIso (cechPushforward g a 𝒰) := by
  let (p : ℕ) : IsIso ((cechPushforward g a 𝒰).f p) :=
    isIso_cechTermPushforward_of_isIso g a 𝒰 p
  exact HomologicalComplex.Hom.isIso_of_components _

variable (N)

/-- Čech for the actual pushforward is isomorphic to the pushforward of
Čech for the full inverse-image cover. Its forward map is `cechPushforward`
for the identity of `g_* N`. -/
def cechPushforwardIso :
    cechComplex 𝒰 ((Scheme.Modules.pushforward g).obj N) ≅
      ((Scheme.Modules.pushforward g).mapHomologicalComplex _).obj
        (cechComplex (inverseImageCover g 𝒰) N) := by
  let := isIso_cechPushforward_of_isIso g (𝟙 ((Scheme.Modules.pushforward g).obj N)) 𝒰
  exact asIso (cechPushforward g (𝟙 ((Scheme.Modules.pushforward g).obj N)) 𝒰)

@[simp]
lemma cechPushforwardIso_hom :
    (cechPushforwardIso g N 𝒰).hom =
      cechPushforward g (𝟙 ((Scheme.Modules.pushforward g).obj N)) 𝒰 := rfl

/-- The specified pushforward isomorphism commutes with the actual
augmentations. -/
lemma cechAug_cechPushforwardIso :
    cechAug 𝒰 ((Scheme.Modules.pushforward g).obj N) ≫
        (cechPushforwardIso g N 𝒰).hom =
      mapResolutionAugmentation (Scheme.Modules.pushforward g)
        (cechAug (inverseImageCover g 𝒰) N) := by
  simpa only [cechPushforwardIso_hom, CategoryTheory.Functor.map_id,
    Category.id_comp] using
    cechAug_cechPushforward g (𝟙 ((Scheme.Modules.pushforward g).obj N)) 𝒰

/-- Pushforward of the inverse-image Čech augmentation is a
quasi-isomorphism for every coefficient module sheaf. -/
lemma quasiIso_pushforward_cechAug :
    QuasiIso (mapResolutionAugmentation (Scheme.Modules.pushforward g)
      (cechAug (inverseImageCover g 𝒰) N)) := by
  let := quasiIso_cechAug 𝒰 ((Scheme.Modules.pushforward g).obj N)
  rw [← cechAug_cechPushforwardIso g N 𝒰]
  infer_instance

end Cover

end Langlands.AlgebraicGeometry.Modules.CechResolution
