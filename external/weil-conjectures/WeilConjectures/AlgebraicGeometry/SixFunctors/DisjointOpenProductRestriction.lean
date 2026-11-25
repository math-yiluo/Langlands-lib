/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restriction of a disjoint-open direct-image product

## References

* Stacks Project, Sheaves, Tags 00AL, 00AM and 04TN
* Stacks Project, Sheaves, Tags 00AL and 00AM (disjoint gluing), and Tag 0095 (direct image on
  sections)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def restrictTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : restrictFunctor f ≅ tensorPullback f :=
  restrictFunctorIsoPullback f ≪≫
    ((tensorPullbackSectionAdjunction f).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).symm

private theorem restrict_preservesLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesLimits (restrictFunctor f) := by
  let T := toPresheaf X
  have : ReflectsLimits T := reflectsLimits_of_reflectsIsomorphisms
  have : PreservesLimits (restrictFunctor f ⋙ T) := by
    change PreservesLimits
      ((SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf Y.ringCatSheaf.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op)
    infer_instance
  exact preservesLimits_of_reflects_of_preserves (restrictFunctor f) T

private theorem empty_sections {X : Scheme.{u}} (M : X.Modules)
    (s t : Γ(M, ⊥)) : s = t := by
  let S : TopCat.Sheaf (Type u) X.toTopCat :=
    (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
  exact S.eq_of_locally_eq' (fun i : Empty ↦ ⊥) ⊥
    (fun i ↦ isEmptyElim i) bot_le s t (fun i ↦ isEmptyElim i)

private noncomputable def productSingleIso {C : Type*} [Category C]
    [HasZeroMorphisms C] {ι : Type} (F : ι → C) [HasProduct F] (i : ι)
    (hF : ∀ j, j ≠ i → IsZero (F j)) : (∏ᶜ F) ≅ F i := by
  classical
  refine ⟨Pi.π F i,
    Pi.lift (fun j ↦ if h : i = j then eqToHom (congrArg F h) else 0), ?_, ?_⟩
  · apply Pi.hom_ext
    intro j
    by_cases h : i = j
    · subst j
      simp
    · exact (hF j (Ne.symm h)).eq_of_tgt _ _
  · simp

/-- A direct-image product on pairwise disjoint opens restricts to its single
supported factor. No covering or finiteness assumption is necessary. -/
@[no_expose] noncomputable def disjointOpenProductRestrictIso {X : Scheme.{u}} {ι : Type}
    (U : ι → X.Opens)
    (hdisjoint : ∀ (i j : ι) (x : X), x ∈ U i → x ∈ U j → i = j)
    (F : ι → X.Modules) (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    (tensorPullback V.ι).obj
      (∏ᶜ fun j ↦ (pushforward (U j).ι).obj ((tensorPullback (U j).ι).obj (F j))) ≅
        (tensorPullback V.ι).obj (F i) := by
  classical
  let D (j : ι) :=
    (pushforward (U j).ι).obj ((tensorPullback (U j).ι).obj (F j))
  let R := restrictFunctor V.ι
  have : PreservesLimits R := restrict_preservesLimits V.ι
  have : PreservesLimitsOfSize.{0, 0} R := preservesSmallestLimits_of_preservesLimits R
  have hz (j : ι) (hj : j ≠ i) : IsZero (R.obj (D j)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext s
    have hempty : (U j).ι ⁻¹ᵁ (V.ι ''ᵁ W.unop) = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hxV : x.1 ∈ V := (V.ι_image_le W.unop) hx
      exact False.elim (hj (hdisjoint j i x.1 x.property (hV hxV)))
    change s = 0
    change Γ((tensorPullback (U j).ι).obj (F j),
      (U j).ι ⁻¹ᵁ (V.ι ''ᵁ W.unop)) at s
    have hs : ∀ a b : Γ((tensorPullback (U j).ι).obj (F j),
        (U j).ι ⁻¹ᵁ (V.ι ''ᵁ W.unop)), a = b := by
      rw [hempty]
      exact empty_sections _
    exact hs _ _
  let g := X.homOfLE hV
  let c : restrictFunctor V.ι ≅ restrictFunctor (U i).ι ⋙ restrictFunctor g :=
    restrictFunctorCongr (X.homOfLE_ι hV).symm ≪≫ restrictFunctorComp g (U i).ι
  let ei : R.obj (D i) ≅ R.obj (F i) :=
    c.app (D i) ≪≫
      (restrictFunctor g).mapIso ((restrictFunctorAdjCounitIso (U i).ι).app _ ≪≫
        ((restrictTensorIso (U i).ι).app (F i)).symm) ≪≫ (c.app (F i)).symm
  exact ((restrictTensorIso V.ι).app _).symm ≪≫
    PreservesProduct.iso R D ≪≫ productSingleIso (fun j ↦ R.obj (D j)) i hz ≪≫
      ei ≪≫ (restrictTensorIso V.ι).app (F i)

end AlgebraicGeometry.Scheme.Modules
