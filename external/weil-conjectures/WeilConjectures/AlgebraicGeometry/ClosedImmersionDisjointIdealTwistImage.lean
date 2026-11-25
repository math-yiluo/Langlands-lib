/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.ModulePullbackIdealProductImage
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardCokernel
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-! # Image of restriction on an ideal twist

Source: Stacks Project, Remark 09NW, the formula IB = (I+J)/J, and Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-image).
-/

set_option backward.isDefEq.respectTransparency false in
/-- The ambient restriction of an ideal twist has the target ideal-product image.
No zero-intersection hypothesis is needed for this image calculation.

Source: Stacks Project, Remark 09NW, the formula IB = (I+J)/J, and the
local trivialization argument in Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-image).

Proof: put N = M.tensorPow m and P = (tensorPullback i).obj M tensor-power m.
1. Base change the closed subscheme defined by I along i. The base-change ideal
   image theorem and the kernel-comap formula identify image φ with
   (I.comap i).toModules, compatibly with their inclusions in the structure sheaf.
2. The existing pullback ideal-product image theorem, applied to the
   quasi-coherent invertible module N, identifies the image of the pulled-back
   source inclusion with multiplication by I.comap i on the pullback of N.
3. Tensor the inverse ideal-image identification with e. Naturality of the left
   unitor makes this isomorphism commute with multiplication. Postcomposition
   of Step 2 by e therefore identifies the image with image μ₁.
4. Naturality of the adjunction unit expresses the original restriction as the
   unit on image μ followed by pushforward of the map in Step 3. The unit is epi
   for a closed immersion, so precomposing with it does not change the image.
5. Closed pushforward preserves cokernels, hence epimorphisms. Apply it to the
   epi-image factorization and the image isomorphism from Step 3. Precomposition
   by the pushed epi and then the pushed isomorphism leaves exactly the image
   of the pushed inclusion image.ι μ₁, as required.
No zero-intersection or injectivity of the pulled-back ideal is used. The
argument includes m = 0, the zero and unit ideals, and empty schemes. -/
theorem closedImmersion_disjointIdeal_twist_image {Y X : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (I : Y.IdealSheafData)
    (M : Y.Modules) [M.IsInvertible] (m : ℕ)
    (e : (tensorPullback i).obj (M.tensorPow m) ≅
      ((tensorPullback i).obj M).tensorPow m) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
    let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
    let μ₁ := image.ι φ ▷ ((tensorPullback i).obj M).tensorPow m ≫
      (λ_ (((tensorPullback i).obj M).tensorPow m)).hom
    imageSubobject (image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫
      (pushforward i).map e.hom) = imageSubobject ((pushforward i).map (image.ι μ₁)) := by
  classical
  dsimp only
  let T := tensorPullback i
  let R := pushforward i
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
  let N := M.tensorPow m
  let P := ((tensorPullback i).obj M).tensorPow m
  let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
    (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
  let μ := I.toModulesι ▷ N ≫ (λ_ N).hom
  let μ₁ := image.ι φ ▷ P ≫ (λ_ P).hom
  let a := image.ι μ
  have hker : (pullback.snd I.subschemeι i).ker = I.comap i := by
    calc
      _ = (pullback.fst i I.subschemeι).ker := by
        rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry I.subschemeι i).hom
          (pullback.fst i I.subschemeι), pullbackSymmetry_hom_comp_fst]
      _ = I.subschemeι.ker.comap i :=
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion I.subschemeι i
      _ = I.comap i := congrArg (fun K ↦ K.comap i) I.ker_subschemeι
  have himg : Subobject.mk (image.ι φ) = Subobject.mk (I.comap i).toModulesι := by
    have h := (closedSubscheme_baseChange_ideal_image I.subschemeι i).2
    rw [hker, I.ker_subschemeι] at h
    change imageSubobject φ = _
    simpa only [φ, adj, Adjunction.homEquiv_naturality_left_symm] using h.symm
  let k := Subobject.isoOfMkEqMk (image.ι φ) (I.comap i).toModulesι himg
  have hk : k.hom ≫ (I.comap i).toModulesι = image.ι φ := by simp [k]
  let b := k.symm ⊗ᵢ e
  let ν := (I.comap i).toModulesι ▷ T.obj N ≫ (λ_ (T.obj N)).hom
  have hb : b.hom ≫ μ₁ = ν ≫ e.hom := by
    change (k.inv ⊗ₘ e.hom) ≫ (image.ι φ ▷ P ≫ (λ_ P).hom) = _
    have hk' : k.inv ≫ image.ι φ = (I.comap i).toModulesι := by
      rw [← hk, Iso.inv_hom_id_assoc]
    rw [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← comp_whiskerRight_assoc, hk']
    change (I.comap i).toModulesι ▷ T.obj N ≫
      (𝟙_ X.Modules) ◁ e.hom ≫ (λ_ P).hom = _
    rw [leftUnitor_naturality]
    simp only [ν, Category.assoc]
  have hp : imageSubobject (T.map a) = imageSubobject ν := by
    simpa only [T, a, μ, ν, Scheme.idealModuleProductι, imageSubobject_mono] using
      modulePullbackIdealProductImage i I N inferInstance
  have hpost {A B D : X.Modules} (f : A ⟶ B) (g : B ⟶ D) :
      (Subobject.«exists» g).obj (imageSubobject f) = imageSubobject (f ≫ g) := by
    rw [Subobject.exists_obj_eq_imageSubobject]
    conv_rhs =>
      rw [← imageSubobject_arrow_comp f, Category.assoc, imageSubobject_comp_of_epi]
  have he : imageSubobject (T.map a ≫ e.hom) = imageSubobject μ₁ := by
    have h := congrArg (fun S ↦ (Subobject.«exists» e.hom).obj S) hp
    rw [hpost, hpost] at h
    rw [h, ← hb, imageSubobject_iso_comp]
  let q := Subobject.isoOfMkEqMk (image.ι (T.map a ≫ e.hom)) (image.ι μ₁) he
  have hq : q.hom ≫ image.ι μ₁ = image.ι (T.map a ≫ e.hom) := by simp [q]
  have : ∀ {A B : X.Modules} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) R :=
    fun f ↦ closedImmersion_pushforward_preservesCokernel i f
  have : R.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels R
  have : Epi (adj.unit.app (image μ)) := closedImmersion_unit_epi i (image μ)
  have hnat : a ≫ adj.unit.app N ≫ R.map e.hom =
      adj.unit.app (image μ) ≫ R.map (T.map a ≫ e.hom) := by
    rw [R.map_comp, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ R.map e.hom) (adj.unit.naturality a)
  change imageSubobject (a ≫ adj.unit.app N ≫ R.map e.hom) =
    imageSubobject (R.map (image.ι μ₁))
  rw [hnat, imageSubobject_comp_of_epi]
  conv_lhs => rw [← image.fac (T.map a ≫ e.hom)]
  rw [R.map_comp, imageSubobject_comp_of_epi, ← hq, R.map_comp,
    imageSubobject_iso_comp]

end AlgebraicGeometry.Scheme.Modules
