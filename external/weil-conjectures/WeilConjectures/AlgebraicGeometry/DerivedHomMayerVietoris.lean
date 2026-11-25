/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.OpenHomTriangleRealization
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Mayer--Vietoris sequence for derived Hom

Source: Stacks Project, Cohomology, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).

## Main statements

- `derived_hom_mayer_vietoris`: exactness at global and local derived Hom.
- `derivedOpenHomRestriction`: the canonical restriction to a smaller open.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The structure sheaf viewed as a sheaf of rings, as in the module-stalk siblings.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris). -/
abbrev moduleRings (X : RingedSpace.{u}) :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf

private theorem modulePushforward_limits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

/-- Additivity of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_additive (X : RingedSpace.{u}) (U : Opens X) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) U).Additive := by
  exact Functor.Additive.mk (by intros; rfl)

/-- Finite-limit preservation of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_limits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  exact modulePushforward_limits (𝟙 _)

/-- Finite-colimit preservation of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_colimits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) := by
  unfold SheafOfModules.overFunctor
  infer_instance

/-- Additivity of restriction between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_additive (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    (SheafOfModules.overMap.{u} (moduleRings X) i).Additive := by
  exact Functor.Additive.mk (by intros; rfl)

/-- Finite-limit preservation between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_limits (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u} (moduleRings X) i) := by
  exact modulePushforward_limits (Sheaf.pushforwardOverMapIso (moduleRings X) i).inv

/-- Finite-colimit preservation between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_colimits (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u} (moduleRings X) i) := by
  infer_instance

/-- Restrict a morphism on `U` to `W`, transporting along the canonical restriction iso.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris). -/
def derivedOpenHomRestriction (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over W))]
    {E F : DerivedCategory (SheafOfModules.{u} (moduleRings X))}
    (f : (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj E ⟶
      (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj F) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) W).mapDerivedCategory.obj E ⟶
      (SheafOfModules.overFunctor.{u} (moduleRings X) W).mapDerivedCategory.obj F :=
  let A := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let B := SheafOfModules.overMap.{u} (moduleRings X) i
  letI : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  letI : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  let e := Functor.mapDerivedCategoryCompIso A B ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u} (moduleRings X) i)
  e.inv.app E ≫ (SheafOfModules.overMap.{u} (moduleRings X) i).mapDerivedCategory.map f ≫
    e.hom.app F

private theorem derivedOpenHomRestriction_eq (X : RingedSpace.{u})
    {W U : Opens X} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over W))]
    {E F : DerivedCategory (SheafOfModules.{u} (moduleRings X))}
    (f : (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj E ⟶
      (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj F) :
    derivedOpenHomRestriction X i f =
      SheafOfModules.openHomRestriction (moduleRings X) i f := rfl

private theorem hom_exact_of_open_triangle
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {E F A B : C} (a : A ⟶ B) (b : B ⟶ E) (δ : E ⟶ A⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk a b δ ∈ distTriang C)
    {P Q N : Type*} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup N]
    (eB : (B ⟶ F) ≃+ P) (eA : (A ⟶ F) ≃+ Q) (eN : (A⟦(1 : ℤ)⟧ ⟶ F) ≃+ N)
    (r : (E ⟶ F) → P) (d : P → Q)
    (hb : ∀ f, eB (b ≫ f) = r f) (ha : ∀ g, eA (a ≫ g) = d (eB g)) :
    ∃ negExt : N →+ (E ⟶ F), Function.Exact negExt r ∧ Function.Exact r d := by
  have hab : a ≫ b = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ (Pretriangulated.Triangle.mk a b δ) hT
  have hbδ : b ≫ δ = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₂₃ (Pretriangulated.Triangle.mk a b δ) hT
  let negExt : N →+ (E ⟶ F) :=
    { toFun := fun x ↦ δ ≫ eN.symm x
      map_zero' := by simp
      map_add' := by intro x y; simp [Preadditive.comp_add] }
  refine ⟨negExt, ?_, ?_⟩
  · intro f
    constructor
    · intro hf
      have hbf : b ≫ f = 0 := by
        apply eB.injective
        simpa only [hb, map_zero] using hf
      obtain ⟨g, hg⟩ := (Pretriangulated.Triangle.mk a b δ).yoneda_exact₃ hT f hbf
      refine ⟨eN g, ?_⟩
      change δ ≫ eN.symm (eN g) = f
      rw [eN.symm_apply_apply]
      exact hg.symm
    · rintro ⟨x, rfl⟩
      have hzero : b ≫ negExt x = 0 := by
        dsimp [negExt]
        rw [← Category.assoc, hbδ, zero_comp]
      simp only [← hb, hzero, map_zero]
  · intro p
    constructor
    · intro hp
      let g := eB.symm p
      have hag : a ≫ g = 0 := by
        apply eA.injective
        simpa only [ha, g, AddEquiv.apply_symm_apply, map_zero] using hp
      obtain ⟨f, hf⟩ := (Pretriangulated.Triangle.mk a b δ).yoneda_exact₂ hT g hag
      let f' : E ⟶ F := f
      change g = b ≫ f' at hf
      refine ⟨f', ?_⟩
      rw [← hb, ← hf]
      exact eB.apply_symm_apply p
    · rintro ⟨f, rfl⟩
      have hzero : a ≫ b ≫ f = 0 := by
        rw [← Category.assoc, hab, zero_comp]
      calc
        d (r f) = eA (a ≫ b ≫ f) := by rw [← hb, ← ha]
        _ = 0 := by rw [hzero, map_zero]

/-- Mayer--Vietoris exactness at global Hom and at the pair of local Hom groups.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris).

Proof: apply the distinguished Mayer--Vietoris triangle
(`lem-sc-derived-mayer-vietoris-triangle`) to `E`. Contravariant Hom into `F`
gives the long exact sequence (`lem-weil-pbc-hom-out-of-triangle-exact`).
The derived extension-by-zero/restriction adjunction
(`lem-sc-derived-open-shriek-derived-adjunction`) identifies its terms with
Hom on the three opens and global Hom. The preceding term is negative Ext on
the overlap. The first arrow is the pair of restrictions; the next is their
difference, because the triangle's first arrow is the difference of the two
extension-by-zero maps. Thus the sequence is exact at both specified terms. -/
theorem derived_hom_mayer_vietoris
    (X : RingedSpace.{u}) (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over (U ⊓ V)))]
    (E F : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    let R_U := (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory
    let R_V := (SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory
    let R_UV := (SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapDerivedCategory
    ∃ (negExt : (R_UV.obj E ⟶ (R_UV.obj F)⟦(-1 : ℤ)⟧) →+ (E ⟶ F)),
      Function.Exact negExt (fun f => (R_U.map f, R_V.map f)) ∧
      Function.Exact
        (fun f : E ⟶ F => (R_U.map f, R_V.map f))
        (fun p : (R_U.obj E ⟶ R_U.obj F) × (R_V.obj E ⟶ R_V.obj F) =>
          derivedOpenHomRestriction X (homOfLE inf_le_left) p.1 -
            derivedOpenHomRestriction X (homOfLE inf_le_right) p.2) := by
  classical
  -- Bind the witness first so that `rcases` does not generalize its large functor expression.
  have htriangle :=
    SheafOfModules.open_hom_triangle_realization X (moduleRings X) rfl U V hcover E F
  rcases htriangle with ⟨A, B, a, b, δ, hT, eB, eA, eN, hb, ha⟩
  refine hom_exact_of_open_triangle a b δ hT eB eA eN
    (fun f ↦ ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.map f,
      (SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory.map f))
    (fun p ↦ derivedOpenHomRestriction X (homOfLE inf_le_left) p.1 -
      derivedOpenHomRestriction X (homOfLE inf_le_right) p.2) hb ?_
  intro g
  simpa only [derivedOpenHomRestriction_eq] using ha g

end AlgebraicGeometry
