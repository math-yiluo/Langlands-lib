/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
import WeilConjectures.AlgebraicGeometry.GlobalSectionsLimitComparison
import WeilConjectures.AlgebraicGeometry.ConstantModulePullbackSectionComparison
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Descent of constant-module sections on affine etale test objects

Source: Stacks Project, Tags 09Z1 and 09YQ, degree zero.
(blueprint: lem-weil-pbc-constant-module-limit-affine-section-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Sections on an affine etale test object descend along an inverse limit.

Source: Stacks Project, Tag 09Z1, proof on affine etale objects in degree zero,
and Tag 09YQ, continuity of cohomology.
(blueprint: lem-weil-pbc-constant-module-limit-affine-section-descent).

Proof: Base change the diagram and its limit cone along U.hom, obtaining E_i =
U times_X D_i and L = U times_X Y. Connected limits commute with these pullbacks.
Each E_i is qcqs since its map to the affine scheme U is qcqs, and the transitions
are affine by base change. Let G be the constant abelian sheaf on U with value
M's underlying abelian group. The constant-sheaf pullback isomorphisms identify
its inverse images on E_i and L with the underlying constant module sheaves.
Forgetting coefficients commutes with constant sheafification: the coefficient
forgetful functor is a left adjoint and preserves sheafification, giving the
canonical constantCommuteCompose comparison. Direct image commutes with forgetting
by its sectionwise definition. Evaluation of direct image on U is global sections
on the corresponding pullback; restriction to this etale object gives this
identification. Apply globalSections_limit_comparison to E over U, its limit L,
and G, and take its surjectivity clause. Under these comparisons its legs are
constantModulePushforwardMap evaluated on U: both are the inverse-image adjunction
unit followed by the canonical constant pullback and direct-image composition
comparisons. Naturality of the units and uniqueness of the constant-sheaf left
adjoint comparison identify the maps. The underlying section sets of module
sheaves and their abelian sheaves agree, so the representative and equality
transfer back to module sections. The global-section theorem already handles
arbitrary cofiltered categories. For an empty pullback or the zero module the
only section is zero; a singleton system has an invertible comparison, and no
finite generation of M is used. -/
theorem exists_constantModule_limit_affine_section_rep
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (U : X.Etale) [IsAffine U.left]
    (x : ((lowerStar (ModuleCat.{u + 1} Λ) ν).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op U)) :
    ∃ (i : I) (y : ((lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
      ((constantSheaf (D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op U)),
      (constantModulePushforwardMap Λ M _ _ (π.app i) (hπ i)).hom.app (op U) y = x := by
  classical
  let : IsConnected I := IsCofiltered.isConnected I
  let E : I ⥤ Scheme.{u} :=
    { obj := fun i ↦ pullback U.hom (p i)
      map := fun {i j} f ↦ pullback.map _ _ _ _ (𝟙 U.left) (D.map f) (𝟙 X)
        (by simp) (by simpa using (hp f).symm)
      map_id := fun i ↦ by apply pullback.hom_ext <;> simp
      map_comp := fun f g ↦ by apply pullback.hom_ext <;> simp }
  let c : Cone E :=
    { pt := pullback U.hom ν
      π :=
        { app := fun i ↦ pullback.map _ _ _ _ (𝟙 U.left) (π.app i) (𝟙 X)
            (by simp) (by simpa using (hπ i).symm)
          naturality i j f := by
            apply pullback.hom_ext
            · simp [E]
            · suffices pullback.snd U.hom ν ≫ π.app j =
                  pullback.snd U.hom ν ≫ π.app i ≫ D.map f by
                simpa [E] using this
              have hn := π.naturality f
              change 𝟙 Y ≫ π.app j = π.app i ≫ D.map f at hn
              simpa only [Category.id_comp] using
                congrArg (fun k ↦ pullback.snd U.hom ν ≫ k) hn } }
  let β : E ⟶ D :=
    { app := fun i ↦ pullback.snd U.hom (p i)
      naturality i j f := by simp [E] }
  have hlimit : IsLimit c :=
    isLimitOfIsPullbackOfIsConnected β c (Cone.mk Y π)
      { hom := pullback.snd U.hom ν
        w := fun i ↦ by simp [c, β] }
      (fun i ↦ isPullback_pullback_map U.hom ν (p i) (π.app i) (hπ i)) hc
  let q : E ⟶ (Functor.const I).obj U.left :=
    { app := fun i ↦ pullback.fst U.hom (p i)
      naturality i j f := by simp [E] }
  let P : c.pt ⟶ U.left := pullback.fst U.hom ν
  have hP : ∀ i, P = c.π.app i ≫ q.app i := by intro i; simp [P, c, q]
  let : QuasiSeparatedSpace U.left := inferInstance
  let : ∀ i, CompactSpace (E.obj i) := fun i ↦ by dsimp [E]; infer_instance
  let : ∀ i, QuasiSeparatedSpace (E.obj i) := fun i ↦ by
    dsimp [E]
    exact @quasiSeparatedSpace_of_quasiSeparated _ U.left
      (pullback.fst U.hom (p i)) inferInstance inferInstance
  let : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (E.map f) := fun {i j} f ↦
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_pullback_map U.hom (p i) (p j) (D.map f) (hp f)).flip inferInstance
  let G := (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)
  obtain ⟨e, he⟩ := exists_constantModule_pullback_section_comparison Λ M U
  obtain ⟨hsurj, -⟩ := globalSections_limit_comparison E q c P hP hlimit G
  obtain ⟨i, y, hy⟩ := hsurj (e Y ν x)
  refine ⟨i, (e (D.obj i) (p i)).symm y, ?_⟩
  apply (e Y ν).injective
  have heq := he (Z := D.obj i) (W := Y) (π.app i) (p i) ν (hπ i) (c.π.app i)
    (by simp [c]) (by simp [c]) ((e (D.obj i) (p i)).symm y)
  exact heq.trans (by
    simpa only [AddEquiv.apply_symm_apply, E, q, P, c, G, Functor.const_obj_obj] using hy)

end AlgebraicGeometry.Etale
