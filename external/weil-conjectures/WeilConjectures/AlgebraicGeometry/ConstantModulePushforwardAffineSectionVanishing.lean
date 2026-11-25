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

/-! # Constant-module section vanishing at an inverse limit

Source: Stacks Project, Tags 09Z1 and 09YQ, degree-zero continuity.
(blueprint: lem-weil-pbc-constant-module-affine-section-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

-- The explicit base-change construction needs a larger reduction budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A section on an affine etale test scheme which vanishes at the limit already
vanishes at a later stage. This assertion concerns sections, not geometric germs.

Source: Stacks Project, Tag 09Z1, degree-zero injectivity, using Tag 09YQ.
(blueprint: lem-weil-pbc-constant-module-affine-section-vanishing).

Proof: Form the system E_j = U times_X D_j over U and its cone with vertex
U times_X Y. Pullback preserves this limit because I is cofiltered and hence
connected. The transition maps remain affine. Since U is affine and the structure
maps p_j are qcqs, every E_j is qcqs. Forget the coefficients to abelian groups.
The underlying abelian sheaf of a constant module sheaf is the constant underlying
abelian sheaf: the forgetful functor preserves colimits and finite limits and thus
commutes with sheafification. Identify these constant sheaves with the pullbacks
of the constant abelian sheaf G on U. The canonical comparison maps agree with
unitComparison under these identifications, by naturality of the constant-sheaf
pullback comparison with the adjunction unit and the pushforward composition
comparison. Apply exists_unitComparison_app_eq_zero_of_isLimit to E over U and
the terminal etale object of U. Its hypotheses hold since affine U is
quasi-separated and E_j are qcqs. This gives an arrow g:j -> i where the
restricted underlying abelian section is zero. Faithfulness of coefficient
forgetting reflects this equality as an equality of module sections.
No directed reindexing is needed: the section-continuity theorem already accepts
any small cofiltered category. Zero modules and empty fibre products satisfy the
same argument. -/
theorem exists_constantModulePushforward_affine_section_eq_zero
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
    (U : X.Etale) [IsAffine U.left] (i : I)
    (a : ((lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
      ((constantSheaf (D.obj i).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj M)).obj.obj (op U))
    (ha : (constantModulePushforwardMap Λ M (p i) ν (π.app i) (hπ i)).hom.app
      (op U) a = 0) :
    ∃ (j : I) (g : j ⟶ i),
      (constantModulePushforwardMap Λ M (p i) (p j) (D.map g) (hp g)).hom.app
        (op U) a = 0 := by
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
  obtain ⟨-, hzero⟩ := globalSections_limit_comparison E q c P hP hlimit G
  have hvanish := he (Z := D.obj i) (W := Y) (π.app i) (p i) ν (hπ i)
    (c.π.app i) (by simp [c]) (by simp [c]) a
  rw [ha, map_zero] at hvanish
  obtain ⟨j, g, hg⟩ := hzero i (e (D.obj i) (p i) a) hvanish.symm
  refine ⟨j, g, ?_⟩
  apply (e (D.obj j) (p j)).injective
  have heq := he (Z := D.obj i) (W := D.obj j) (D.map g) (p i) (p j) (hp g)
    (E.map g) (by simp [E]) (by simp [E]) a
  exact heq.trans (by
    simpa only [map_zero, E, q, P, c, G, Functor.const_obj_obj] using hg)

end AlgebraicGeometry.Etale
