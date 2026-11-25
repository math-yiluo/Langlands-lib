/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Topology.RingedModuleSkyscraper

/-!
# Stalks of flat sheaves of modules

Source: Stacks Project, Modules, Lemma 17.17.2 (Tag 05NE), flat sheaf implies flat stalks
(blueprint: lem-pc-flat-sheaf-stalk-flat).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

set_option autoImplicit false

noncomputable section

/- The constant-section calculation below is adapted from the private helpers of
`WeilConjectures.Topology.SkyscraperComplexStalk`. We need its naturality for arbitrary module
morphisms, whereas that module exposes only recovery for an individual complex.
Source: Stacks, Tag 009A (4), and the neighbourhood-colimit description of stalks. -/

/-- Send a vector to the germ of its constant global section. -/
private noncomputable def constantGermAdd (X : RingedSpace.{u}) (x : X)
    (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    M →+ (RingedSpace.moduleStalkFunctor X x).obj (SheafOfModules.ringedModuleSkyscraper X x M) :=
  (TopCat.Presheaf.germ (SheafOfModules.ringedSkyscraperPresheafAb X x M) ⊤ x (by trivial)).hom.comp
    { toFun := fun m _ ↦ m
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- Constant sections have the same germ on every neighbourhood. -/
private theorem constantGermAdd_eq (X : RingedSpace.{u}) (x : X)
    (M : ModuleCat.{u} (X.presheaf.stalk x)) (U : TopologicalSpace.Opens X) (hx : x ∈ U)
    (m : M) :
    constantGermAdd X x M m =
      TopCat.Presheaf.germ (SheafOfModules.ringedSkyscraperPresheafAb X x M)
        U x hx (fun _ ↦ m) := by
  exact (TopCat.Presheaf.germ_res_apply (SheafOfModules.ringedSkyscraperPresheafAb X x M)
    (homOfLE le_top : U ⟶ ⊤) x hx (fun _ ↦ m)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Represent the scalar locally and apply the compatibility of germs with scalar action. -/
private theorem constantGermAdd_linear (X : RingedSpace.{u}) (x : X)
    (M : ModuleCat.{u} (X.presheaf.stalk x)) (r : X.presheaf.stalk x) (m : M) :
    constantGermAdd X x M (r • m) = r • constantGermAdd X x M m := by
  obtain ⟨U, hx, a, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [constantGermAdd_eq X x M U hx, constantGermAdd_eq X x M U hx]
  exact PresheafOfModules.germ_smul (R := X.presheaf)
    (SheafOfModules.ringedModuleSkyscraper X x M).val x U hx a (fun _ ↦ m)

/-- The constant-section germ as a morphism of stalk modules. -/
private noncomputable def constantGerm (X : RingedSpace.{u}) (x : X)
    (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    M ⟶ (RingedSpace.moduleStalkFunctor X x).obj (SheafOfModules.ringedModuleSkyscraper X x M) :=
  ModuleCat.ofHom
    { toFun := constantGermAdd X x M
      map_add' := (constantGermAdd X x M).map_add
      map_smul' := constantGermAdd_linear X x M }

/-- Germ equality detects constant values; every local section is constant on its
subsingleton domain of membership proofs. -/
private theorem constantGerm_bijective (X : RingedSpace.{u}) (x : X)
    (M : ModuleCat.{u} (X.presheaf.stalk x)) :
    Function.Bijective (constantGerm X x M) := by
  constructor
  · intro m n h
    obtain ⟨U, hx, i, j, heq⟩ := TopCat.Presheaf.germ_eq
      (SheafOfModules.ringedSkyscraperPresheafAb X x M) (U := ⊤) (V := ⊤) x
      (by trivial) (by trivial) (fun _ ↦ m) (fun _ ↦ n) h
    exact congrFun heq ⟨hx⟩
  · intro t
    obtain ⟨U, hx, s, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (SheafOfModules.ringedSkyscraperPresheafAb X x M) t
    refine ⟨s ⟨hx⟩, ?_⟩
    change constantGermAdd X x M (s ⟨hx⟩) = _
    rw [constantGermAdd_eq X x M U hx]

/-- Pointwise module maps take constant sections to constant sections. -/
private theorem constantGerm_naturality (X : RingedSpace.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (f : M ⟶ N) :
    constantGerm X x M ≫ (RingedSpace.moduleStalkFunctor X x).map
      ((SheafOfModules.ringedModuleSkyscraperFunctor X x).map f) = f ≫ constantGerm X x N := by
  ext m
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf _).map (SheafOfModules.ringedModuleSkyscraperMap X x f).val)
      (TopCat.Presheaf.germ (SheafOfModules.ringedSkyscraperPresheafAb X x M) ⊤ x (by trivial)
        (fun _ ↦ m)) = _
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- Every stalk of a flat sheaf of modules on a ringed space is flat over the stalk ring.
Source: Stacks Project, Modules, Lemma 17.17.2 (Tag 05NE), implication from sheaf flatness
(blueprint: lem-pc-flat-sheaf-stalk-flat).

Proof:
1. Use Mathlib's injectivity criterion for `Module.Flat`: fix an injective linear map
   `f : M →ₗ N` of stalk modules. The skyscraper map is monic, by pointwise injectivity
   on sections (`def-pc-ringed-module-skyscraper`).
2. By `def-pc-flat-sheaf-modules`, right tensoring with `F` preserves finite limits,
   hence preserves this monomorphism.
3. Apply `lem-weil-pbc-module-stalk-exact` to the exact short complex with first map
   zero and second map the tensored skyscraper map. Its stalk is exact, so the stalk
   of the tensored map is again monic.
4. Naturality of `lem-pc-ringed-space-module-stalk-tensor` conjugates this stalk map
   to the tensor of the skyscraper stalk map with `F_x`.
5. Constant sections identify the skyscraper stalk of `M` with `M`: every section on
   a neighbourhood is constant on its subsingleton domain of membership proofs, and
   equality of germs detects its value. Representing scalars by germs proves linearity;
   stalk maps preserve these constant-section germs. Conjugating by these isomorphisms
   shows that `f ⊗ id` is injective, as required. -/
theorem flat_stalk_of_isFlat (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    (hF : SheafOfModules.IsFlat F) (x : X) :
    Module.Flat (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj F) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  have hlim : Limits.PreservesFiniteLimits (MonoidalCategory.tensorRight F) := hF.1
  let S := moduleStalkFunctor X x
  let T := SheafOfModules.ringedModuleSkyscraperFunctor X x
  obtain ⟨Φ, _, hΦ⟩ := SheafOfModules.stalkTensorIso X x
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ f hf
  let A := ModuleCat.of (X.presheaf.stalk x) M
  let B := ModuleCat.of (X.presheaf.stalk x) N
  let g : A ⟶ B := ModuleCat.ofHom f
  let j := T.map g
  -- Skyscraper maps are injective on every open.
  have hj : Mono j := by
    constructor
    intro Z a b hab
    ext V s
    funext h
    apply hf
    exact congrArg (fun k : Z ⟶ T.obj B ↦ k.val.app V s h) hab
  have ht : Mono (MonoidalCategory.whiskerRight j F) := (MonoidalCategory.tensorRight F).map_mono j
  -- A zero first map packages monicity as exactness.
  let C := ShortComplex.mk
    (0 : MonoidalCategory.tensorObj (T.obj A) F ⟶ MonoidalCategory.tensorObj (T.obj A) F)
    (MonoidalCategory.whiskerRight j F) (by simp)
  have hC : C.Exact := (C.exact_iff_mono rfl).mpr ht
  have hCS : (C.map S).Exact :=
    ((module_stalk_exact X C.f).2.2.2.2 C.X₃ C.f C.g C.zero).mp hC x
  have hst : Mono (S.map (MonoidalCategory.whiskerRight j F)) :=
    ((C.map S).exact_iff_mono (by simp [C])).mp hCS
  -- Naturality transfers monicity across the stalk-tensor isomorphisms.
  have hn : S.map (MonoidalCategory.whiskerRight j F) ≫ (Φ (T.obj B) F).hom =
      (Φ (T.obj A) F).hom ≫ (MonoidalCategory.whiskerRight (S.map j) (S.obj F)) := by
    simpa using hΦ (T.obj A) F (T.obj B) F j (𝟙 F)
  have he : MonoidalCategory.whiskerRight (S.map j) (S.obj F) =
      (Φ (T.obj A) F).inv ≫ S.map (MonoidalCategory.whiskerRight j F) ≫ (Φ (T.obj B) F).hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  have hm : Mono (MonoidalCategory.whiskerRight (S.map j) (S.obj F)) := by
    rw [he]
    infer_instance
  -- Recover the original map by natural constant-section germ isomorphisms.
  let eA : A ≅ S.obj (T.obj A) :=
    (LinearEquiv.ofBijective (constantGerm X x A).hom
      (constantGerm_bijective X x A)).toModuleIso
  let eB : B ≅ S.obj (T.obj B) :=
    (LinearEquiv.ofBijective (constantGerm X x B).hom
      (constantGerm_bijective X x B)).toModuleIso
  have hg : g = eA.hom ≫ S.map j ≫ eB.inv := by
    rw [← Category.assoc]
    change g = (constantGerm X x A ≫ S.map j) ≫ eB.inv
    rw [constantGerm_naturality]
    change g = g ≫ eB.hom ≫ eB.inv
    simp
  have hm' : Mono (MonoidalCategory.whiskerRight g (S.obj F)) := by
    rw [hg, MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight]
    infer_instance
  exact (ModuleCat.mono_iff_injective (MonoidalCategory.whiskerRight g (S.obj F))).mp hm'

end

end AlgebraicGeometry.RingedSpace
