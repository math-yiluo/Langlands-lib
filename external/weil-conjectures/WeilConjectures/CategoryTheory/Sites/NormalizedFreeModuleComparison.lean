/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.LinearAlgebra.FreeModule.Basic

import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Conditional calculus of normalized free-module comparisons

Source: Stacks Project, Modules on Sites, Tag 08TQ (lemma-pullback-differentials),
free-module identifications, and Tag 04BL (lemma-universal-module), generator extensions
(auxiliary; not a blueprint node).

The free sheaves, generators, and simultaneous coefficient/generator changes are the
existing `SheafFreeModule.free`, `generator`, and `change`. No adjunction is assumed for
the set-sheaf functors. Equalities of semilinear maps are expressed on their underlying
sheaves; this forgetful description is faithful. The explicit `ULift` identifications
are those of the recorded algebraic inverse-image interface.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w wI uC vC uD vD uH vH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafFreeModule

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

-- Cache the existing sheaf-composition witnesses once for each site.
local instance : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : J.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : J.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : K.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : K.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private theorem change_generator {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (u : E ⟶ E') :
    generator B E ≫ changeSets b u = u ≫ generator B' E' := by
  let M := (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj
      ((free B').obj E')
  let a : E ⟶ (underlyingRaw B).obj M := u ≫ generatorRaw B' E'
  have h := (freeModule_extend_inverse B E M).1 a
  have hc : change b u = extendGenerators B E M a := by
    simp only [change, extendGenerators, Adjunction.comp_homEquiv,
      PresheafOfModules.freeAdjunction_homEquiv, Equiv.symm_trans_apply]
    rfl
  rw [← hc] at h
  ext U x
  apply ULift.ext
  exact congrArg (fun f ↦ f.hom.app U x) h

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private abbrev coefficientSets (B : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def addSections {B : Sheaf J CommRingCat.{w}}
    (M : SheafOfModules.{w} (ring B)) :
    (moduleSets B).obj M ⊗ (moduleSets B).obj M ⟶ (moduleSets B).obj M :=
  ⟨{ app := fun U ↦ ↾(fun z ↦ ULift.up (z.1.down + z.2.down))
     naturality := by
       intro U V f
       ext z
       apply ULift.ext
       exact ((M.val.map f).hom.map_add _ _).symm }⟩

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def smulSections {B : Sheaf J CommRingCat.{w}}
    (M : SheafOfModules.{w} (ring B)) :
    coefficientSets B ⊗ (moduleSets B).obj M ⟶ (moduleSets B).obj M :=
  ⟨{ app := fun U ↦ ↾(fun z ↦ ULift.up
        ((@id (B.obj.obj U) z.1.down) • (@id (M.val.obj U) z.2.down)))
     naturality := by
       intro U V f
       ext z
       apply ULift.ext
       exact (M.val.map_smul f z.1.down z.2.down).symm }⟩

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] in
private theorem pair_sections (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    [PreservesFiniteLimits L] (X Y : Sheaf J (Type w)) (V : Dᵒᵖ)
    (x : (L.obj X).obj.obj V) (y : (L.obj Y).obj.obj V) :
    ∃ z : (L.obj (X ⊗ Y)).obj.obj V,
      (L.map (CartesianMonoidalCategory.fst X Y)).hom.app V z = x ∧
      (L.map (CartesianMonoidalCategory.snd X Y)).hom.app V z = y := by
  refine ⟨(inv (CartesianMonoidalCategory.prodComparison L X Y)).hom.app V (x, y),
    ?_, ?_⟩
  · exact congrArg (fun f ↦ f.hom.app V (x, y))
      (CartesianMonoidalCategory.inv_prodComparison_map_fst L X Y)
  · exact congrArg (fun f ↦ f.hom.app V (x, y))
      (CartesianMonoidalCategory.inv_prodComparison_map_snd L X Y)

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private theorem transport_semilinear
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') (bi : BI ⟶ BI')
    (hb : L.map ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b) ≫ F'.ringUnderlying.hom =
      F.ringUnderlying.hom ≫ (sheafCompose K
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map bi)
    (M : SheafOfModules.{w} (ring B)) (M' : SheafOfModules.{w} (ring B'))
    (h : (moduleSets B).obj M ⟶ (moduleSets B').obj M')
    (ha : ∀ U (x y : M.val.obj U),
      (h.hom.app U (ULift.up (x + y))).down =
        (h.hom.app U (ULift.up x)).down + (h.hom.app U (ULift.up y)).down)
    (hs : ∀ U (a : B.obj.obj U) (x : M.val.obj U),
      (h.hom.app U (ULift.up (a • x))).down =
        b.hom.app U a • (@id (M'.val.obj U) (h.hom.app U (ULift.up x)).down)) :
    let t := F.moduleUnderlying.hom.app M ≫ L.map h ≫ F'.moduleUnderlying.inv.app M'
    (∀ V (x y : (F.modules.obj M).val.obj V),
      (t.hom.app V (ULift.up (x + y))).down =
        (t.hom.app V (ULift.up x)).down + (t.hom.app V (ULift.up y)).down) ∧
    (∀ V (a : BI.obj.obj V) (x : (F.modules.obj M).val.obj V),
      (t.hom.app V (ULift.up (a • x))).down =
        bi.hom.app V a •
          (@id ((F'.modules.obj M').val.obj V) (t.hom.app V (ULift.up x)).down)) := by
  let X := (moduleSets B).obj M
  let Y := coefficientSets B
  let t := F.moduleUnderlying.hom.app M ≫ L.map h ≫ F'.moduleUnderlying.inv.app M'
  have hi (V : Dᵒᵖ) (x : (F.modules.obj M).val.obj V) :
      (F.moduleUnderlying.inv.app M).hom.app V
        ((F.moduleUnderlying.hom.app M).hom.app V (ULift.up x)) = ULift.up x :=
    congrArg (fun f ↦ f.hom.app V (ULift.up x)) (F.moduleUnderlying.hom_inv_id_app M)
  have ht (T : Sheaf J (Type w)) (g : T ⟶ X) (V : Dᵒᵖ)
      (z : (L.obj T).obj.obj V) :
      (t.hom.app V ((F.moduleUnderlying.inv.app M).hom.app V
        ((L.map g).hom.app V z))).down =
      ((F'.moduleUnderlying.inv.app M').hom.app V
        ((L.map (g ≫ h)).hom.app V z)).down := by
    have hh := congrArg (fun f ↦ f.hom.app V ((L.map g).hom.app V z))
      (F.moduleUnderlying.inv_hom_id_app M)
    dsimp at hh
    dsimp [t]
    rw [hh]
    rw [L.map_comp]
    rfl
  constructor
  · intro V x y
    obtain ⟨z, hx, hy⟩ := pair_sections L X X V
      ((F.moduleUnderlying.hom.app M).hom.app V (ULift.up x))
      ((F.moduleUnderlying.hom.app M).hom.app V (ULift.up y))
    have hF := F.moduleAdd M (X ⊗ X) (CartesianMonoidalCategory.fst X X)
      (CartesianMonoidalCategory.snd X X) (addSections M) (fun _ _ ↦ rfl) V z
    have hG := F'.moduleAdd M' (X ⊗ X)
      (CartesianMonoidalCategory.fst X X ≫ h)
      (CartesianMonoidalCategory.snd X X ≫ h) (addSections M ≫ h)
      (fun U z ↦ ha U z.1.down z.2.down) V z
    rw [hx, hy] at hF
    simp only [hi, ULift.down_up, id_eq] at hF
    change (t.hom.app V (ULift.up (x + y))).down = _
    rw [← hF]
    have hu : ULift.up
        (((F.moduleUnderlying.inv.app M).hom.app V
          ((L.map (addSections M)).hom.app V z)).down) =
        (F.moduleUnderlying.inv.app M).hom.app V
          ((L.map (addSections M)).hom.app V z) := ULift.up_down _
    dsimp only [id_eq] at hG
    rw [hu, ht, hG]
    rw [← ht, ← ht, hx, hy, hi, hi]
  · intro V a x
    obtain ⟨z, ha', hx⟩ := pair_sections L Y X V
      (F.ringUnderlying.inv.hom.app V (ULift.up a))
      ((F.moduleUnderlying.hom.app M).hom.app V (ULift.up x))
    have hr : F.ringUnderlying.hom.hom.app V
        ((L.map (CartesianMonoidalCategory.fst Y X)).hom.app V z) = ULift.up a := by
      rw [ha']
      exact congrArg (fun f ↦ f.hom.app V (ULift.up a)) F.ringUnderlying.inv_hom_id
    have hF := F.moduleSMul M (Y ⊗ X) (CartesianMonoidalCategory.fst Y X)
      (CartesianMonoidalCategory.snd Y X) (smulSections M) (fun _ _ ↦ rfl) V z
    have hG := F'.moduleSMul M' (Y ⊗ X)
      (CartesianMonoidalCategory.fst Y X ≫ (sheafCompose J
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b)
      (CartesianMonoidalCategory.snd Y X ≫ h) (smulSections M ≫ h)
      (fun U z ↦ hs U z.1.down z.2.down) V z
    have hr' : F'.ringUnderlying.hom.hom.app V
        ((L.map (CartesianMonoidalCategory.fst Y X ≫ (sheafCompose J
          (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b)).hom.app V z) =
        ULift.up (bi.hom.app V a) := by
      rw [L.map_comp]
      have he := congrArg (fun f ↦ f.hom.app V
        ((L.map (CartesianMonoidalCategory.fst Y X)).hom.app V z)) hb
      change _ = ((sheafCompose K
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map bi).hom.app V
          (F.ringUnderlying.hom.hom.app V
            ((L.map (CartesianMonoidalCategory.fst Y X)).hom.app V z)) at he
      rw [hr] at he
      exact he
    rw [hr, hx] at hF
    simp only [hi, ULift.down_up, id_eq] at hF
    change (t.hom.app V (ULift.up (a • x))).down = _
    rw [← hF]
    dsimp only [id_eq] at hG
    rw [ULift.up_down, ht, hG, hr']
    rw [← ht, hx, hi]
    rfl

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def linearMapOfSets {B : Sheaf J CommRingCat.{w}}
    {M N : SheafOfModules.{w} (ring B)}
    (f : (moduleSets B).obj M ⟶ (moduleSets B).obj N)
    (ha : ∀ U (x y : M.val.obj U),
      (f.hom.app U (ULift.up (x + y))).down =
        (f.hom.app U (ULift.up x)).down + (f.hom.app U (ULift.up y)).down)
    (hs : ∀ U (a : B.obj.obj U) (x : M.val.obj U),
      (f.hom.app U (ULift.up (a • x))).down =
        a • (@id (N.val.obj U) (f.hom.app U (ULift.up x)).down)) : M ⟶ N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun x ↦ (f.hom.app U (ULift.up x)).down
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V g
        ext x
        exact congrArg ULift.down (congrArg (fun k ↦ k (ULift.up x))
          (f.hom.naturality g)) }

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private theorem linearMapOfSets_underlying {B : Sheaf J CommRingCat.{w}}
    {M N : SheafOfModules.{w} (ring B)}
    (f : (moduleSets B).obj M ⟶ (moduleSets B).obj N) (ha hs) :
    (moduleSets B).map (linearMapOfSets f ha hs) = f := by
  ext U x
  exact ULift.up_down _

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private theorem change_identity_comp {B : Sheaf J CommRingCat.{w}}
    {E E' E'' : Sheaf J (Type w)} (u : E ⟶ E') (v : E' ⟶ E'') :
    changeSets (𝟙 B) u ≫ changeSets (𝟙 B) v = changeSets (𝟙 B) (u ≫ v) := by
  let M := (free B).obj E''
  let f : (free B).obj E ⟶ (free B).obj E' :=
    linearMapOfSets (changeSets (𝟙 B) u)
      (fun U x y ↦ (change (𝟙 B) u).val.app U |>.hom.map_add x y)
      (fun U a x ↦ (change (𝟙 B) u).val.app U |>.hom.map_smul a x)
  let g : (free B).obj E' ⟶ M :=
    linearMapOfSets (changeSets (𝟙 B) v)
      (fun U x y ↦ (change (𝟙 B) v).val.app U |>.hom.map_add x y)
      (fun U a x ↦ (change (𝟙 B) v).val.app U |>.hom.map_smul a x)
  let h : (free B).obj E ⟶ M :=
    linearMapOfSets (changeSets (𝟙 B) (u ≫ v))
      (fun U x y ↦ (change (𝟙 B) (u ≫ v)).val.app U |>.hom.map_add x y)
      (fun U a x ↦ (change (𝟙 B) (u ≫ v)).val.app U |>.hom.map_smul a x)
  have he : f ≫ g = h := (freeModule_restrict_bijective B E M).1 (by
    apply Sheaf.hom_ext
    ext U x
    have hn : generator B E ≫ (moduleSets B).map (f ≫ g) =
        generator B E ≫ (moduleSets B).map h := by
      simp only [Functor.map_comp, f, g, h, linearMapOfSets_underlying]
      rw [← Category.assoc, change_generator, Category.assoc, change_generator]
      rw [change_generator, Category.assoc]
    exact congrArg (fun f ↦ (f.hom.app U x).down) hn)
  have he' := congrArg ((moduleSets B).map) he
  simpa only [Functor.map_comp, f, g, h, linearMapOfSets_underlying] using he'

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Underlying comparison for an arbitrary algebraic transport, with the canonical
underlying-module identification retained. Source: Stacks 08TQ, free identifications
(auxiliary; not a blueprint node). -/
def normalizedFreeComparison
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (L.obj E)) :
    L.obj ((moduleSets B).obj ((free B).obj E)) ⟶
      (moduleSets BI).obj ((free BI).obj (L.obj E)) :=
  F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map p.hom

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- The stated representing hypothesis is precisely bijectivity of restriction along
L of the canonical generator, for every target module sheaf. Source: Stacks 04BL and
08TQ, conditional free identification
(auxiliary; not a blueprint node). -/
def HasTransportedFreeUniversalProperty
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w)) : Prop :=
  ∀ M : SheafOfModules.{w} (ring BI),
    Function.Bijective (fun h : F.modules.obj ((free B).obj E) ⟶ M ↦
      L.map (generator B E) ≫ F.moduleUnderlying.inv.app ((free B).obj E) ≫
        (moduleSets BI).map h)

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- The source and target underlying identifications applied to L of a coefficient and
 generator change. Source: Stacks 04BL and 08TQ, semilinear generator extension
(auxiliary; not a blueprint node). -/
def transportedFreeChange
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') {E E' : Sheaf J (Type w)} (u : E ⟶ E') :
    (moduleSets BI).obj (F.modules.obj ((free B).obj E)) ⟶
      (moduleSets BI').obj (F'.modules.obj ((free B').obj E')) :=
  F.moduleUnderlying.hom.app ((free B).obj E) ≫ L.map (changeSets b u) ≫
    F'.moduleUnderlying.inv.app ((free B').obj E')

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Sectionwise form of the transported change, descending the interface's `ULift`.
Source: Stacks 04BL and 08TQ, semilinear generator extension
(auxiliary; not a blueprint node). -/
def transportedFreeChangeSection
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') {E E' : Sheaf J (Type w)} (u : E ⟶ E')
    (V : Dᵒᵖ) (x : (F.modules.obj ((free B).obj E)).val.obj V) :
    (F'.modules.obj ((free B').obj E')).val.obj V :=
  ((transportedFreeChange L F F' b u).hom.app V (ULift.up x)).down

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Applying L to the actual semilinear extension gives a semilinear map over Lb,
including additivity and zero compatibility. The equation hb merely identifies Lb
in the chosen ring presentations; it does not assume it invertible.
Source: Stacks 08TQ and 04BL, operation transport and generator extension
(auxiliary; not a blueprint node).

Proof: node step 1 constructs change by scalar restriction and sheafification; it is
additive and satisfies c(ax)=b(a)c(x). Step 2 writes these laws as operation diagrams
on universal generalized sections. Apply L to the diagrams. The graph laws in F and
F' transport addition, zero, and scalar multiplication. Naturality of the finite-product
comparisons, and hb, identify the transported coefficient map with bi. The three
resulting sectionwise equations are precisely those below. No adjoint is used. -/
theorem normalizedFreeModule_change_semilinear
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') (bi : BI ⟶ BI')
    (hb : L.map ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b) ≫ F'.ringUnderlying.hom =
      F.ringUnderlying.hom ≫ (sheafCompose K
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map bi)
    {E E' : Sheaf J (Type w)} (u : E ⟶ E') :
    ∀ V : Dᵒᵖ,
      (∀ x y : (F.modules.obj ((free B).obj E)).val.obj V,
        transportedFreeChangeSection L F F' b u V (x + y) =
          transportedFreeChangeSection L F F' b u V x +
            transportedFreeChangeSection L F F' b u V y) ∧
      transportedFreeChangeSection L F F' b u V 0 = 0 ∧
      (∀ (a : BI.obj.obj V) (x : (F.modules.obj ((free B).obj E)).val.obj V),
        transportedFreeChangeSection L F F' b u V (a • x) =
          (bi.hom.app V a) • transportedFreeChangeSection L F F' b u V x) := by
  have h := transport_semilinear L F F' b bi hb ((free B).obj E) ((free B').obj E')
    (changeSets b u) (fun U x y ↦ (change b u).val.app U |>.hom.map_add x y)
    (fun U a x ↦ (change b u).val.app U |>.hom.map_smul a x)
  intro V
  refine ⟨h.1 V, ?_, h.2 V⟩
  have hz := h.1 V 0 0
  change transportedFreeChangeSection L F F' b u V (0 + 0) = _ at hz
  simp only [zero_add] at hz
  exact (add_eq_left.mp hz.symm)

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Simultaneous naturality for arbitrary coefficient maps and generator maps.
Source: Stacks 08TQ and 04BL, normalized free identifications
(auxiliary; not a blueprint node).

Proof: node step 1 identifies change with the sheafified semilinear extension and proves
its generator equation, using lem-trf-free-module-sheaf-universal-property. Step 2
transports its semilinearity by the operation graphs. In step 3 restrict scalars of the
target (BI')[LE'] along bi. Both displayed composites are then BI-linear. Their
restrictions along Li are i followed by Lu: this follows from the generator equation,
functoriality of L, and the two normalization hypotheses. The assumed representing
bijection for F,E is injective at that scalar-restricted target, so the composites agree.
Faithfulness of the underlying-sheaf description gives equality as semilinear maps. -/
theorem normalizedFreeModule_naturality
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B' BI')
    (b : B ⟶ B') (bi : BI ⟶ BI')
    (hb : L.map ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b) ≫ F'.ringUnderlying.hom =
      F.ringUnderlying.hom ≫ (sheafCompose K
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map bi)
    {E E' : Sheaf J (Type w)} (u : E ⟶ E')
    (hL : HasTransportedFreeUniversalProperty L F E)
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (L.obj E))
    (p' : F'.modules.obj ((free B').obj E') ≅ (free BI').obj (L.obj E'))
    (hp : L.map (generator B E) ≫ normalizedFreeComparison L F E p =
      generator BI (L.obj E))
    (hp' : L.map (generator B' E') ≫ normalizedFreeComparison L F' E' p' =
      generator BI' (L.obj E')) :
    L.map (changeSets b u) ≫ normalizedFreeComparison L F' E' p' =
      normalizedFreeComparison L F E p ≫ changeSets bi (L.map u) := by
  let M := (SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map bi)).obj
      ((free BI').obj (L.obj E'))
  let t := transportedFreeChange L F F' b u
  have ht := normalizedFreeModule_change_semilinear L F F' b bi hb u
  let a : F.modules.obj ((free B).obj E) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map bi)).obj
          (F'.modules.obj ((free B').obj E')) :=
    linearMapOfSets t (fun V ↦ (ht V).1) (fun V ↦ (ht V).2.2)
  let c : F.modules.obj ((free B).obj E) ⟶ M :=
    a ≫ (SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map bi)).map p'.hom
  let d : F.modules.obj ((free B).obj E) ⟶ M := p.hom ≫ change bi (L.map u)
  have hc : (moduleSets BI).map c = t ≫ (moduleSets BI').map p'.hom := by
    dsimp only [c]
    rw [Functor.map_comp, linearMapOfSets_underlying]
    rfl
  have hd : (moduleSets BI).map d =
      (moduleSets BI).map p.hom ≫ changeSets bi (L.map u) := by
    rw [Functor.map_comp]
    rfl
  have he : c = d := (hL M).1 (by
    dsimp only
    rw [hc, hd]
    change L.map (generator B E) ≫ F.moduleUnderlying.inv.app _ ≫
        (F.moduleUnderlying.hom.app _ ≫ L.map (changeSets b u) ≫
          F'.moduleUnderlying.inv.app _) ≫ (moduleSets BI').map p'.hom = _
    simp only [Category.assoc, ← Iso.app_inv, ← Iso.app_hom, Iso.inv_hom_id_assoc]
    change L.map (generator B E) ≫ L.map (changeSets b u) ≫
        normalizedFreeComparison L F' E' p' =
      L.map (generator B E) ≫ normalizedFreeComparison L F E p ≫
        changeSets bi (L.map u)
    rw [← Category.assoc, ← L.map_comp, change_generator, L.map_comp]
    rw [Category.assoc, hp', ← Category.assoc, hp, change_generator])
  have he' := congrArg (fun f ↦ F.moduleUnderlying.inv.app ((free B).obj E) ≫
    (moduleSets BI).map f) he
  rw [hc, hd] at he'
  simpa only [t, transportedFreeChange, normalizedFreeComparison, Category.assoc,
    ← Iso.app_inv, ← Iso.app_hom, Iso.inv_hom_id_assoc] using he'

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Generator compatibility after an arbitrary map out of LE, without requiring that map
be invertible. Source: Stacks 08TQ and 04BL, generator extensions
(auxiliary; not a blueprint node).

Proof: node step 4 composes normalization with the generator equation for c(1,v).
That equation follows by evaluating the sectionwise extension on [e] and factoring
through module sheafification (step 1). Associativity yields the displayed equality. -/
theorem normalizedFreeModule_generators
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w)) (A : Sheaf K (Type w)) (v : L.obj E ⟶ A)
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (L.obj E))
    (hp : L.map (generator B E) ≫ normalizedFreeComparison L F E p =
      generator BI (L.obj E)) :
    L.map (generator B E) ≫ normalizedFreeComparison L F E p ≫ changeSets (𝟙 BI) v =
      v ≫ generator BI A := by
  rw [← Category.assoc, hp, change_generator]

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Finite-product generator normalization, including the empty product, and every
projection square. Source: Stacks 08TQ, free module on the product of generator sheaves
(auxiliary; not a blueprint node).

Proof: in node step 5 apply step 4 with v the canonical finite-product comparison.
Finite-limit preservation makes this comparison an isomorphism, even for the empty
index type. For each i, its composite with the i-th target projection is L of the
source projection. Both maps in the projection square restrict along Li to the same
generator map followed by L of that projection, by step 1 and normalization. Injectivity
of hL at the target free module identifies them. For the empty index type there are
no projection equations, and the generator equation still concerns the terminal sheaf;
the free module on that terminal sheaf is not confused with the zero module. -/
theorem normalizedFreeModule_products
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    {I : Type wI} [Finite I] (E : I → Sheaf J (Type w))
    (hL : HasTransportedFreeUniversalProperty L F (∏ᶜ E))
    (p : F.modules.obj ((free B).obj (∏ᶜ E)) ≅ (free BI).obj (L.obj (∏ᶜ E)))
    (pi : ∀ i : I, F.modules.obj ((free B).obj (E i)) ≅ (free BI).obj (L.obj (E i)))
    (hp : L.map (generator B (∏ᶜ E)) ≫ normalizedFreeComparison L F (∏ᶜ E) p =
      generator BI (L.obj (∏ᶜ E)))
    (hpi : ∀ i : I, L.map (generator B (E i)) ≫
      normalizedFreeComparison L F (E i) (pi i) = generator BI (L.obj (E i))) :
    (L.map (generator B (∏ᶜ E)) ≫ normalizedFreeComparison L F (∏ᶜ E) p ≫
        changeSets (𝟙 BI) (piComparison L E) =
      piComparison L E ≫ generator BI (∏ᶜ fun i ↦ L.obj (E i))) ∧
    (∀ i : I,
      normalizedFreeComparison L F (∏ᶜ E) p ≫ changeSets (𝟙 BI) (piComparison L E) ≫
          changeSets (𝟙 BI) (Pi.π (fun i ↦ L.obj (E i)) i) =
        L.map (changeSets (𝟙 B) (Pi.π E i)) ≫
          normalizedFreeComparison L F (E i) (pi i)) := by
  refine ⟨normalizedFreeModule_generators L F _ _ _ p hp, ?_⟩
  intro i
  have hn := normalizedFreeModule_naturality L F F (𝟙 B) (𝟙 BI)
    (by simp) (Pi.π E i) hL p (pi i) hp (hpi i)
  have he : changeSets (𝟙 BI) (piComparison L E) ≫
      changeSets (𝟙 BI) (Pi.π (fun i ↦ L.obj (E i)) i) =
      changeSets (𝟙 BI) (L.map (Pi.π E i)) := by
    rw [change_identity_comp, piComparison_comp_π]
  rw [he]
  exact hn.symm

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- For identity transport with the original operations, a normalized comparison is
literally the identity isomorphism. Source: Stacks 04BL and 08TQ, normalized uniqueness
(auxiliary; not a blueprint node).

Proof: node step 6 applies the free-sheaf restriction bijection of
lem-trf-free-module-sheaf-universal-property. The comparison and the identity both
restrict to i by normalization, so their homs are equal; hence the isomorphisms agree. -/
theorem normalizedFreeModule_identity
    (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w))
    (p : (free B).obj E ≅ (free B).obj E)
    (hp : generator B E ≫ (moduleSets B).map p.hom = generator B E) :
    p = Iso.refl ((free B).obj E) := by
  apply Iso.ext
  apply (freeModule_restrict_bijective B E ((free B).obj E)).1
  apply Sheaf.hom_ext
  ext U x
  have h := congrArg (fun f ↦ (f.hom.app U x).down) hp
  exact h

variable {H : Type uH} [Category.{vH} H] [EssentiallySmall.{w} H]
  {T : GrothendieckTopology H}

local instance : T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : T.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : T.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
private def compositePresentation
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (N : Sheaf K (Type w) ⥤ Sheaf T (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    {BII : Sheaf T CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (G : SheafOfModules.AlgebraicInverseImageOfUniverses.{uD, vD, uH, vH, w, w} N BI BII) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uH, vH, w, w} (L ⋙ N) B BII where
  ringUnderlying := N.mapIso F.ringUnderlying ≪≫ G.ringUnderlying
  ringAdd := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringAdd (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringAdd S a b t h) V x
  ringMul := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringMul (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringMul S a b t h) V x
  ringZero := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringZero (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringZero S a h) V x
  ringOne := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringOne (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringOne S a h) V x
  modules := F.modules ⋙ G.modules
  moduleUnderlying := Functor.isoWhiskerLeft F.modules G.moduleUnderlying ≪≫
    Functor.isoWhiskerRight F.moduleUnderlying N
  moduleAdd := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleAdd (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleAdd M S a b t h) V x
  moduleZero := by
    intro M S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleZero (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M) (F.moduleZero M S a h) V x
  moduleSMul := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleSMul (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleSMul M S a b t h) V x

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- Coherence for composite transported operations and their underlying identifications.
Source: Stacks 08TQ and 04BL, composite normalized free identifications
(auxiliary; not a blueprint node).

Proof: in node step 7, step 2 makes K of the first linear comparison linear over KLB.
The ring equation hB identifies the composite scalar action with the one of FG.
Applying K to the first normalization and then using the second shows that the
successive comparison and r both restrict along KLi to the target generator. The
representing bijection hKL is injective at the target free module, giving equality.
The displayed equation retains every underlying identification rather than requiring
chosen module functors to be definitionally equal. No adjunction is used anywhere. -/
theorem normalizedFreeModule_composition
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (N : Sheaf K (Type w) ⥤ Sheaf T (Type w)) [PreservesFiniteLimits N]
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    {BII : Sheaf T CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (G : SheafOfModules.AlgebraicInverseImageOfUniverses.{uD, vD, uH, vH, w, w} N BI BII)
    (FG : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uH, vH, w, w}
      (L ⋙ N) B BII)
    (hB : FG.ringUnderlying.hom = N.map F.ringUnderlying.hom ≫ G.ringUnderlying.hom)
    (E : Sheaf J (Type w))
    (hKL : HasTransportedFreeUniversalProperty (L ⋙ N) FG E)
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (L.obj E))
    (q : G.modules.obj ((free BI).obj (L.obj E)) ≅ (free BII).obj (N.obj (L.obj E)))
    (r : FG.modules.obj ((free B).obj E) ≅ (free BII).obj ((L ⋙ N).obj E))
    (hp : L.map (generator B E) ≫ normalizedFreeComparison L F E p =
      generator BI (L.obj E))
    (hq : N.map (generator BI (L.obj E)) ≫ normalizedFreeComparison N G (L.obj E) q =
      generator BII (N.obj (L.obj E)))
    (hr : (L ⋙ N).map (generator B E) ≫ normalizedFreeComparison (L ⋙ N) FG E r =
      generator BII ((L ⋙ N).obj E)) :
    normalizedFreeComparison (L ⋙ N) FG E r =
      N.map (normalizedFreeComparison L F E p) ≫ normalizedFreeComparison N G (L.obj E) q := by
  have : PreservesFiniteLimits (L ⋙ N) := comp_preservesFiniteLimits L N
  let A := compositePresentation L N F G
  let M := (free B).obj E
  let t := FG.moduleUnderlying.hom.app M ≫ A.moduleUnderlying.inv.app M
  have hba : (L ⋙ N).map ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map (𝟙 B)) ≫ A.ringUnderlying.hom =
      FG.ringUnderlying.hom ≫ (sheafCompose T
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map (𝟙 BII) := by
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using
      (show A.ringUnderlying.hom = FG.ringUnderlying.hom from hB.symm)
  have ht := transport_semilinear (L ⋙ N) FG A (𝟙 B) (𝟙 BII) hba M M (𝟙 _)
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
  let a : FG.modules.obj M ⟶ A.modules.obj M := linearMapOfSets t
    (by
      intro V x y
      have hv := ht.1 V x y
      simpa [t] using hv)
    (by
      intro V a x
      have hv := ht.2 V a x
      simpa [t] using hv)
  let c : FG.modules.obj M ⟶ (free BII).obj ((L ⋙ N).obj E) :=
    a ≫ G.modules.map p.hom ≫ q.hom
  have hc : FG.moduleUnderlying.inv.app M ≫ (moduleSets BII).map c =
      N.map (normalizedFreeComparison L F E p) ≫
        normalizedFreeComparison N G (L.obj E) q := by
    dsimp only [c]
    rw [Functor.map_comp, Functor.map_comp, linearMapOfSets_underlying]
    dsimp only [t]
    simp only [Category.assoc, ← Iso.app_inv, ← Iso.app_hom, Iso.inv_hom_id_assoc]
    change N.map (F.moduleUnderlying.inv.app M) ≫
        G.moduleUnderlying.inv.app (F.modules.obj M) ≫
          (moduleSets BII).map (G.modules.map p.hom) ≫ (moduleSets BII).map q.hom = _
    have hg := G.moduleUnderlying.inv.naturality p.hom
    change N.map ((moduleSets BI).map p.hom) ≫ G.moduleUnderlying.inv.app _ =
      G.moduleUnderlying.inv.app (F.modules.obj M) ≫
        (moduleSets BII).map (G.modules.map p.hom) at hg
    rw [← Category.assoc (G.moduleUnderlying.inv.app _), ← hg]
    simp only [Functor.comp_map, Category.assoc, normalizedFreeComparison, N.map_comp]
    rfl
  have he : r.hom = c := (hKL ((free BII).obj ((L ⋙ N).obj E))).1 (by
    dsimp only
    change (L ⋙ N).map (generator B E) ≫ normalizedFreeComparison (L ⋙ N) FG E r = _
    rw [hr, hc]
    change generator BII (N.obj (L.obj E)) =
      N.map (L.map (generator B E)) ≫ N.map (normalizedFreeComparison L F E p) ≫
        normalizedFreeComparison N G (L.obj E) q
    rw [← Category.assoc, ← N.map_comp, hp, hq])
  rw [normalizedFreeComparison, he]
  exact hc

end CategoryTheory.SheafFreeModule
