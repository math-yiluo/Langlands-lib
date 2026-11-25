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
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# The normalized Hom chain for a transported free module sheaf

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D3, 04BL and 08TQ
(auxiliary; not a blueprint node).

The free object, its generator, and its algebraic inverse-image presentation are the
published constructions. The right module is specified by its underlying direct image
and the addition and scalar-action graphs under the set adjunction. These graphs express
the direct image of the operations followed by restriction along the coefficient unit.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafFreeModule

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Restrict a linear map to the transported canonical generator, retaining the
underlying-sheaf identification. Source: Stacks 08TQ, free-module identifications
(auxiliary; not a blueprint node). -/
def inverseFreeRestriction
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (H : SheafOfModules.{w} (ring BI))
    (h : F.modules.obj ((free B).obj E) ⟶ H) :
    f.inverse.obj E ⟶ (moduleSets BI).obj H :=
  f.inverse.map (generator B E) ≫ F.moduleUnderlying.inv.app ((free B).obj E) ≫
    (moduleSets BI).map h

/-- Transpose a generalized section of a module's underlying direct image.
Source: Stacks 03D3, underlying sheaf adjunction
(auxiliary; not a blueprint node). -/
def directModuleTranspose
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    {N : SheafOfModules.{w} (ring B)}
    {H : SheafOfModules.{w} (ring BI)}
    (e : (moduleSets B).obj N ≅ f.direct.obj ((moduleSets BI).obj H))
    {T : Sheaf J (Type w)} (a : T ⟶ (moduleSets B).obj N) :
    f.inverse.obj T ⟶ (moduleSets BI).obj H :=
  (f.adj.homEquiv T ((moduleSets BI).obj H)).symm (a ≫ e.hom)

section ComposeInstances
variable {S : Type uC} [Category.{vC} S] [EssentiallySmall.{w} S]
  (T : GrothendieckTopology S)
private theorem composeRings :
    T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
private theorem composeRingSets :
    T.HasSheafCompose (forget CommRingCat.{w}) := inferInstance
omit [EssentiallySmall.{w} S] in
private theorem composeGroupSets :
    T.HasSheafCompose (forget AddCommGrpCat.{w}) := inferInstance
private theorem composeLiftRingSets :
    T.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
omit [EssentiallySmall.{w} S] in
private theorem composeLiftGroupSets :
    T.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
omit [EssentiallySmall.{w} S] in
private theorem composeLift : T.HasSheafCompose uliftFunctor.{w, w} := inferInstance
end ComposeInstances
attribute [local instance] SheafOfModules.sheafHasBinaryProduct
attribute [local instance] composeRings composeRingSets composeGroupSets
  composeLiftRingSets composeLiftGroupSets composeLift

private def moduleLift (B : Sheaf J CommRingCat.{w}) :
    underlyingRaw B ≅ moduleSets B :=
  NatIso.ofComponents (fun M ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.up }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.down }⟩ })
    (by intro M N h; rfl)

private def unliftIso {S : Type uC} [Category.{vC} S] [EssentiallySmall.{w} S]
    {T : GrothendieckTopology S} :
    sheafCompose T uliftFunctor.{w, w} ≅ 𝟭 (Sheaf T (Type w)) :=
  NatIso.ofComponents (fun X ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro X Y f; rfl)

private def ringLift (B : Sheaf J CommRingCat.{w}) :
    (sheafCompose J (forget CommRingCat.{w})).obj B ≅
      (sheafCompose J (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B where
  hom := ⟨{ app := fun _ ↦ ↾ULift.up }⟩
  inv := ⟨{ app := fun _ ↦ ↾ULift.down }⟩

private def rawPresentation
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      (JC := J) (JD := K) f.inverse B BI) :
    SheafOfModules.AlgebraicInverseImage (JC := J) (JD := K) f.inverse B BI := by
  let eJ := unliftIso (T := J)
  let eK := unliftIso (T := K)
  let rB : Sheaf J (Type w) := (sheafCompose J (forget CommRingCat.{w})).obj B
  let mB := underlyingRaw B
  let mBI := underlyingRaw BI
  refine
    { ringUnderlying := f.inverse.mapIso (ringLift B) ≪≫
        F.ringUnderlying ≪≫ (ringLift BI).symm
      modules := F.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft F.modules (Functor.isoWhiskerLeft mBI eK.symm) ≪≫
          F.moduleUnderlying ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft mB eJ) f.inverse
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t ht V x
    have h := F.ringAdd T (a ≫ eJ.inv.app rB) (b ≫ eJ.inv.app rB)
        (t ≫ eJ.inv.app rB) ht V x
    simp only [Functor.map_comp] at h
    exact h
  · intro T a b t ht V x
    have h := F.ringMul T (a ≫ eJ.inv.app rB) (b ≫ eJ.inv.app rB)
        (t ≫ eJ.inv.app rB) ht V x
    simp only [Functor.map_comp] at h
    exact h
  · intro T a ht V x
    have h := F.ringZero T (a ≫ eJ.inv.app rB) ht V x
    simp only [Functor.map_comp] at h
    exact h
  · intro T a ht V x
    have h := F.ringOne T (a ≫ eJ.inv.app rB) ht V x
    simp only [Functor.map_comp] at h
    exact h
  · intro M T a b t ht V x
    have h := F.moduleAdd M T (a ≫ eJ.inv.app (mB.obj M))
      (b ≫ eJ.inv.app (mB.obj M)) (t ≫ eJ.inv.app (mB.obj M)) ht V x
    simp only [Functor.map_comp] at h
    exact h
  · intro M T a ht V x
    have h := F.moduleZero M T (a ≫ eJ.inv.app (mB.obj M)) ht V x
    simp only [Functor.map_comp] at h
    exact h
  · intro M T a b t ht V x
    have h := F.moduleSMul M T (a ≫ eJ.inv.app rB) (b ≫ eJ.inv.app (mB.obj M))
      (t ≫ eJ.inv.app (mB.obj M)) ht V x
    simp only [Functor.map_comp] at h
    exact h

attribute [local irreducible] free

open SheafOfModules SheafOfModules.GeometricConstruction

private theorem binary_of_graph
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {X Y Z : Sheaf J (Type w)} {A B E : Sheaf K (Type w)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type w)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private noncomputable def madd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable def msmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M

private theorem towerAddSpec
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (ring R)) :
    addSpec M (madd R M) := by
  intro W x
  rfl

private theorem towerSMulSpec
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (ring R)) :
    smulSpec M (msmul R M) := by
  intro W x
  rfl

private theorem rawRight
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    [PreservesLimits f.direct]
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (I : AlgebraicInverseImage (JC := J) (JD := K) f.inverse B BI) :
    ∃ (P : SheafOfModules.{w} (ring BI) ⥤ SheafOfModules.{w} (ring B))
      (eP : P ⋙ underlyingRaw B ≅ underlyingRaw BI ⋙ f.direct),
      ∀ (H : SheafOfModules.{w} (ring BI)), madd B (P.obj H) ≫ eP.hom.app H =
        prod.map (eP.hom.app H) (eP.hom.app H) ≫
          inv (prodComparison f.direct ((underlyingRaw BI).obj H)
            ((underlyingRaw BI).obj H)) ≫ f.direct.map (madd BI H) ∧
      msmul B (P.obj H) ≫ eP.hom.app H =
        prod.map (f.adj.homEquiv _ _ I.ringUnderlying.hom) (eP.hom.app H) ≫
          inv (prodComparison f.direct (rset BI) ((underlyingRaw BI).obj H)) ≫
            f.direct.map (msmul BI H) := by
  let L := f.inverse
  let V := f.direct
  let adj := f.adj
  let : PreservesFiniteLimits L := f.leftExact
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let : V.Braided := Functor.Braided.ofChosenFiniteProducts V
  let g := I.ringUnderlying.hom
  let d := adj.homEquiv (rset B) (rset BI) g
  have hb (a : rset B ⊗ rset B ⟶ rset B) (b : rset BI ⊗ rset BI ⟶ rset BI)
      (h : L.map a ≫ g = CartesianMonoidalCategory.prodComparison L _ _ ≫
        (g ⊗ₘ g) ≫ b) :
      a ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫ V.map b :=
    adjunct_binary L V adj _ _ a b g h
  have ha : ringAdd B ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫
      V.map (ringAdd BI) := by
    apply hb
    ext U t
    exact I.ringAdd _ (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) (ringAdd B) (fun _ _ ↦ rfl) U t
  have hm : let := ringMonoid BI
            let := ringMonoid B
            let := V.monObjObj (rset BI)
            IsMonHom d := by
    let := ringMonoid BI
    let := ringMonoid B
    let := V.monObjObj (rset BI)
    constructor
    · apply adjunct_constant L V adj _ _ (ringOne B) (ringOne BI) g
      ext U t
      exact I.ringOne _ (ringOne B) (fun _ _ ↦ rfl) U t
    · apply hb
      ext U t
      exact I.ringMul _ (CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.snd _ _) (ringMul B) (fun _ _ ↦ rfl) U t
  let P := imageFunctor V BI B d ha hm
  refine ⟨P, imageFunctorUnderlying V BI B d ha hm, ?_⟩
  intro H
  constructor
  · change (fromProd _ _ ≫ addition B (imageModule V BI B d ha hm H)) =
        prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (fromProd _ _ ≫ addition BI H)
    rw [imageModule_addition, V.map_comp, ← fromProd_comparison]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.map_id_id, Category.id_comp]
    rfl
  · change (fromProd _ _ ≫ action B (imageModule V BI B d ha hm H)) =
        prod.map d (𝟙 _) ≫ inv (prodComparison V _ _) ≫
          V.map (fromProd _ _ ≫ action BI H)
    exact imageModule_action_comparison_right V BI B d ha hm H

attribute [local irreducible] mateIsoEquiv restrictHomEquiv

private theorem rawHom
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    [PreservesLimits f.direct]
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (I : AlgebraicInverseImage (JC := J) (JD := K) f.inverse B BI)
    (P : SheafOfModules.{w} (ring BI) ⥤ SheafOfModules.{w} (ring B))
    (eP : P ⋙ underlyingRaw B ≅ underlyingRaw BI ⋙ f.direct)
    (hOps : ∀ (H : SheafOfModules.{w} (ring BI)), madd B (P.obj H) ≫ eP.hom.app H =
        prod.map (eP.hom.app H) (eP.hom.app H) ≫
          inv (prodComparison f.direct ((underlyingRaw BI).obj H)
            ((underlyingRaw BI).obj H)) ≫ f.direct.map (madd BI H) ∧
      msmul B (P.obj H) ≫ eP.hom.app H =
        prod.map (f.adj.homEquiv _ _ I.ringUnderlying.hom) (eP.hom.app H) ≫
          inv (prodComparison f.direct (rset BI) ((underlyingRaw BI).obj H)) ≫
            f.direct.map (msmul BI H)) :
    ∃ A : ∀ (M : SheafOfModules.{w} (ring B)) (H : SheafOfModules.{w} (ring BI)),
      (I.modules.obj M ⟶ H) ≃ (M ⟶ P.obj H),
      ∀ M H h, (underlyingRaw B).map (A M H h) ≫ eP.hom.app H =
        f.adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ (underlyingRaw BI).map h) := by
  let : PreservesFiniteLimits f.inverse := f.leftExact
  let : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let E := fun M H ↦ mateIsoEquiv f.adj (I.moduleUnderlying.app M) (eP.app H)
  have hImage M H (α : (underlyingRaw BI).obj (I.modules.obj M) ⟶
      (underlyingRaw BI).obj H) :
      (∃ h : I.modules.obj M ⟶ H, (underlyingRaw BI).map h = α) ↔
      ∃ h : M ⟶ P.obj H, (underlyingRaw B).map h = E M H α := by
    have hLA : f.inverse.map (madd B M) =
        prodComparison f.inverse ((underlyingRaw B).obj M) ((underlyingRaw B).obj M) ≫
          prod.map (I.moduleUnderlying.inv.app M) (I.moduleUnderlying.inv.app M) ≫
            madd BI (I.modules.obj M) ≫ I.moduleUnderlying.hom.app M := by
      apply (cancel_mono (I.moduleUnderlying.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph f.inverse (I.moduleUnderlying.inv.app M)
        (I.moduleUnderlying.inv.app M) (I.moduleUnderlying.inv.app M)
        (madd B M) (madd BI (I.modules.obj M))
        (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
        (towerAddSpec B M) (towerAddSpec BI (I.modules.obj M))
        (fun T a b t ht V x ↦ I.moduleAdd M T a b t ht V x)
    have hLS : f.inverse.map (msmul B M) =
        prodComparison f.inverse (rset B) ((underlyingRaw B).obj M) ≫
          prod.map I.ringUnderlying.hom (I.moduleUnderlying.inv.app M) ≫
            msmul BI (I.modules.obj M) ≫ I.moduleUnderlying.hom.app M := by
      apply (cancel_mono (I.moduleUnderlying.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph f.inverse I.ringUnderlying.hom (I.moduleUnderlying.inv.app M)
        (I.moduleUnderlying.inv.app M) (msmul B M) (msmul BI (I.modules.obj M))
        (fun U x y ↦ @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @SMul.smul (BI.obj.obj U) ((I.modules.obj M).val.obj U)
          inferInstance x y)
        (towerSMulSpec B M) (towerSMulSpec BI (I.modules.obj M))
        (fun T a b t ht V x ↦ I.moduleSMul M T a b t ht V x)
    have hm : f.adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ α) =
        E M H α ≫ eP.hom.app H :=
      mateIsoEquiv_equation f.adj (I.moduleUnderlying.app M) (eP.app H) α
    have hAdd := binary_mate_iso_iff f.adj
      (I.moduleUnderlying.app M) (I.moduleUnderlying.app M) (I.moduleUnderlying.app M)
      (eP.hom.app H) (eP.hom.app H) (eP.app H)
      (madd B M) (madd BI (I.modules.obj M)) (madd BI H) (madd B (P.obj H))
      hLA (hOps H).1 α α α (E M H α) (E M H α) (E M H α) hm hm hm
    have hSmul := binary_mate_iso_iff f.adj I.ringUnderlying.symm
      (I.moduleUnderlying.app M) (I.moduleUnderlying.app M)
      (f.adj.homEquiv _ _ I.ringUnderlying.hom) (eP.hom.app H) (eP.app H)
      (msmul B M) (msmul BI (I.modules.obj M)) (msmul BI H) (msmul B (P.obj H))
      hLS (hOps H).2 (𝟙 _) α α (𝟙 _) (E M H α) (E M H α)
      (by simp) hm hm
    have hX := linear_iff (𝟙 BI) (I.modules.obj M) H
      (madd BI (I.modules.obj M)) (madd BI H)
      (msmul BI (I.modules.obj M)) (msmul BI H)
      (towerAddSpec BI (I.modules.obj M)) (towerAddSpec BI H)
      (towerSMulSpec BI (I.modules.obj M)) (towerSMulSpec BI H) α
    have hY := linear_iff (𝟙 B) M (P.obj H) (madd B M) (madd B (P.obj H))
      (msmul B M) (msmul B (P.obj H))
      (towerAddSpec B M) (towerAddSpec B (P.obj H))
      (towerSMulSpec B M) (towerSMulSpec B (P.obj H)) (E M H α)
    exact hX.trans ((and_congr hAdd hSmul).trans hY.symm)
  refine ⟨fun M H ↦ restrictHomEquiv (underlyingRaw BI) (underlyingRaw B)
    (E M H) (hImage M H), ?_⟩
  intro M H h
  rw [restrictHomEquiv_map]
  exact (mateIsoEquiv_equation f.adj (I.moduleUnderlying.app M) (eP.app H) _).symm

private theorem transpose_pair
    {A D : Type*} [Category A] [Category D] [HasBinaryProducts A]
    [HasBinaryProducts D] {L : A ⥤ D} {R : D ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts R] {T : A} {X Y Z : D}
    (a : T ⟶ R.obj X) (b : T ⟶ R.obj Y) (o : X ⨯ Y ⟶ Z) :
    (adj.homEquiv T Z).symm
      (prod.lift a b ≫ inv (prodComparison R X Y) ≫ R.map o) =
        prod.lift ((adj.homEquiv T X).symm a) ((adj.homEquiv T Y).symm b) ≫ o := by
  apply (adj.homEquiv T Z).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  have hp : prod.lift ((adj.homEquiv T X).symm a) ((adj.homEquiv T Y).symm b) =
      L.map (prod.lift (𝟙 T) (𝟙 T)) ≫ prodComparison L T T ≫
        prod.map ((adj.homEquiv T X).symm a) ((adj.homEquiv T Y).symm b) := by
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd, prod.map_fst,
        prod.map_snd, prodComparison_fst_assoc, prodComparison_snd_assoc] <;>
      rw [← Category.assoc, ← L.map_comp] <;> simp
  rw [hp, adj.homEquiv_naturality_left, product_mate]
  simp only [Equiv.apply_symm_apply, ← Category.assoc, prod.lift_map, Category.id_comp]

private theorem normalized_left
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      (JC := J) (JD := K) f.inverse B BI)
    {E E' : Sheaf J (Type w)} (u : E' ⟶ E)
    (H : SheafOfModules.{w} (ring BI)) (h : F.modules.obj ((free B).obj E) ⟶ H) :
    inverseFreeRestriction f F E' H (F.modules.map ((free B).map u) ≫ h) =
      f.inverse.map u ≫ inverseFreeRestriction f F E H h := by
  have hg := (freeModule_restrict_naturality B E' E u ((free B).obj E)
    ((free B).obj E)).1 (𝟙 _)
  simp only [restrictGenerators, Functor.map_id, Category.comp_id] at hg
  have hg' : generator B E' ≫ (moduleSets B).map ((free B).map u) =
      u ≫ generator B E := by
    ext U x
    exact congrArg ULift.up (congrArg (fun a ↦ a.hom.app U x) hg)
  unfold inverseFreeRestriction
  rw [(moduleSets BI).map_comp]
  have hn := F.moduleUnderlying.inv.naturality ((free B).map u)
  change (moduleSets B ⋙ f.inverse).map ((free B).map u) ≫
      F.moduleUnderlying.inv.app ((free B).obj E) =
    F.moduleUnderlying.inv.app ((free B).obj E') ≫
      (moduleSets BI).map (F.modules.map ((free B).map u)) at hn
  rw [← Category.assoc (F.moduleUnderlying.inv.app _), ← hn]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k ↦ (f.inverse.map k ≫
    F.moduleUnderlying.inv.app ((free B).obj E)) ≫ (moduleSets BI).map h) hg'

omit [EssentiallySmall.{w} C] in
private theorem lift_operation {T X Y Z : Sheaf J (Type w)}
    (o : X ⨯ Y ⟶ Z) (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (hs : ∀ U p, o.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (a : T ⟶ X) (b : T ⟶ Y) (U : Cᵒᵖ) (x : T.obj.obj U) :
    (prod.lift a b ≫ o).hom.app U x = op U (a.hom.app U x) (b.hom.app U x) := by
  have hf := congrArg (fun k ↦ k.hom.app U x) (prod.lift_fst a b)
  have hg := congrArg (fun k ↦ k.hom.app U x) (prod.lift_snd a b)
  change o.hom.app U ((prod.lift a b).hom.app U x) = _
  rw [hs]
  exact congrArg₂ (op U) hf hg

private theorem rawGraphs
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    [PreservesLimits f.direct]
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (I : AlgebraicInverseImage (JC := J) (JD := K) f.inverse B BI)
    (P : SheafOfModules.{w} (ring BI) ⥤ SheafOfModules.{w} (ring B))
    (eP : P ⋙ underlyingRaw B ≅ underlyingRaw BI ⋙ f.direct)
    (hOps : ∀ (H : SheafOfModules.{w} (ring BI)), madd B (P.obj H) ≫ eP.hom.app H =
        prod.map (eP.hom.app H) (eP.hom.app H) ≫
          inv (prodComparison f.direct ((underlyingRaw BI).obj H)
            ((underlyingRaw BI).obj H)) ≫ f.direct.map (madd BI H) ∧
      msmul B (P.obj H) ≫ eP.hom.app H =
        prod.map (f.adj.homEquiv _ _ I.ringUnderlying.hom) (eP.hom.app H) ≫
          inv (prodComparison f.direct (rset BI) ((underlyingRaw BI).obj H)) ≫
            f.direct.map (msmul BI H)) :
    (∀ (H : SheafOfModules.{w} (ring BI)) (T : Sheaf J (Type w))
      (a b t : T ⟶ (underlyingRaw B).obj (P.obj H)),
      (∀ U x, t.hom.app U x =
        @Add.add ((P.obj H).val.obj U) inferInstance (a.hom.app U x) (b.hom.app U x)) →
      ∀ V x, ((f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
        (t ≫ eP.hom.app H)).hom.app V x =
      @Add.add (H.val.obj V) inferInstance
        (((f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
          (a ≫ eP.hom.app H)).hom.app V x)
        (((f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
          (b ≫ eP.hom.app H)).hom.app V x)) ∧
    (∀ (H : SheafOfModules.{w} (ring BI)) (T : Sheaf J (Type w))
      (a : T ⟶ rset B) (b t : T ⟶ (underlyingRaw B).obj (P.obj H)),
      (∀ U x, t.hom.app U x = @SMul.smul (B.obj.obj U) ((P.obj H).val.obj U)
        inferInstance (a.hom.app U x) (b.hom.app U x)) →
      ∀ V x, ((f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
        (t ≫ eP.hom.app H)).hom.app V x =
      @SMul.smul (BI.obj.obj V) (H.val.obj V) inferInstance
        ((f.inverse.map a ≫ I.ringUnderlying.hom).hom.app V x)
        (((f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
          (b ≫ eP.hom.app H)).hom.app V x)) := by
  constructor
  · intro H T a b t ht V x
    have he : t = prod.lift a b ≫ madd B (P.obj H) := by
      ext U y
      exact (ht U y).trans (lift_operation (madd B (P.obj H))
        (fun U x y ↦ @Add.add ((P.obj H).val.obj U) inferInstance x y)
        (towerAddSpec B (P.obj H)) a b U y).symm
    have he' : t ≫ eP.hom.app H =
        prod.lift (a ≫ eP.hom.app H) (b ≫ eP.hom.app H) ≫
          inv (prodComparison f.direct _ _) ≫ f.direct.map (madd BI H) := by
      rw [he, Category.assoc, (hOps H).1]
      simp only [← Category.assoc, prod.lift_map]
    rw [he', transpose_pair]
    exact lift_operation (J := K) (madd BI H)
      (fun V x y ↦ @Add.add (H.val.obj V) inferInstance x y)
      (towerAddSpec BI H) _ _ V x
  · intro H T a b t ht V x
    have he : t = prod.lift a b ≫ msmul B (P.obj H) := by
      ext U y
      exact (ht U y).trans (lift_operation (msmul B (P.obj H))
        (fun U x y ↦ @SMul.smul (B.obj.obj U) ((P.obj H).val.obj U) inferInstance x y)
        (towerSMulSpec B (P.obj H)) a b U y).symm
    have he' : t ≫ eP.hom.app H =
        prod.lift (a ≫ f.adj.homEquiv _ _ I.ringUnderlying.hom) (b ≫ eP.hom.app H) ≫
          inv (prodComparison f.direct _ _) ≫ f.direct.map (msmul BI H) := by
      rw [he, Category.assoc, (hOps H).2]
      simp only [← Category.assoc, prod.lift_map]
    rw [he', transpose_pair, f.adj.homEquiv_naturality_left_symm,
      Equiv.symm_apply_apply]
    exact lift_operation (J := K) (msmul BI H)
      (fun V x y ↦ @SMul.smul (BI.obj.obj V) (H.val.obj V) inferInstance x y)
      (towerSMulSpec BI H) _ _ V x

private theorem map_iso_cancel
    {A D : Type*} [Category A] [Category D] (L : A ⥤ D)
    {T X Y : A} {Z Q : D} (e : X ≅ Y) (a : T ⟶ Y)
    (b : L.obj Y ⟶ Z) (c : Z ⟶ Q) :
    L.map (a ≫ e.inv) ≫ (L.map e.hom ≫ b ≫ c) = (L.map a ≫ b) ≫ c := by
  rw [L.map_comp]
  simp only [Category.assoc, ← L.map_comp_assoc, e.inv_hom_id,
    L.map_id, Category.id_comp]

private theorem normalized_hom_naturality
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      (JC := J) (JD := K) f.inverse B BI)
    (P : SheafOfModules.{w} (ring BI) ⥤ SheafOfModules.{w} (ring B))
    (eP : P ⋙ moduleSets B ≅ moduleSets BI ⋙ f.direct)
    (A : ∀ E H, (F.modules.obj ((free B).obj E) ⟶ H) ≃ ((free B).obj E ⟶ P.obj H))
    (hA : ∀ E H h, (moduleSets B).map (A E H h) ≫ eP.hom.app H =
      f.adj.homEquiv _ _ (F.moduleUnderlying.inv.app ((free B).obj E) ≫
        (moduleSets BI).map h)) :
    (∀ E E' (u : E' ⟶ E) H h,
      A E' H (F.modules.map ((free B).map u) ≫ h) = (free B).map u ≫ A E H h) ∧
    (∀ E H H' (v : H ⟶ H') h, A E H' (h ≫ v) = A E H h ≫ P.map v) := by
  constructor
  · intro E E' u H h
    apply (moduleSets B).map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    rw [hA, (moduleSets B).map_comp, Category.assoc, hA]
    rw [(moduleSets BI).map_comp]
    have hn : F.moduleUnderlying.inv.app ((free B).obj E') ≫
        (moduleSets BI).map (F.modules.map ((free B).map u)) =
      f.inverse.map ((moduleSets B).map ((free B).map u)) ≫
        F.moduleUnderlying.inv.app ((free B).obj E) :=
      (F.moduleUnderlying.inv.naturality ((free B).map u)).symm
    rw [← Category.assoc, hn, Category.assoc, f.adj.homEquiv_naturality_left]
  · intro E H H' v h
    apply (moduleSets B).map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    rw [hA, (moduleSets B).map_comp, Category.assoc]
    have hn : (moduleSets B).map (P.map v) ≫ eP.hom.app H' =
        eP.hom.app H ≫ f.direct.map ((moduleSets BI).map v) := eP.hom.naturality v
    rw [hn, ← Category.assoc, hA, (moduleSets BI).map_comp]
    change f.adj.homEquiv _ _ (F.moduleUnderlying.inv.app ((free B).obj E) ≫
      ((moduleSets BI).map h ≫ (moduleSets BI).map v)) = _
    rw [← Category.assoc, f.adj.homEquiv_naturality_right]

-- The large conjunction checks both transported operations and every Hom naturality equation.
/-- The module adjunction, free-module bijection, and inverse set adjunction form the
claimed natural chain, whose composite is restriction to the inverse-image generator.
The existential right functor carries the prescribed direct-image operations, not an
unspecified adjoint. Source: Stacks 03D2, 03D3, 04BL and 08TQ
(auxiliary; not a blueprint node).

Proof: (1) apply geometric_module_construction with R = B, A = S = BI and c = id.
Its comparisons transport exactly the operations of F, so uniqueness of transported
operations identifies its left functor with F.modules. Its right functor P has underlying
f.direct and scalar action restricted along B to f.direct BI; the two graph clauses
below are the adjunct forms of those addition and scalar-action comparisons.
(2) geometric_module_transport restricts the given set adjunction to linear maps.
At B[E] this gives A, normalized by the first equation below. Its naturality gives
the two equations for A. (3) freeModule_restrict_bijective gives G by restriction to
i, and freeModule_restrict_naturality gives its two naturality equations. Follow G
by the underlying comparison eP and the inverse of f.adj.homEquiv. Counit naturality
moves the map h past the counit, and the triangle identity cancels the counit against
the image of the unit. The composite is therefore exactly h after L(i), as displayed.
(4) each arrow is bijective, so inverseFreeRestriction is bijective for every H.
Functoriality and generator naturality give the two final equations, proving naturality
in E and H. The third arrow is the given inverse set adjunction and is natural too. -/
theorem geometricFreeModule_hom_chain
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) :
    ∃ (P : SheafOfModules.{w} (ring BI) ⥤
        SheafOfModules.{w} (ring B))
      (eP : P ⋙ moduleSets B ≅ moduleSets BI ⋙ f.direct),
      (∀ (H : SheafOfModules.{w} (ring BI)) (T : Sheaf J (Type w))
        (a b t : T ⟶ (moduleSets B).obj (P.obj H)),
        (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
          @id ((P.obj H).val.obj U) (t.hom.app U x).down =
            @id ((P.obj H).val.obj U) (a.hom.app U x).down +
              @id ((P.obj H).val.obj U) (b.hom.app U x).down) →
        ∀ (V : Dᵒᵖ) (x : (f.inverse.obj T).obj.obj V),
          @id (H.val.obj V) ((directModuleTranspose f (eP.app H) t).hom.app V x).down =
            @id (H.val.obj V) ((directModuleTranspose f (eP.app H) a).hom.app V x).down +
              @id (H.val.obj V) ((directModuleTranspose f (eP.app H) b).hom.app V x).down) ∧
      (∀ (H : SheafOfModules.{w} (ring BI)) (T : Sheaf J (Type w))
        (a : T ⟶ (sheafCompose J
          (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B)
        (b t : T ⟶ (moduleSets B).obj (P.obj H)),
        (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
          @id ((P.obj H).val.obj U) (t.hom.app U x).down =
            @id (B.obj.obj U) (a.hom.app U x).down •
              @id ((P.obj H).val.obj U) (b.hom.app U x).down) →
        ∀ (V : Dᵒᵖ) (x : (f.inverse.obj T).obj.obj V),
          @id (H.val.obj V) ((directModuleTranspose f (eP.app H) t).hom.app V x).down =
            @id (BI.obj.obj V)
              ((f.inverse.map a ≫ F.ringUnderlying.hom).hom.app V x).down •
                @id (H.val.obj V)
                  ((directModuleTranspose f (eP.app H) b).hom.app V x).down) ∧
      ∃ (A : ∀ (E : Sheaf J (Type w))
          (H : SheafOfModules.{w} (ring BI)),
          (F.modules.obj ((free B).obj E) ⟶ H) ≃ ((free B).obj E ⟶ P.obj H))
        (G : ∀ (E : Sheaf J (Type w))
          (H : SheafOfModules.{w} (ring BI)),
          ((free B).obj E ⟶ P.obj H) ≃ (E ⟶ (moduleSets B).obj (P.obj H))),
        (∀ (E : Sheaf J (Type w)) (H : SheafOfModules.{w} (ring BI))
          (h : F.modules.obj ((free B).obj E) ⟶ H),
          (moduleSets B).map (A E H h) ≫ eP.hom.app H =
            f.adj.homEquiv _ _ (F.moduleUnderlying.inv.app ((free B).obj E) ≫
              (moduleSets BI).map h)) ∧
        (∀ (E : Sheaf J (Type w)) (H : SheafOfModules.{w} (ring BI))
          (b : (free B).obj E ⟶ P.obj H),
          G E H b = generator B E ≫ (moduleSets B).map b) ∧
        (∀ (E : Sheaf J (Type w)) (H : SheafOfModules.{w} (ring BI))
          (h : F.modules.obj ((free B).obj E) ⟶ H),
          (f.adj.homEquiv E ((moduleSets BI).obj H)).symm
            (G E H (A E H h) ≫ eP.hom.app H) = inverseFreeRestriction f F E H h) ∧
        (∀ (E E' : Sheaf J (Type w)) (u : E' ⟶ E)
          (H : SheafOfModules.{w} (ring BI))
          (h : F.modules.obj ((free B).obj E) ⟶ H),
          A E' H (F.modules.map ((free B).map u) ≫ h) =
            (free B).map u ≫ A E H h) ∧
        (∀ (E : Sheaf J (Type w))
          (H H' : SheafOfModules.{w} (ring BI))
          (v : H ⟶ H') (h : F.modules.obj ((free B).obj E) ⟶ H),
          A E H' (h ≫ v) = A E H h ≫ P.map v) ∧
        (∀ (E E' : Sheaf J (Type w)) (u : E' ⟶ E)
          (H : SheafOfModules.{w} (ring BI))
          (b : (free B).obj E ⟶ P.obj H),
          G E' H ((free B).map u ≫ b) = u ≫ G E H b) ∧
        (∀ (E : Sheaf J (Type w))
          (H H' : SheafOfModules.{w} (ring BI))
          (v : H ⟶ H') (b : (free B).obj E ⟶ P.obj H),
          G E H' (b ≫ P.map v) = G E H b ≫ (moduleSets B).map (P.map v)) ∧
        (∀ (E : Sheaf J (Type w)) (H : SheafOfModules.{w} (ring BI)),
          Function.Bijective (inverseFreeRestriction f F E H)) ∧
        (∀ (E E' : Sheaf J (Type w)) (u : E' ⟶ E)
          (H : SheafOfModules.{w} (ring BI))
          (h : F.modules.obj ((free B).obj E) ⟶ H),
          inverseFreeRestriction f F E' H (F.modules.map ((free B).map u) ≫ h) =
            f.inverse.map u ≫ inverseFreeRestriction f F E H h) ∧
        (∀ (E : Sheaf J (Type w))
          (H H' : SheafOfModules.{w} (ring BI))
          (v : H ⟶ H') (h : F.modules.obj ((free B).obj E) ⟶ H),
          inverseFreeRestriction f F E H' (h ≫ v) =
            inverseFreeRestriction f F E H h ≫ (moduleSets BI).map v) := by
  classical
  let : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let I := rawPresentation (J := J) (K := K) (B := B) (BI := BI) f F
  obtain ⟨P, eR, hOps⟩ := rawRight (C := C) (D := D) (J := J) (K := K) (B := B) (BI := BI) f I
  obtain ⟨AR, hAR⟩ := rawHom (J := J) (K := K) (B := B) (BI := BI) f I P eR hOps
  obtain ⟨hAdd, hSmul⟩ := rawGraphs (J := J) (K := K) (B := B) (BI := BI) f I P eR hOps
  let eP : P ⋙ moduleSets B ≅ moduleSets BI ⋙ f.direct :=
    Functor.isoWhiskerLeft P (moduleLift B).symm ≪≫ eR ≪≫
      Functor.isoWhiskerRight (moduleLift BI) f.direct
  let A : ∀ (E : Sheaf J (Type w)) (H : SheafOfModules.{w} (ring BI)),
      (F.modules.obj ((free B).obj E) ⟶ H) ≃ ((free B).obj E ⟶ P.obj H) :=
    fun E H ↦ AR ((free B).obj E) H
  let G := fun E H ↦ (Equiv.ofBijective (restrictGenerators B E (P.obj H))
    (freeModule_restrict_bijective B E (P.obj H))).trans
      (Iso.homToEquiv ((moduleLift B).app (P.obj H)))
  have hA E H h : (moduleSets B).map (A E H h) ≫ eP.hom.app H =
      f.adj.homEquiv _ _ (F.moduleUnderlying.inv.app ((free B).obj E) ≫
        (moduleSets BI).map h) := by
    have hr := hAR ((free B).obj E) H h
    have hi : I.moduleUnderlying.inv.app ((free B).obj E) ≫
        (underlyingRaw BI).map h =
        f.inverse.map ((moduleLift B).hom.app ((free B).obj E)) ≫
          (F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map h) ≫
            (moduleLift BI).inv.app H := by
      simp only [I, rawPresentation, Iso.trans_inv, NatTrans.comp_app,
        Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv]
      rfl
    rw [hi, f.adj.homEquiv_naturality_left, f.adj.homEquiv_naturality_right] at hr
    apply (cancel_epi ((moduleLift B).hom.app ((free B).obj E))).mp
    change (moduleLift B).hom.app ((free B).obj E) ≫
      ((moduleSets B).map (A E H h) ≫
        ((moduleLift B).inv.app (P.obj H) ≫ eR.hom.app H ≫
          f.direct.map ((moduleLift BI).hom.app H))) = _
    rw [← Category.assoc, ← (moduleLift B).hom.naturality]
    simp only [Functor.comp_map, Category.assoc, Iso.hom_inv_id_app_assoc]
    change ((underlyingRaw B).map (AR ((free B).obj E) H h) ≫
      eR.hom.app H) ≫ f.direct.map ((moduleLift BI).hom.app H) = _
    rw [hr]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Category.comp_id]
    rfl
  have hG E H b : G E H b = generator B E ≫ (moduleSets B).map b := by
    rfl
  have hcomp E H h : (f.adj.homEquiv E ((moduleSets BI).obj H)).symm
      (G E H (A E H h) ≫ eP.hom.app H) = inverseFreeRestriction f F E H h := by
    rw [hG, Category.assoc, hA, f.adj.homEquiv_naturality_left_symm,
      Equiv.symm_apply_apply]
    rfl
  have htrans (H : SheafOfModules.{w} (ring BI)) (T : Sheaf J (Type w))
      (a : T ⟶ (moduleSets B).obj (P.obj H)) :
      directModuleTranspose f (eP.app H) a =
        (f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
          (a ≫ (moduleLift B).inv.app (P.obj H) ≫ eR.hom.app H) ≫
            (moduleLift BI).hom.app H := by
    change (f.adj.homEquiv T ((moduleSets BI).obj H)).symm
      ((a ≫ (moduleLift B).inv.app (P.obj H) ≫ eR.hom.app H) ≫
        f.direct.map ((moduleLift BI).hom.app H)) = _
    exact f.adj.homEquiv_naturality_right_symm _ _
  refine ⟨P, eP, ?_, ?_, A, G, hA, hG, hcomp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H T a b t ht V x
    have h := hAdd H T (a ≫ (moduleLift B).inv.app (P.obj H))
      (b ≫ (moduleLift B).inv.app (P.obj H))
      (t ≫ (moduleLift B).inv.app (P.obj H)) ht V x
    rw [htrans, htrans, htrans]
    exact h
  · intro H T a b t ht V x
    have h := hSmul H T (a ≫ (ringLift B).inv)
      (b ≫ (moduleLift B).inv.app (P.obj H))
      (t ≫ (moduleLift B).inv.app (P.obj H)) ht V x
    rw [htrans, htrans]
    have he : f.inverse.map (a ≫ (ringLift B).inv) ≫
        I.ringUnderlying.hom =
      (f.inverse.map a ≫ F.ringUnderlying.hom) ≫
        (ringLift BI).inv := by
      exact map_iso_cancel f.inverse (ringLift B) a F.ringUnderlying.hom
        (ringLift BI).inv
    have hcoeff : (f.inverse.map (a ≫ (ringLift B).inv) ≫
        I.ringUnderlying.hom).hom.app V x =
        ((f.inverse.map a ≫ F.ringUnderlying.hom).hom.app V x).down :=
      congrArg (fun k ↦ k.hom.app V x) he
    exact h.trans (congrArg (fun r : BI.obj.obj V ↦
      @SMul.smul (BI.obj.obj V) (H.val.obj V) inferInstance r
      (((f.adj.homEquiv T ((underlyingRaw BI).obj H)).symm
        ((b ≫ (moduleLift B).inv.app (P.obj H)) ≫ eR.hom.app H)).hom.app V x)) hcoeff)
  · exact (normalized_hom_naturality (J := J) (K := K) (B := B) (BI := BI) f F P eP A hA).1
  · exact (normalized_hom_naturality (J := J) (K := K) (B := B) (BI := BI) f F P eP A hA).2
  · intro E E' u H b
    change restrictGenerators B E' (P.obj H) ((free B).map u ≫ b) ≫
      (moduleLift B).hom.app (P.obj H) = _
    rw [(freeModule_restrict_naturality B E' E u (P.obj H) (P.obj H)).1,
      Category.assoc]
    rfl
  · intro E H H' v b
    rw [hG, hG, (moduleSets B).map_comp, Category.assoc]
  · intro E H
    have he : inverseFreeRestriction f F E H =
        ((A E H).trans ((G E H).trans ((Iso.homToEquiv (eP.app H)).trans
          (f.adj.homEquiv E ((moduleSets BI).obj H)).symm))).toFun := by
      funext h
      exact (hcomp E H h).symm
    rw [he]
    exact Equiv.bijective _
  · intro E E' u H h
    exact normalized_left (J := J) (K := K) (B := B) (BI := BI) f F u H h
  · intro E H H' v h
    simp only [inverseFreeRestriction, Functor.map_comp, Category.assoc]

end CategoryTheory.SheafFreeModule
