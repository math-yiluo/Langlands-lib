/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction

import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison

/-!
# Geometric inverse image of free module sheaves

Source: Stacks Project, Modules on Sites, Tags 04BL, 03CY, 03D3 and 08TQ
(auxiliary; not a blueprint node).

The free module is module sheafification of the sectionwise free module, on an arbitrary
sheaf of generators. Algebraic inverse-image presentations record precisely the transported
operations. Underlying modules use the common value universe of that recorded interface.
-/

@[expose] public section

universe w wI uC vC uD vD uH vH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafFreeModule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {K : GrothendieckTopology D}

local instance : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

local instance : J.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : J.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

local instance : K.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : K.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

private def rawLift (B : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (ring B)) :
    (underlyingRaw B).obj M ≅ (moduleSets B).obj M where
  hom := ⟨{ app := fun _ ↦ ↾ULift.up, naturality := by intros; rfl }⟩
  inv := ⟨{ app := fun _ ↦ ↾ULift.down, naturality := by intros; rfl }⟩

private theorem rawLift_naturality (B : Sheaf J CommRingCat.{w})
    {M N : SheafOfModules.{w} (ring B)} (a : M ⟶ N) :
    (underlyingRaw B).map a ≫ (rawLift B N).hom =
      (rawLift B M).hom ≫ (moduleSets B).map a := rfl

private theorem generator_lift (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    generatorRaw B E ≫ (rawLift B ((free B).obj E)).hom = generator B E := rfl

private theorem generator_naturality (B : Sheaf J CommRingCat.{w})
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    generator B E ≫ (moduleSets B).map ((free B).map e) = e ≫ generator B E' := by
  have h := (freeModule_restrict_naturality B E E' e
    ((free B).obj E') ((free B).obj E')).1 (𝟙 _)
  have hh := congrArg (fun a ↦ a ≫ (rawLift B ((free B).obj E')).hom) h
  simp only [restrictGenerators, Functor.map_id, Category.comp_id, Category.assoc,
    rawLift_naturality, generator_lift] at hh
  rw [← Category.assoc, generator_lift] at hh
  exact hh

private def identityUnderlying
    (B : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uC, vC, w, w}
      (𝟭 (Sheaf J (Type w))) B B)
    (hB : F.ringUnderlying = Iso.refl ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B))
    (M : SheafOfModules.{w} (ring B)) : M ⟶ F.modules.obj M := by
  let α := F.moduleUnderlying.inv.app M
  refine { val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun x ↦ (α.hom.app U (ULift.up x)).down
          map_add' := ?_
          map_smul' := ?_ }
      naturality := ?_ } }
  · intro x y
    let T := (underlyingRaw B).obj M ⊗ (underlyingRaw B).obj M
    let a : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.1, naturality := by intros; rfl }⟩
    let b : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.2, naturality := by intros; rfl }⟩
    let t : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun V ↦ ↾fun z ↦ ULift.up
           (@id (M.val.obj V) z.1 + @id (M.val.obj V) z.2)
         naturality := by
           intro U V i
           ext z
           exact congrArg ULift.up ((M.val.map i).hom.map_add _ _).symm }⟩
    exact F.moduleAdd M T a b t (fun _ _ ↦ rfl) U (x, y)
  · intro a x
    let R := (sheafCompose J (forget CommRingCat.{w})).obj B
    let T := R ⊗ (underlyingRaw B).obj M
    let r : T ⟶ (sheafCompose J
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.1, naturality := by intros; rfl }⟩
    let b : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun _ ↦ ↾fun z ↦ ULift.up z.2, naturality := by intros; rfl }⟩
    let t : T ⟶ (moduleSets B).obj M :=
      ⟨{ app := fun V ↦ ↾fun z ↦ ULift.up
           (@id (B.obj.obj V) z.1 • @id (M.val.obj V) z.2)
         naturality := by
           intro U V i
           ext z
           exact congrArg ULift.up ((M.val.map i).hom.map_smulₛₗ _ _).symm }⟩
    simpa [α, t, r, b, hB] using F.moduleSMul M T r b t (fun _ _ ↦ rfl) U (a, x)
  · intro U V i
    ext x
    exact congrArg ULift.down (congrArg (fun a ↦ a (ULift.up x))
      (α.hom.naturality i))

private theorem transportedFreeProperty
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w)) :
    HasTransportedFreeUniversalProperty f.inverse F E := by
  obtain ⟨P, eP, hAdd, hSmul, A, G, hA, hG, hChain, hAL, hAR, hGL, hGR,
    hBij, hEL, hER⟩ := geometricFreeModule_hom_chain f F
  exact hBij E

/-- The underlying comparison with the canonical inverse-image identification retained.
Source: Stacks 08TQ (auxiliary; not a blueprint node). -/
noncomputable def comparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E)) :
    f.inverse.obj ((moduleSets B).obj ((free B).obj E)) ⟶
      (moduleSets BI).obj ((free BI).obj (f.inverse.obj E)) :=
  F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map p.hom

/-- Generator normalization of the comparison, an equality of sheaf maps and hence
valid on all generalized sections. Source: Stacks 08TQ
(auxiliary; not a blueprint node). -/
def IsComparison
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E)) : Prop :=
  f.inverse.map (generator B E) ≫ comparison f F E p = generator BI (f.inverse.obj E)

/-- Inverse image preserves the free module sheaf on any sheaf of sets, with its uniquely
normalized isomorphism. Source: Stacks 04BL, 03CY, 03D3 and 08TQ
(auxiliary; not a blueprint node).

Proof: first extend a map E → |M| sectionwise by summing coefficients times the images
of generators. The free presheaf universal property and module sheafification give
Hom_B(B[E], M) ≃ Hom(E, |M|). The geometric module transport adjunction of 03D3,
with coefficient map the identity on the transported ring, then gives
Hom_BI(F(B[E]), H) ≃ Hom_B(B[E], f_* H) ≃ Hom(E, f_* |H|) ≃ Hom(f⁻¹ E, |H|).
The transport normalization identifies this bijection with restriction to f⁻¹ of the
generator map. Thus source and target are free on f⁻¹ E with those generator maps.
Extend each generator map into the other free module. Their composites fix generators,
so freeness makes them identities. This gives the isomorphism; the same uniqueness
makes it the only generator-normalized isomorphism. -/
theorem inverseFreeModule_existsUnique
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI) (E : Sheaf J (Type w)) :
    ∃! p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E),
      IsComparison f F E p := by
  let P := F.modules.obj ((free B).obj E)
  let k := f.inverse.map (generator B E) ≫ F.moduleUnderlying.inv.app ((free B).obj E)
  let kRaw := k ≫ (rawLift BI P).inv
  have hP : ∀ M : SheafOfModules.{w} (ring BI),
      Function.Bijective (fun h : P ⟶ M ↦ kRaw ≫ (underlyingRaw BI).map h) := by
    intro M
    have h := transportedFreeProperty f F E M
    have eqn (a : P ⟶ M) :
        kRaw ≫ (underlyingRaw BI).map a =
          inverseFreeRestriction f F E M a ≫ (rawLift BI M).inv := by
      ext V x
      rfl
    simp_rw [eqn]
    exact ((rawLift BI M).symm.homToEquiv).bijective.comp h
  obtain ⟨p, hp, hu⟩ := freeModule_unique_iso BI (f.inverse.obj E) P kRaw hP
  have normalize (q : P ≅ (free BI).obj (f.inverse.obj E)) :
      (kRaw ≫ (underlyingRaw BI).map q.hom = generatorRaw BI (f.inverse.obj E)) ↔
        IsComparison f F E q := by
    rw [← cancel_mono (rawLift BI ((free BI).obj (f.inverse.obj E))).hom]
    simp only [Category.assoc, rawLift_naturality, generator_lift]
    simp only [kRaw, k, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  refine ⟨p, (normalize p).mp hp.1, ?_⟩
  intro q hq
  apply Iso.ext
  have hqp := (hP ((free BI).obj (f.inverse.obj E))).1
  exact hqp (((normalize q).mpr hq).trans hp.1.symm)

/-- Naturality in both generator sheaves and coefficient-ring maps, expressed on
underlying sheaves to retain semilinear coefficient changes. The compatibility hypothesis
only identifies the transported coefficient map. Source: Stacks 04BL and 08TQ
(auxiliary; not a blueprint node).

Proof: both composites are semilinear along the same transported ring map. On f⁻¹ E
they both equal the target generator map after f⁻¹ e, by the two normalization equations
and the sectionwise definition of change. The transported free universal property
therefore identifies the two composites. Taking b and bi to be identities gives
naturality in E; taking e to be identity gives coefficient naturality. -/
theorem inverseFreeModule_naturality
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B B' : Sheaf J CommRingCat.{w}} {BI BI' : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (F' : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B' BI')
    (b : B ⟶ B') (bi : BI ⟶ BI')
    (hb : f.inverse.map ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map b) ≫ F'.ringUnderlying.hom =
      F.ringUnderlying.hom ≫ (sheafCompose K
        (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).map bi)
    {E E' : Sheaf J (Type w)} (e : E ⟶ E')
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E))
    (p' : F'.modules.obj ((free B').obj E') ≅ (free BI').obj (f.inverse.obj E'))
    (hp : IsComparison f F E p) (hp' : IsComparison f F' E' p') :
    f.inverse.map (changeSets b e) ≫ comparison f F' E' p' =
      comparison f F E p ≫ changeSets bi (f.inverse.map e) := by
  let := f.leftExact
  exact normalizedFreeModule_naturality f.inverse F F' b bi hb e
    (transportedFreeProperty f F E) p p' hp hp'

/-- Finite-product compatibility on the generator sheaves, including the empty product.
Source: Stacks 08TQ (auxiliary; not a blueprint node).

Proof: normalize the comparison at the product sheaf. The free functor applied to the
finite-product comparison carries [s] to [lambda(s)], by its sectionwise construction
and sheafification. Composing the normalization equation gives the asserted equality.
Left exactness makes lambda invertible; no product decomposition of free modules is used. -/
theorem inverseFreeModule_products
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    {I : Type wI} [Finite I] (E : I → Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj (∏ᶜ E)) ≅ (free BI).obj (f.inverse.obj (∏ᶜ E)))
    (hp : IsComparison f F (∏ᶜ E) p) :
    f.inverse.map (generator B (∏ᶜ E)) ≫ comparison f F (∏ᶜ E) p ≫
        (moduleSets BI).map ((free BI).map (piComparison f.inverse E)) =
      piComparison f.inverse E ≫ generator BI (∏ᶜ fun i ↦ f.inverse.obj (E i)) := by
  rw [← Category.assoc, hp]
  exact generator_naturality BI (piComparison f.inverse E)

/-- The identity comparison is identity after its underlying-module identification.
The ring presentation is normalized to the identity, rather than requiring equality of
chosen module structures. Source: Stacks 08TQ
(auxiliary; not a blueprint node).

Proof: both the normalized comparison and the identity fix the generator map. The free
universal property identifies them on the entire free sheaf. -/
theorem inverseFreeModule_identity
    (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w))
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uC, vC, w, w}
      (𝟭 (Sheaf J (Type w))) B B)
    (hB : F.ringUnderlying = Iso.refl ((sheafCompose J
      (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w})).obj B))
    (p : F.modules.obj ((free B).obj E) ≅ (free B).obj E)
    (hp : generator B E ≫ F.moduleUnderlying.inv.app ((free B).obj E) ≫
      (moduleSets B).map p.hom = generator B E) :
    F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets B).map p.hom =
      𝟙 ((moduleSets B).obj ((free B).obj E)) := by
  let a := identityUnderlying B F hB ((free B).obj E) ≫ p.hom
  have ha : (moduleSets B).map a =
      F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets B).map p.hom := by
    ext U x
    rfl
  have hid : a = 𝟙 _ := by
    apply (freeModule_restrict_bijective B E ((free B).obj E)).1
    apply (cancel_mono (rawLift B ((free B).obj E)).hom).mp
    simp only [restrictGenerators, Functor.map_id, Category.comp_id, Category.assoc,
      rawLift_naturality, generator_lift, ha]
    rw [← Category.assoc, generator_lift]
    exact hp
  rw [← ha, hid, Functor.map_id]


variable {H : Type uH} [Category.{vH} H] [EssentiallySmall.{w} H]
  {T : GrothendieckTopology H}

local instance : T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance

local instance : T.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

local instance : T.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance


/-- Composition coherence with the actual composite inverse image and ring comparison.
Source: Stacks 08TQ (auxiliary; not a blueprint node).

Proof: the comparison for the composite sends the twice transported generator to the
target generator. Applying g⁻¹ to the first normalization equation and then using the
second proves that the successive comparisons have the same effect. The compatibility
of the ring presentations makes both maps linear over the same target ring. The free
universal property for the composite identifies them, with the underlying-module
comparisons retained explicitly as in the equation. -/
theorem inverseFreeModule_composition
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (g : GeometricMorphism (Sheaf T (Type w)) (Sheaf K (Type w)))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    {BII : Sheaf T CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
      f.inverse B BI)
    (G : SheafOfModules.AlgebraicInverseImageOfUniverses.{uD, vD, uH, vH, w, w}
      g.inverse BI BII)
    (FG : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uH, vH, w, w}
      (g.comp f).inverse B BII)
    (hB : FG.ringUnderlying.hom =
      g.inverse.map F.ringUnderlying.hom ≫ G.ringUnderlying.hom)
    (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (f.inverse.obj E))
    (q : G.modules.obj ((free BI).obj (f.inverse.obj E)) ≅
      (free BII).obj (g.inverse.obj (f.inverse.obj E)))
    (r : FG.modules.obj ((free B).obj E) ≅
      (free BII).obj ((g.comp f).inverse.obj E))
    (hp : IsComparison f F E p) (hq : IsComparison g G (f.inverse.obj E) q)
    (hr : IsComparison (g.comp f) FG E r) :
    comparison (g.comp f) FG E r =
      g.inverse.map (comparison f F E p) ≫ comparison g G (f.inverse.obj E) q := by
  let := f.leftExact
  let := g.leftExact
  exact normalizedFreeModule_composition f.inverse g.inverse F G FG hB E
    (transportedFreeProperty (g.comp f) FG E) p q r hp hq hr

end CategoryTheory.SheafFreeModule
