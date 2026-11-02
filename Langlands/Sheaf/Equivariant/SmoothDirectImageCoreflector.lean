import Langlands.Sheaf.Equivariant.SmoothDirectImage

/-! # Smooth coreflection and actual equivariant direct image -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.SmoothDirectImage

open CategoryTheory Opposite

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- A fixed neighbourhood in the direct image pulls back to a fixed
neighbourhood of each point in its inverse image. -/
theorem isLocallyFixedAt_preimage
    (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) {U : ActionOpens G Y}
    {s : F.obj (op ((DirectImage.preimage f hf).obj U))} {x : X}
    (hs : IsLocallyFixedAt R ((DirectImage.presheaf f hf (ModuleCat.{u} R)).obj F)
      s (f x)) : IsLocallyFixedAt R F s x := by
  obtain ⟨V, hVU, H, hV, hxV, hfix⟩ := hs
  let hW : ∀ h : (H : Subgroup G), ∀ y ∈ ((DirectImage.preimage f hf).obj V).openSet,
      (h : G) • y ∈ ((DirectImage.preimage f hf).obj V).openSet := by
    intro h y hy
    change f ((h : G) • y) ∈ V.openSet
    rw [hf]
    exact hV h (f y) hy
  refine ⟨(DirectImage.preimage f hf).obj V, (fun _ hy => hVU hy), H, hW, hxV, ?_⟩
  intro h
  exact hfix h

variable [IsTopologicalGroup G]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]

/-- A locally smooth section of the direct image is locally smooth at every
point of the inverse-image open; the original section is retained. -/
def preimageSmoothMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothSubsheafFunctor R).obj ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ⟶
      (DirectImage.sheaf f hf (ModuleCat.{u} R)).obj ((smoothSubsheafFunctor R).obj F) :=
  ObjectProperty.homMk
    { app _U := ModuleCat.ofHom
        { toFun s := ⟨s.val, fun x hx => isLocallyFixedAt_preimage f hf F.obj (s.property (f x) hx)⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality _ _ _ := rfl }

@[simp]
theorem preimageSmoothMap_apply (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G Y)
    (s : ((smoothSubsheafFunctor R).obj
      ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).obj.obj (op U)) :
    (((preimageSmoothMap f hf F).hom.app (op U)).hom s).val = s.val := rfl

/-- The map is the factorization of the actual smooth-subsheaf inclusion. -/
@[reassoc (attr := simp)]
theorem preimageSmoothMap_inclusion (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    preimageSmoothMap f hf F ≫
        (DirectImage.sheaf f hf (ModuleCat.{u} R)).map ((smoothSubsheafι R).app F) =
      (smoothSubsheafι R).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) := rfl

/-- Naturality holds for every original equivariant sheaf morphism. -/
@[reassoc]
theorem preimageSmoothMap_naturality {F F' : TopologicalSheaf G X (ModuleCat.{u} R)}
    (a : F ⟶ F') :
    (smoothSubsheafFunctor R).map ((DirectImage.sheaf f hf (ModuleCat.{u} R)).map a) ≫
        preimageSmoothMap f hf F' =
      preimageSmoothMap f hf F ≫
        (DirectImage.sheaf f hf (ModuleCat.{u} R)).map ((smoothSubsheafFunctor R).map a) := rfl

@[simp]
theorem preimageSmoothMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    preimageSmoothMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      𝟙 ((smoothSubsheafFunctor R).obj F) := rfl

/-- The inverse-image smoothness factorization retains spatial composition. -/
theorem preimageSmoothMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    preimageSmoothMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      preimageSmoothMap g hg ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (DirectImage.sheaf g hg (ModuleCat.{u} R)).map (preimageSmoothMap f hf F) := rfl

/-- Smooth coreflection after full direct image maps into the smooth direct
image of the actual smooth subsheaf, retaining the original section. -/
def coreflectorMap :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ smoothCoreflector R ⟶
      smoothCoreflector R ⋙ functor (R := R) f hf where
  app F := lift f hf (preimageSmoothMap f hf F)
  naturality _ _ _ := rfl

/-- The reverse map is induced by the original smooth-subsheaf inclusion. -/
def coreflectorInclusion :
    smoothCoreflector R ⋙ functor (R := R) f hf ⟶
      DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ smoothCoreflector R where
  app F := (smoothCoreflector R).map
    ((DirectImage.sheaf f hf (ModuleCat.{u} R)).map ((smoothSubsheafι R).app F))
  naturality _ _ _ := rfl

/-- Full direct image followed by smooth coreflection is naturally isomorphic
to smooth direct image of the smooth coreflection. -/
def coreflectorIso :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ smoothCoreflector R ≅
      smoothCoreflector R ⋙ functor (R := R) f hf where
  hom := coreflectorMap f hf
  inv := coreflectorInclusion f hf
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The isomorphism forgets precisely the two local-smoothness proofs. -/
@[simp]
theorem coreflectorIso_hom_apply (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (U : ActionOpens G Y)
    (s : ((smoothCoreflector R).obj
      ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).obj.obj.obj (op U)) :
    (((((coreflectorIso f hf).hom.app F).hom.hom.app (op U)).hom s).val).val = s.val := rfl

/-- Forgetting only the outer smooth-image proof recovers the constructed
inverse-image smoothness factorization. -/
@[reassoc]
theorem coreflectorIso_hom_inclusion (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothInclusion R G Y).map ((coreflectorIso f hf).hom.app F) ≫
        (inclusion f hf).app ((smoothCoreflector R).obj F) =
      preimageSmoothMap f hf F := lift_inclusion f hf _

/-- The identity comparison is the existing smooth-direct-image unit. -/
theorem coreflectorIso_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (coreflectorIso (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)).hom.app F =
      (idIso (R := R) (G := G) (X := X)).hom.app ((smoothCoreflector R).obj F) := rfl

/-- The comparison is coherent with the actual lax composition map. -/
theorem coreflectorIso_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (coreflectorIso g hg).hom.app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (functor g hg).map ((coreflectorIso f hf).hom.app F) ≫
        (compMap f hf g hg).app ((smoothCoreflector R).obj F) =
      (coreflectorIso (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])).hom.app F := rfl

end Langlands.Sheaf.Equivariant.SmoothDirectImage
