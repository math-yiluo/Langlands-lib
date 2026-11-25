/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-! # Geometric stalks of a proper-support subsheaf

Source: Stacks Project, Tag 0F76, including the restriction normalization in the first
paragraph of its proof (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/-- The image of the proper-support stalk map is the submodule of properly supported
fibre sections. This is the support-image and extension-by-zero part of Stacks Project,
Tag 0F76. The proof constructs the image submodule, identifies membership with proper
support using base-change locality, and extends every properly supported fibre section
by zero after shrinking to a quasi-compact open and applying compactification.
(auxiliary; not a blueprint node). -/
theorem properSupport_geometricStalk_image
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F) (hi : Mono i)
    (hG : ∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
      (∃ t, i.hom.app (op V) t = s) ↔
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s)
    (c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ⟶
      upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
        (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y)))))
    (hc : ∀ (V : Y.Etale) (v : (Scheme.pointSmallEtale y).fiber.obj V)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (Scheme.pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v) :
    ∃ S : Submodule Λ
        (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y))))),
      (∀ s, s ∈ S ↔ SectionHasProperSupport Λ
        ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
        (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y) s) ∧
      ∃ e : (Scheme.pointSmallEtale y).sheafFiber.obj G ≅ ModuleCat.of Λ S,
        e.hom ≫ ModuleCat.ofHom S.subtype =
          (Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F := by
  let φ := (Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F
  obtain ⟨hφ, hmem⟩ := properSupport_geometricStalk_image_core Λ f y F G i hi hG c hc
  let S := LinearMap.range φ.hom
  refine ⟨S, ?_, ?_⟩
  · intro s
    exact hmem s
  · let e := (LinearEquiv.ofInjective φ.hom hφ).toModuleIso
    refine ⟨e, ?_⟩
    apply ModuleCat.hom_ext
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem geometricFibreSectionLift_naturality
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    {V W : Y.Etale} (a : V ⟶ W) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    geometricFibreSectionLift sq V v ≫ g'.Etale.map (f.Etale.map a) =
      geometricFibreSectionLift sq W ((Scheme.pointSmallEtale s).fiber.map a v) := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricFibreSectionLift sq V v).left ≫
    (g'.Etale.map (f.Etale.map a)).left = _
  dsimp [geometricFibreSectionLift, Hom.Etale, MorphismProperty.Over.pullback,
    Scheme.pointSmallEtale]
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · simp [Category.assoc]
      rfl
    · simp [Category.assoc]
  · simp

set_option backward.isDefEq.respectTransparency false in
private theorem geometricFibreSectionRestriction_naturality
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : CommSq g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V W : Y.Etale} (a : V ⟶ W) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    F.obj.map (f.Etale.map a).op ≫ geometricFibreSectionRestriction Λ sq F V v =
      geometricFibreSectionRestriction Λ sq F W ((Scheme.pointSmallEtale s).fiber.map a v) := by
  unfold geometricFibreSectionRestriction
  erw [← Category.assoc,
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app F).hom.naturality
      (f.Etale.map a).op]
  change _ ≫ (((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.map
    (g'.Etale.map (f.Etale.map a)).op ≫ _) = _
  rw [← Functor.map_comp, ← op_comp,
    geometricFibreSectionLift_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of direct-image germs to the geometric fibre is natural in the
module sheaf. On every proper-support subsheaf it induces a linear isomorphism onto
exactly the submodule of properly supported fibre sections. The displayed factorization
identifies its composite with the inclusion with ordinary restriction, and the germ
formula specifies that restriction on every representative.
Source: Stacks Project, Tag 0F76
(auxiliary; not a blueprint node).

Proof:
1. Pull representatives to the fibre. Properness survives base change, so their supports
remain proper; inverse-image germ compatibility identifies these with their actual supports.
2. Extension by zero across an open subscheme preserves proper support: the proper-to-separated
triangle makes the support closed in the larger scheme, and sheaf gluing extends by zero.
3. Work locally on the base, then take the filtered union of quasi-compact opens of X.
Quasi-compactness of every proper support puts both representative and fibre sections in
some such open. Exactness of geometric stalks makes the source a union of these submodules.
4. For X quasi-compact and Y affine, Nagata compactification gives X open in a proper scheme.
Extend F by zero, using its unit isomorphism and zero stalks outside X.
5. Restriction identifies the proper direct image of this extension with the given G:
its sections have closed proper support inside X, and conversely gluing with zero extends
any section with such support. These operations commute with restrictions and sheaf maps.
6. The same gluing on the geometric fibre identifies global sections of the extension with
properly supported fibre sections. Base change for extension by zero preserves this formula.
7. Proper geometric-point exchange and the pullback-stalk comparison identify the proper
stalk map with restriction on representatives. Steps 3--6 give the asserted isomorphism.
A linear map shrinks support, so preserves proper support; both naturality paths restrict
the image of the same representative, giving naturality and the displayed normalization. -/
theorem properSupport_geometricStalk
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ∃ c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ⟶
        upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
          (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (Scheme.Etale.mk (𝟙 (pullback f y)))),
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
        (v : (Scheme.pointSmallEtale y).fiber.obj V),
        (Scheme.pointSmallEtale y).toPresheafFiber V v
            ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
          geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v) ∧
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (i : G ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F), Mono i →
        (∀ (V : Y.Etale) (s : F.obj.obj (op (f.Etale.obj V))),
          (∃ t, i.hom.app (op V) t = s) ↔
            SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s) →
        ∃ S : Submodule Λ
            (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F).obj.obj
              (op (Scheme.Etale.mk (𝟙 (pullback f y))))),
          (∀ s, s ∈ S ↔ SectionHasProperSupport Λ
            ((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).obj F)
            (Scheme.Etale.mk (𝟙 (pullback f y))) (pullback.snd f y) s) ∧
          ∃ e : (Scheme.pointSmallEtale y).sheafFiber.obj G ≅ ModuleCat.of Λ S,
            e.hom ≫ ModuleCat.ofHom S.subtype =
              (Scheme.pointSmallEtale y).sheafFiber.map i ≫ c.app F := by
  let cF (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (Scheme.pointSmallEtale y).presheafFiberDesc
      (P := ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj)
      (fun V v ↦ geometricFibreSectionRestriction Λ
        (IsPullback.of_hasPullback f y).toCommSq F V v)
      (fun _ _ a v ↦ geometricFibreSectionRestriction_naturality Λ
        (IsPullback.of_hasPullback f y).toCommSq F a v)
  have hcF (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (V : Y.Etale) (v : (Scheme.pointSmallEtale y).fiber.obj V) :
      (Scheme.pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ cF F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v :=
    (Scheme.pointSmallEtale y).toPresheafFiber_presheafFiberDesc _ _ V v
  let c : lowerStar (ModuleCat.{u + 1} Λ) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ⟶
      upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y) ⋙
        (sheafSections (pullback f y).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (Scheme.Etale.mk (𝟙 (pullback f y)))) :=
    { app := cF
      naturality := by
        intro F F' h
        apply (Scheme.pointSmallEtale y).presheafFiber_hom_ext
        intro V v
        simp only [Functor.comp_map]
        rw [show (Scheme.pointSmallEtale y).sheafFiber.map
            ((lowerStar (ModuleCat.{u + 1} Λ) f).map h) =
          (Scheme.pointSmallEtale y).presheafFiber.map
            ((lowerStar (ModuleCat.{u + 1} Λ) f).map h).hom from rfl,
          GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
          hcF, ← Category.assoc]
        erw [hcF]
        unfold geometricFibreSectionRestriction
        have hu := NatTrans.congr_app (Sheaf.hom_ext_iff.1
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (pullback.fst f y)).unit.naturality h)) (op (f.Etale.obj V))
        change h.hom.app _ ≫ _ = _ ≫ _ at hu
        change h.hom.app _ ≫ _ ≫ _ = (_ ≫ _) ≫ _
        rw [← Category.assoc]
        erw [hu]
        simp only [Category.assoc]
        congr 1
        exact (((upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f y)).map h).hom.naturality
          (geometricFibreSectionLift (IsPullback.of_hasPullback f y).toCommSq V v).op).symm }
  have hc (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (V : Y.Etale) (v : (Scheme.pointSmallEtale y).fiber.obj V) :
      (Scheme.pointSmallEtale y).toPresheafFiber V v
          ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ c.app F =
        geometricFibreSectionRestriction Λ (IsPullback.of_hasPullback f y).toCommSq F V v := by
    exact hcF F V v
  refine ⟨c, hc, ?_⟩
  intro F G i hi hG
  exact properSupport_geometricStalk_image Λ f y F G i hi hG c (fun V v F ↦ hc F V v)

end AlgebraicGeometry.Etale
