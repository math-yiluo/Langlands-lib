/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.ColimitSiteRawAbelianSectionDiagram
import WeilConjectures.CategoryTheory.ColimitSiteRawAbelianSectionSheaf
import WeilConjectures.CategoryTheory.ColimitSiteRawAbelianSectionEvaluation
import Mathlib.CategoryTheory.Filtered.Final

/-! # Finite-site stage section eventual zero

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem raw_comparison_iso
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    (P : GrothendieckTopology C) (Q : GrothendieckTopology D)
    (R : GrothendieckTopology E)
    [f.IsContinuous P Q] [g.IsContinuous Q R] [h.IsContinuous P R]
    (eh : f ⋙ g = h)
    (G : Sheaf P AddCommGrpCat.{u})
    (B : Eᵒᵖ ⥤ AddCommGrpCat.{u})
    (β : ((sheafPullback f AddCommGrpCat.{u} P Q).obj G).obj ⟶ g.op ⋙ B)
    [B.IsLeftKanExtension β]
    (γ : B ⟶ ((sheafPullback h AddCommGrpCat.{u} P R).obj G).obj)
    (α : (sheafPullback f AddCommGrpCat.{u} P Q).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} Q R).obj
        ((sheafPullback h AddCommGrpCat.{u} P R).obj G))
    (hγ : β ≫ Functor.whiskerLeft g.op γ = α.hom)
    (hα : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} P Q).unit.app G).hom.app
        (op X) ≫ α.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} P R).unit.app G).hom.app
        (op X))) :
    IsIso ((presheafToSheaf R AddCommGrpCat.{u}).map γ) := by
  subst h
  let A := sheafAdjunctionContinuous f AddCommGrpCat.{u} P Q
  let A' := sheafAdjunctionContinuous g AddCommGrpCat.{u} Q R
  let AH := sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} P R
  let S := (sheafPullback f AddCommGrpCat.{u} P Q).obj G
  let H := (sheafPullback (f ⋙ g) AddCommGrpCat.{u} P R).obj G
  let raw := g.op.leftKanExtension S.obj
  let eB : B ≅ raw := B.leftKanExtensionUnique β raw (g.op.leftKanExtensionUnit S.obj)
  let δ := ((A.comp A').leftAdjointUniq AH).app G
  let κ := (A'.homEquiv S H).symm α
  have hκ : κ = δ.hom := by
    apply ((A.comp A').homEquiv G H).injective
    have hδ : (A.comp A').homEquiv G H δ.hom = AH.unit.app G :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app (A.comp A') AH G
    rw [hδ]
    change A.homEquiv G _ (A'.homEquiv S H κ) = AH.unit.app G
    rw [Equiv.apply_symm_apply, A.homEquiv_unit]
    ext X x
    exact congrArg (fun k ↦ k x) (Arrow.mk_injective _ _ (hα X.unop))
  have : IsIso κ := by rw [hκ]; infer_instance
  have heB : β ≫ Functor.whiskerLeft g.op eB.hom = g.op.leftKanExtensionUnit S.obj := by
    exact B.descOfIsLeftKanExtension_fac β raw (g.op.leftKanExtensionUnit S.obj)
  have heγ : eB.hom ≫ (g.op.leftKanExtension S.obj).descOfIsLeftKanExtension
      (g.op.leftKanExtensionUnit S.obj) H.obj α.hom = γ := by
    apply B.hom_ext_of_isLeftKanExtension β
    simp only [Functor.whiskerLeft_comp, ← Category.assoc, heB]
    rw [Functor.descOfIsLeftKanExtension_fac]
    exact hγ.symm
  let d := raw.descOfIsLeftKanExtension
    (g.op.leftKanExtensionUnit S.obj) H.obj α.hom
  have hd : (presheafToSheaf R AddCommGrpCat.{u}).map d ≫
      (sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H = κ := by
    apply (A'.homEquiv S H).injective
    rw [Equiv.apply_symm_apply]
    dsimp [A', sheafAdjunctionContinuous]
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
    apply (fullyFaithfulSheafToPresheaf Q AddCommGrpCat.{u}).map_injective
    simp only [Iso.refl_hom, NatTrans.id_app, Functor.id_map]
    rw [Adjunction.comp_unit_app]
    change g.op.leftKanExtensionUnit S.obj ≫
      Functor.whiskerLeft g.op (toSheafify R raw) ≫
        Functor.whiskerLeft g.op (((presheafToSheaf R AddCommGrpCat.{u}).map d ≫
          (sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H).hom) = α.hom
    rw [← Functor.whiskerLeft_comp]
    have ht : toSheafify R raw ≫
        (((presheafToSheaf R AddCommGrpCat.{u}).map d ≫
          (sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H).hom) = d := by
      change toSheafify R raw ≫ sheafifyMap R d ≫
        ((sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H).hom = d
      rw [← toSheafify_naturality_assoc]
      have hh := (sheafificationAdjunction R AddCommGrpCat.{u}).right_triangle_components H
      change toSheafify R H.obj ≫
        ((sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H).hom = 𝟙 _ at hh
      rw [hh, Category.comp_id]
    rw [ht]
    exact raw.descOfIsLeftKanExtension_fac (g.op.leftKanExtensionUnit S.obj) H.obj α.hom
  have : IsIso ((presheafToSheaf R AddCommGrpCat.{u}).map d) := by
    have : IsIso ((presheafToSheaf R AddCommGrpCat.{u}).map d ≫
        (sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H) := by
      rw [hd]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((sheafificationAdjunction R AddCommGrpCat.{u}).counit.app H)
  rw [← heγ, Functor.map_comp]
  infer_instance

private theorem raw_colimit_comparison_iso
    {I C : Type u} [SmallCategory I] [IsConnected I] [SmallCategory C]
    (Q : GrothendieckTopology C)
    (B : I ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})) (T : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (γ : B ⟶ (Functor.const I).obj T)
    [∀ t : I, IsIso ((presheafToSheaf Q AddCommGrpCat.{u}).map (γ.app t))] :
    IsIso ((presheafToSheaf Q AddCommGrpCat.{u}).map
      (colimit.desc B (Cocone.mk T γ))) := by
  let L := presheafToSheaf Q AddCommGrpCat.{u}
  let c := Cocone.mk T γ
  let τ : B ⋙ L ⟶ (Functor.const I).obj (L.obj T) :=
    { app := fun t ↦ L.map (γ.app t)
      naturality := by
        intro t t' b
        change L.map (B.map b) ≫ L.map (γ.app t') = L.map (γ.app t)
        rw [← L.map_comp]
        simp }
  have hτ (t : I) : IsIso (τ.app t) :=
    inferInstanceAs (IsIso (L.map (γ.app t)))
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  have ht : IsColimit (L.mapCocone c) := by
    have hh := (IsColimit.precomposeHomEquiv (asIso τ)
      (constCocone I (L.obj T))).symm (isColimitConstCocone I (L.obj T))
    refine IsColimit.ofIsoColimit hh (Cocone.ext (Iso.refl _) ?_)
    intro t
    simp [τ, c, Cocone.precompose, constCocone]
  let hs := isColimitOfPreserves L (colimit.isColimit B)
  have he : hs.desc (L.mapCocone c) = L.map (colimit.desc B c) := by
    apply hs.hom_ext
    intro t
    rw [hs.fac]
    change L.map (γ.app t) = L.map (colimit.ι B t) ≫ L.map (colimit.desc B c)
    rw [← L.map_comp, colimit.ι_desc]
  have hi : IsIso (hs.desc (L.mapCocone c)) :=
    hs.nonempty_isColimit_iff_isIso_desc.mp ⟨ht⟩
  rw [he] at hi
  exact hi

/-- Source: Stacks Project, Sites, Tag 0A35, presentation construction and
adjunction identification; abelian groups as in Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-finite-section-eventual-zero).

Proof: For each limit object Y, consider presentations (t,W,p), where t is in Under i,
W belongs to F(t.right), and p identifies V(t.right)(W) with Y. Move two presentations
to a common stage and use eventual object equality to refine their representatives
until equal. Equalize parallel refinements using filteredness. Thus the presentation
category is filtered. Evaluate the unit-characterized adjunct stage maps at W;
adjunction uniqueness gives their identity and composition laws. Take their filtered
colimit in abelian groups. Lift restriction arrows by harrows and correct endpoints
using hobjects; eventual arrow equality makes the restriction independent of the
lift. Lifting finite arrow diagrams proves the presheaf laws. By hQ, every cover is
an image of a stage cover, and by hfinite it has finitely many arrows. Lift its
matching data and the finitely many compatibility equations to a common stage.
The preserved covering pullbacks identify the stage matching diagram. Filtered
abelian colimits commute with its finite products and equalizer, so the presheaf
is a sheaf; the empty matching diagram gives the zero group.

A morphism from this sheaf to T is a compatible family of maps on presentation
section groups. Identity refinements give stage sheaf maps, and the stage
adjunctions identify their compatible family with a map G to the restriction of T
along V i. The reverse assignment takes the adjunct at every stage. Adjunction
identities and colimit hom_ext show that the assignments are inverse and natural.
Uniqueness of left adjoints identifies the constructed sheaf with the canonical
inverse image, preserving its unit. At V i U, presentations carrying U forward
are final: lift any presentation to a common stage, enforce eventual object
equality, and equalize the refinement arrows. These constructions use only
object/arrow colimits, finite covers, and adjunctions; they do not use the parent
comparison-bijectivity theorem or any of its downstream zero-detection results.

Suppose (K.ι.app t).hom x is zero. By hK its representative (E t).hom x
maps to zero in the canonical inverse-image sections. Under the constructed
sheaf identification, compare this representative with zero. Equality in a
filtered colimit holds at a common refinement. Equalize the two refinement
arrows if necessary; additivity sends the zero representative to zero. Finality
of the carried-U presentations moves this refinement into Under i. The unit
equations hα and hθ identify its maps with α and θ by adjunct uniqueness.
The equation hD identifies its transported stage value with (E t').hom
((D.map b).hom x). Injectivity and additivity of E t' imply (D.map b).hom x = 0.

Edge cases: a zero section is killed by the identity refinement; zero section
groups satisfy the assertion by map_zero. In a constant identity diagram the
hypothesis already says x = 0. This asserts only eventual vanishing of a single
stage section, not surjectivity or bijectivity of a comparison.
-/
theorem colimit_site_finite_section_eventual_zero
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (U : F.obj i)
    (D : Under i ⥤ AddCommGrpCat.{u})
    (E : ∀ t : Under i, D.obj t ≅
      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G).obj.obj (op ((F.map t.hom).toFunctor.obj U)))
    (K : Cocone D) (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
      i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op ((V.ι.app i).toFunctor.obj U)))
    (hK : ∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj U))))
    (hD : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫ (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) :
    ∀ (t : Under i) (x : D.obj t), (K.ι.app t).hom x = 0 →
      ∃ (t' : Under i) (b : t ⟶ t'), (D.map b).hom x = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  classical
  obtain ⟨B, β, γ, hβ, hβmap, hγ⟩ := colimit_site_raw_abelian_section_diagram
    J F P V Q i G α hα θ hθ
  have hB := colimit_site_raw_abelian_section_isSheaf J F P hfinite hcover hpullback
    V hobjects harrows Q hQ hVpullback i G θ hθ B β hβ hβmap
  let H := (sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let φ : colimit B ⟶ H.obj := colimit.desc B (Cocone.mk H.obj γ)
  have hγiso (t : Under i) :
      IsIso ((presheafToSheaf Q.toGrothendieck AddCommGrpCat.{u}).map (γ.app t)) := by
    have : (B.obj t).IsLeftKanExtension (β t) := hβ t
    apply raw_comparison_iso (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor
      (V.ι.app i).toFunctor (P i).toGrothendieck (P t.right).toGrothendieck
      Q.toGrothendieck (congrArg Cat.Hom.toFunctor (V.w t.hom)) G
      (B.obj t) (β t) (γ.app t) (α t)
    · ext X x
      exact congrArg (fun k ↦ k x) (hγ t X.unop)
    · exact hα t
  have : IsConnected (Under i) := IsFiltered.isConnected (Under i)
  have : IsIso ((presheafToSheaf Q.toGrothendieck AddCommGrpCat.{u}).map φ) :=
    raw_colimit_comparison_iso Q.toGrothendieck B H.obj γ
  have : IsIso (sheafifyMap Q.toGrothendieck φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf Q.toGrothendieck AddCommGrpCat.{u}).map
      ((presheafToSheaf Q.toGrothendieck AddCommGrpCat.{u}).map φ)))
  have : IsIso (toSheafify Q.toGrothendieck (colimit B)) :=
    isIso_toSheafify Q.toGrothendieck hB
  have : IsIso (toSheafify Q.toGrothendieck H.obj) :=
    isIso_toSheafify Q.toGrothendieck H.property
  have : IsIso (φ ≫ toSheafify Q.toGrothendieck H.obj) := by
    rw [toSheafify_naturality]
    infer_instance
  have : IsIso φ :=
    IsIso.of_isIso_comp_right φ (toSheafify Q.toGrothendieck H.obj)
  obtain ⟨R, q, ⟨hR⟩, hRq⟩ := colimit_site_raw_abelian_section_evaluation
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap U D E H.obj γ
    (fun t ↦ (α t).hom) hγ hD
  intro t x hx
  have heq : K.ι.app t ≫ e.hom =
      R.ι.app t ≫ q.hom ≫ φ.app (op ((V.ι.app i).toFunctor.obj U)) :=
    Arrow.mk_injective _ _ ((hK t).trans (hRq t).symm)
  have hz : (R.ι.app t ≫ q.hom ≫
      φ.app (op ((V.ι.app i).toFunctor.obj U))) x = 0 := by
    rw [← heq]
    change e.hom (K.ι.app t x) = 0
    rw [hx]
    exact map_zero e.hom.hom
  have hRx : R.ι.app t x = R.ι.app t 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (q.hom ≫ φ.app (op ((V.ι.app i).toFunctor.obj U)))).1
    rw [map_zero (R.ι.app t).hom, map_zero]
    exact hz
  let hRf := isColimitOfPreserves (forget AddCommGrpCat.{u}) hR
  obtain ⟨t', b, hb⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hRf x (0 : D.obj t)).mp hRx
  exact ⟨t', b, by simpa using hb⟩


end CategoryTheory
