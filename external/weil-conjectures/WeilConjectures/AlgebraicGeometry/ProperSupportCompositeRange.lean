/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality

/-! # The image of the composite proper-support inclusion

Source: Stacks Project, Tag 0F50
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

private theorem proper_comp_support_iff {T U S : Scheme.{u}}
    (p : T ⟶ U) (q : U ⟶ S) [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    [IsSeparated q] (C : TopologicalSpace.Closeds T) (I : TopologicalSpace.Closeds U)
    (hI : (I : Set U) = p '' (C : Set T)) :
    Scheme.IsClosedSubsetProperOver (p ≫ q) C ↔
      Scheme.IsClosedSubsetProperOver p C ∧ Scheme.IsClosedSubsetProperOver q I := by
  let Z := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let j : Z ⟶ T := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hj : Set.range j = (C : Set T) := by
    dsimp only [j]
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  constructor
  · intro hp
    have : IsProper ((j ≫ p) ≫ q) := by
      change IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ p ≫ q) at hp
      simpa only [Category.assoc] using hp
    have h1 : Scheme.IsClosedSubsetProperOver p C := IsProper.of_comp (j ≫ p) q
    obtain ⟨I', hI', h2⟩ :=
      (Scheme.closed_subset_proper_over_base_properties (p ≫ q) C).2.2.2 p q rfl hp
    have he : I' = I := TopologicalSpace.Closeds.ext (hI'.trans hI.symm)
    exact ⟨h1, he ▸ h2⟩
  · rintro ⟨h1, h2⟩
    have : IsProper (j ≫ p) := h1
    let a := j ≫ p ≫ q
    have h3 := (Scheme.isClosedSubsetProperOver_union_preimage a).2
      (j ≫ p) q (by simp only [a, Category.assoc]) I h2
    have htop : I.preimage (j ≫ p).continuous = ⊤ := by
      apply TopologicalSpace.Closeds.ext
      ext z
      change (j ≫ p) z ∈ I ↔ True
      constructor
      · exact fun _ => trivial
      · intro _
        change p (j z) ∈ (I : Set U)
        rw [hI]
        exact ⟨j z, hj ▸ Set.mem_range_self z, rfl⟩
    rw [htop] at h3
    have h4 := (Scheme.closed_subset_proper_over_base_properties a ⊤).2.1.mp h3
      Z (𝟙 Z) (by ext z; simp)
    change IsProper a
    simpa only [Category.id_comp] using h4

private theorem section_support_iso_iff
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V W : X.Etale}
    (e : V ≅ W) (p : V.left ⟶ S) (q : W.left ⟶ S)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsSeparated p] [IsSeparated q]
    (he : e.hom.left ≫ q = p) (s : F.obj.obj (op W)) :
    SectionHasProperSupport Λ F V p (F.obj.map e.hom.op s) ↔
      SectionHasProperSupport Λ F W q s := by
  have forward {V W : X.Etale} (e : V ≅ W) (p : V.left ⟶ S) (q : W.left ⟶ S)
      [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsSeparated q]
      (he : e.hom.left ≫ q = p) (s : F.obj.obj (op W))
      (hs : SectionHasProperSupport Λ F V p (F.obj.map e.hom.op s)) :
      SectionHasProperSupport Λ F W q s := by
    obtain ⟨C, hC, hp⟩ := (sectionHasProperSupport_iff Λ F V p _).1 hs
    let ee : V.left ≅ W.left :=
      (MorphismProperty.Over.forget @Etale ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e
    apply (sectionHasProperSupport_iff Λ F W q s).2
    refine ⟨C.preimage ee.inv.continuous, ?_, proper_iso_image p q ee he C hp⟩
    intro Ω _ _ v
    have hg := not_congr (etaleModuleGerm_restrict_zero Λ F e.hom s Ω (v ≫ ee.inv))
    have hv : (v ≫ ee.inv) ≫ e.hom.left = v := by
      change (v ≫ ee.inv) ≫ ee.hom = v
      simp
    have hc := hC Ω (v ≫ ee.inv)
    rw [Scheme.Hom.comp_apply] at hc
    change ee.inv (v default) ∈ C ↔ _
    apply hc.trans
    apply hg.trans
    exact iff_of_eq (congrArg (fun w : Spec (.of Ω) ⟶ W.left =>
      (Scheme.pointSmallEtale (w ≫ W.hom)).toPresheafFiber W (Over.homMk w) F.obj s ≠ 0) hv)
  constructor
  · exact forward e p q he s
  · intro hs
    have he' : e.inv.left ≫ p = q := by
      rw [← he]
      have hi : e.inv.left ≫ e.hom.left = 𝟙 _ := by
        exact congrArg (fun h => h.left) e.inv_hom_id
      rw [← Category.assoc, hi, Category.id_comp]
    have h := forward e.symm q p he' (F.obj.map e.hom.op s) ?_
    · exact h
    · have hmap : F.obj.map e.inv.op (F.obj.map e.hom.op s) = s := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        simp
      change SectionHasProperSupport Λ F W q
        (F.obj.map e.inv.op (F.obj.map e.hom.op s))
      rwa [hmap]

private theorem support_property_iff
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] (s : F.obj.obj (op V))
    (C : TopologicalSpace.Closeds V.left)
    (hC : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left),
      v default ∈ C ↔ (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
        (Over.homMk v) F.obj s ≠ 0) :
    SectionHasProperSupport Λ F V p s ↔ Scheme.IsClosedSubsetProperOver p C := by
  rw [sectionHasProperSupport_iff]
  constructor
  · rintro ⟨D, hD, hp⟩
    have he : D = C := by
      apply TopologicalSpace.Closeds.ext
      ext x
      change x ∈ D ↔ x ∈ C
      let Ω := AlgebraicClosure (V.left.residueField x)
      let v : Spec (.of Ω) ⟶ V.left := V.left.algClosurePoint x
      have hv : v default = x := Scheme.algClosurePoint_base _ _ _
      simpa only [hv] using (hD Ω v).trans (hC Ω v).symm
    rwa [he] at hp
  · exact fun hp => ⟨C, hC, hp⟩

private theorem iterated_support_iff
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Z.Etale)
    (s : ((properSupportLowerStar Λ f).obj F).obj.obj (op (g.Etale.obj V))) :
    SectionHasProperSupport Λ ((properSupportLowerStar Λ f).obj F) (g.Etale.obj V)
        (pullback.fst V.hom g) s ↔
      SectionHasProperSupport Λ F (f.Etale.obj (g.Etale.obj V))
        (pullback.fst (g.Etale.obj V).hom f ≫ pullback.fst V.hom g) s.val := by
  obtain ⟨T, I, hT, hp, hI, hIg⟩ := properSupportSectionImage Λ f F (g.Etale.obj V) s
  rw [support_property_iff Λ _ _ _ s I hIg,
    support_property_iff Λ _ _ _ s.val T hT]
  exact ⟨fun h => (proper_comp_support_iff _ _ T I hI).2 ⟨hp, h⟩,
    fun h => ((proper_comp_support_iff _ _ T I hI).1 h).2⟩

/-- The composite support inclusion has exactly the properly supported sections as image.

Source: Stacks Project, Tag 0F50.
(auxiliary; not a blueprint node)

Proof:
Let T be the support of an underlying section on X_W. If it is proper over Y_W,
its image I in Y_W is closed. The section of f_! F has support exactly I: off I its
restriction is zero; conversely, a zero germ gives a Zariski zero neighbourhood, whose
inverse image misses T. Thus a point of I cannot have zero germ.
If T is proper over W, it is proper over the separated Y_W by proper-over-separated.
The closed proper-image lemma makes I proper over W. This gives both successive
proper-support conditions. Conversely those two conditions say that T is proper over
Y_W and I is proper over W. The proper-preimage lemma applied to T_red -> Y_W and I
makes the whole T_red proper over W. The ordinary direct-image compositor identifies
these underlying sections and commutes with restriction. -/
theorem properSupportComposite_range (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Z.Etale)
    (s : F.obj.obj (op ((f ≫ g).Etale.obj V))) :
    (∃ t, (((properSupportLowerStarInclusion Λ g).app
          ((properSupportLowerStar Λ f).obj F) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((properSupportLowerStarInclusion Λ f).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F).hom.app (op V)) t = s) ↔
      SectionHasProperSupport Λ F ((f ≫ g).Etale.obj V) (pullback.fst V.hom (f ≫ g)) s  := by
  classical
  let W := g.Etale.obj V
  let B := f.Etale.obj W
  let C := (f ≫ g).Etale.obj V
  let e : C ≅ B := (MorphismProperty.Over.pullbackComp f g).app V
  let p := pullback.fst W.hom f
  let q := pullback.fst V.hom g
  let r := pullback.fst V.hom (f ≫ g)
  have he : e.hom.left ≫ (p ≫ q) = r :=
    MorphismProperty.Over.pullbackComp_left_fst_fst f g V
  have hc (s₀ : F.obj.obj (op B)) :=
    section_support_iso_iff Λ F e r (p ≫ q) he s₀
  have hmap (t : ((properSupportLowerStar Λ g).obj
      ((properSupportLowerStar Λ f).obj F)).obj.obj (op V)) :
      (((properSupportLowerStarInclusion Λ g).app
          ((properSupportLowerStar Λ f).obj F) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((properSupportLowerStarInclusion Λ f).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F).hom.app (op V)) t =
      F.obj.map e.hom.op t.val.val := by
    change (((lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F).hom.app (op V))
      t.val.val = _
    rw [lowerStarComp_hom_app_hom_app]
    rfl
  constructor
  · rintro ⟨t, ht⟩
    rw [hmap] at ht
    rw [← ht]
    exact (hc t.val.val).2 ((iterated_support_iff Λ f g F V t.val).1 t.property)
  · intro hs
    let s₀ := F.obj.map e.inv.op s
    have hback : F.obj.map e.hom.op s₀ = s := by
      dsimp only [s₀]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      simp
    have hpq : SectionHasProperSupport Λ F B (p ≫ q) s₀ :=
      (hc s₀).1 (hback.symm ▸ hs)
    obtain ⟨T, hT, hpT⟩ := (sectionHasProperSupport_iff Λ F B (p ≫ q) s₀).1 hpq
    have hp : SectionHasProperSupport Λ F B p s₀ := by
      refine (sectionHasProperSupport_iff Λ F B p s₀).2 ⟨T, hT, ?_⟩
      have : IsProper (((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p) ≫ q) := by
        simpa only [Category.assoc] using hpT
      exact IsProper.of_comp _ q
    let t₀ : ((properSupportLowerStar Λ f).obj F).obj.obj (op W) := ⟨s₀, hp⟩
    let t : ((properSupportLowerStar Λ g).obj
        ((properSupportLowerStar Λ f).obj F)).obj.obj (op V) :=
      ⟨t₀, (iterated_support_iff Λ f g F V t₀).2 hpq⟩
    exact ⟨t, (hmap t).trans hback⟩

end AlgebraicGeometry.Etale
