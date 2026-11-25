/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-! # The sectionwise image of extension by zero

Source: Stacks Project, Tag 0F4Y
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

private theorem properSupport_openRestriction_isIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((openImmersionRestriction (ModuleCat.{u + 1} Λ) f).map
      ((properSupportLowerStarInclusion Λ f).app F)) := by
  let A := ModuleCat.{u + 1} Λ
  let ψ := (openImmersionRestriction A f).map ((properSupportLowerStarInclusion Λ f).app F)
  have hc (V : X.Etaleᵒᵖ) : IsIso (ψ.hom.app V) := by
    let B := (MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj V.unop
    have hpb : IsIso (pullback.fst B.hom f) := by
      let adj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance trivial
      have : IsIso (adj.unit.app V.unop) := inferInstance
      have : IsIso (adj.unit.app V.unop).left :=
        inferInstanceAs (IsIso ((MorphismProperty.Over.forget @Etale ⊤ X ⋙
          CategoryTheory.Over.forget X).map (adj.unit.app V.unop)))
      have he : (adj.unit.app V.unop).left ≫ pullback.fst B.hom f = 𝟙 _ := by
        simp [adj, MorphismProperty.Over.mapPullbackAdj, B]
      exact IsIso.of_isIso_fac_left he
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective
      (((properSupportLowerStarInclusion Λ f).app F).hom.app (op B))
    refine ⟨(properSupportLowerStarInclusion_range Λ f F B).1, ?_⟩
    intro s
    apply (properSupportLowerStarInclusion_range Λ f F B).2 s |>.2
    obtain ⟨T, _, hT⟩ := etaleModuleSection_closedSupport Λ F (f.Etale.obj B) s
    refine ⟨T, hT, ?_⟩
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
      pullback.fst B.hom f)
    infer_instance
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology A).map ψ) := by
    change IsIso ψ.hom
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso ψ (sheafToPresheaf X.smallEtaleTopology A)

private theorem properSupport_stalk_outside_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (hy : y default ∉ Set.range f) :
    IsZero ((Scheme.pointSmallEtale y).sheafFiber.obj
      ((properSupportLowerStar Λ f).obj F)) := by
  classical
  let G := (properSupportLowerStar Λ f).obj F
  let Φ := Scheme.pointSmallEtale y
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hz (z : (Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) : z = 0 := by
    obtain ⟨V, v, s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) z
    obtain ⟨v, hv, rfl⟩ := Over.homMk_surjective v
    change Spec (.of Ω) ⟶ V.left at v
    change v ≫ V.hom = y at hv
    obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ F (f.Etale.obj V)
      (pullback.fst V.hom f) s.val).1 s.property
    have : LocallyOfFiniteType (𝟙 V.left) := MorphismProperty.id_mem _ _
    have : IsSeparated (𝟙 V.left) := MorphismProperty.id_mem _ _
    obtain ⟨I, hI, _⟩ :=
      (Scheme.closed_subset_proper_over_base_properties (pullback.fst V.hom f) T).2.2.2
        (pullback.fst V.hom f) (𝟙 V.left) (by simp) hp
    change TopologicalSpace.Closeds V.left at I
    have hnv : v default ∉ I := by
      intro hm
      change v default ∈ (I : Set V.left) at hm
      rw [hI] at hm
      obtain ⟨x, _, hx⟩ := hm
      apply hy
      refine ⟨pullback.snd V.hom f x, ?_⟩
      have hpb := congrArg (fun k => k x) (pullback.condition (f := V.hom) (g := f))
      change V.hom (pullback.fst V.hom f x) = f (pullback.snd V.hom f x) at hpb
      exact hpb.symm.trans ((congrArg V.hom hx).trans
        (congrArg (fun k => k default) hv))
    let O : V.left.Opens := ⟨(I : Set V.left)ᶜ, I.isClosed.isOpen_compl⟩
    let W : Y.Etale := Scheme.Etale.mk (O.ι ≫ V.hom)
    let h : W ⟶ V := MorphismProperty.Over.homMk O.ι (by simp [W]) trivial
    have hvr : Set.range v ⊆ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      have hq : q = default := Subsingleton.elim _ _
      change v q ∉ I
      simpa only [hq] using hnv
    let w := IsOpenImmersion.lift O.ι v hvr
    have hs0 : G.obj.map h.op s = 0 := by
      apply Subtype.ext
      change F.obj.map (f.Etale.map h).op s.val = 0
      apply module_section_zero_of_germs Λ F (f.Etale.obj W)
      intro K _ _ k
      by_contra hn
      have hnk := (not_congr
        (etaleModuleGerm_restrict_zero Λ F (f.Etale.map h) s.val K k)).1 hn
      have hkT := (hT K (k ≫ (f.Etale.map h).left)).2 hnk
      rw [Scheme.Hom.comp_apply] at hkT
      have hkI : pullback.fst V.hom f ((f.Etale.map h).left (k default)) ∈ I := by
        change _ ∈ (I : Set V.left)
        rw [hI]
        exact ⟨(f.Etale.map h).left (k default), hkT, rfl⟩
      have he : (f.Etale.map h).left ≫ pullback.fst V.hom f =
          pullback.fst W.hom f ≫ h.left := by
        simp [Scheme.Hom.Etale, MorphismProperty.Over.pullback_map_left]
      have he' := congrArg (fun a => a (k default)) he
      change pullback.fst V.hom f ((f.Etale.map h).left (k default)) =
        h.left (pullback.fst W.hom f (k default)) at he'
      have hO : h.left (pullback.fst W.hom f (k default)) ∉ I := by
        exact (pullback.fst W.hom f (k default)).property
      exact hO (he' ▸ hkI)
    let w' : Φ.fiber.obj W := Over.homMk w (by
      change w ≫ O.ι ≫ V.hom = y
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact hv)
    have hw : Φ.fiber.map h w' = Over.homMk v hv := by
      apply Over.OverMorphism.ext
      exact IsOpenImmersion.lift_fac O.ι v hvr
    have eg := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w h w' G.obj) s
    change Φ.toPresheafFiber W w' G.obj (G.obj.map h.op s) =
      Φ.toPresheafFiber V (Φ.fiber.map h w') G.obj s at eg
    rw [hs0, map_zero, hw] at eg
    exact eg.symm
  have : Subsingleton ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The canonical extension-by-zero comparison has image exactly the sections whose
support is proper over the target.

Source: Stacks Project, Tag 0F4Y, specialized to open immersions.
(auxiliary; not a blueprint node)

Proof:
On an etale object factoring through the open, its fibre-product projection to that
object is an isomorphism. Every closed section support is therefore proper there,
so restriction of the literal support inclusion to the open is an isomorphism.
Compose that restriction with the counit of restriction/pushforward and invert it.
The extension-by-zero adjunction then constructs q from the extension to the support
sheaf. Counit naturality identifies q followed by the inclusion with the canonical
extension-by-zero comparison.
At a geometric point outside the open, represent a support-sheaf germ by a section.
Its proper support has closed image in the etale neighbourhood, missing the marked
point. Restrict to the complementary open: every geometric germ of the restricted
section is zero, hence the section itself is zero by the zero-open theorem. The
original support-sheaf germ is zero as well. Thus both q's source and target have zero
stalks outside the open; inside it, restriction makes q invertible. Geometric stalk
detection proves q is an isomorphism. Composing its bijective component on sections
with the literal subtype inclusion proves injectivity and the stated image equality. -/
theorem openExtensionProperSupport_range (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) :
    Function.Injective
      (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) f).app F).hom.app (op V)) ∧
    ∀ s, (∃ t,
      (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) f).app F).hom.app
        (op V)) t = s) ↔
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let G := (properSupportLowerStar Λ f).obj F
  let i := (properSupportLowerStarInclusion Λ f).app F
  let R := openImmersionRestriction A f
  let L := openImmersionLowerShriek A f
  let adj := openImmersionLowerShriekAdjunction A f
  let adj' := openImmersionRestrictionLowerStarAdjunction A f
  have : IsIso (R.map i) := properSupport_openRestriction_isIso Λ f F
  let t := R.map i ≫ adj'.counit.app F
  have : IsIso t := inferInstance
  let q : L.obj F ⟶ G := L.map (inv t) ≫ adj.counit.app G
  have hqi : q ≫ i = (openImmersionLowerShriekToLowerStar A f).app F := by
    rw [openImmersionLowerShriekToLowerStar_app]
    dsimp only [q]
    have hn : L.map (R.map i) ≫ adj.counit.app ((lowerStar A f).obj F) =
        adj.counit.app G ≫ i := adj.counit.naturality i
    rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
    have ht : inv t ≫ R.map i = inv (adj'.counit.app F) := by
      dsimp only [t]
      rw [IsIso.inv_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [ht]
    simp only [NatIso.isIso_inv_app]
    rfl
  have hRq : IsIso (R.map q) := by
    dsimp only [q]
    rw [Functor.map_comp]
    infer_instance
  have hUq : IsIso ((upperStar A f).map q) :=
    (NatIso.isIso_map_iff (upperStarIsoOpenImmersionRestriction A f) q).2 hRq
  have hq : IsIso q := by
    apply Scheme.isIso_of_isIso_sheafFiber_map
    intro x
    let y := Y.algClosurePoint x
    have hpoint : y.base (IsLocalRing.closedPoint _) = y default :=
      congrArg y (Subsingleton.elim _ _)
    by_cases hy : y default ∈ Set.range f
    · have hh := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map A f q hUq
        (IsOpenImmersion.lift f y
          (Scheme.range_base_subset_of_closedPoint_mem y (hpoint.symm ▸ hy)))
      rw [IsOpenImmersion.lift_fac] at hh
      exact hh
    · have hzG := properSupport_stalk_outside_zero Λ f F _ y hy
      have hzG' : IsZero (((Scheme.pointSmallEtale y).ulift.{u + 1}).sheafFiber.obj G) :=
        hzG.of_iso (((Scheme.pointSmallEtale y).uliftSheafFiberIso A).app G)
      have hzL := isZero_uliftSheafFiber_openImmersionLowerShriek_obj A f y (hpoint.symm ▸ hy) F
      exact ⟨⟨hzG'.to_ _, hzL.eq_of_src _ _, hzG'.eq_of_src _ _⟩⟩
  have hqbij : Function.Bijective (q.hom.app (op V)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  constructor
  · rw [← hqi]
    change Function.Injective (fun t => i.hom.app (op V) (q.hom.app (op V) t))
    exact (properSupportLowerStarInclusion_range Λ f F V).1.comp hqbij.1
  · intro s
    rw [← hqi]
    change (∃ t, i.hom.app (op V) (q.hom.app (op V) t) = s) ↔ _
    rw [← (properSupportLowerStarInclusion_range Λ f F V).2 s]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨q.hom.app (op V) t, ht⟩
    · rintro ⟨t, ht⟩
      obtain ⟨r, rfl⟩ := hqbij.2 t
      exact ⟨r, ht⟩

end AlgebraicGeometry.Etale
