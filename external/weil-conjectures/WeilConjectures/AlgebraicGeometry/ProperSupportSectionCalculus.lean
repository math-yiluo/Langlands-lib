/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality

/-! # Local and linear calculus of proper-support sections

Source: Stacks Project, Tags 04FR, 04FT and 0F4X
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem support_of_germ_zero_imp
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p]
    (s : F.obj.obj (op V)) (t : G.obj.obj (op V))
    (hs : SectionHasProperSupport Λ F V p s)
    (hz : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left),
      (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.obj s = 0 →
      (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) G.obj t = 0) :
    SectionHasProperSupport Λ G V p t := by
  classical
  obtain ⟨Ts, hTs, hp⟩ := hs
  obtain ⟨Tt, _, hTt⟩ := etaleModuleSection_closedSupport Λ G V t
  refine ⟨Tt, hTt, (Scheme.closed_subset_proper_over_base_properties p Ts).2.2.1
    Tt ?_ hp⟩
  change (Tt : Set V.left) ⊆ Ts
  intro x hx
  obtain ⟨Ω, _, _, v, rfl, hg⟩ := hTt ▸ hx
  by_contra hn
  have hs0 : (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
      (Over.homMk v) F.obj s = 0 := by
    by_contra h
    exact hn (hTs.symm ▸ ⟨Ω, inferInstance, inferInstance, v, rfl, h⟩)
  exact hg (hz Ω v hs0)

private theorem support_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] :
    SectionHasProperSupport Λ F V p 0 := by
  refine ⟨⊥, ?_, ?_⟩
  · ext x
    simp only [TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false,
      Set.mem_ofPred_eq, map_zero, ne_self_iff_false, and_false, exists_false]
  · have h := (Scheme.isClosedSubsetProperOver_union_preimage p).1 0 (fun _ => ⊥)
      (fun i => Fin.elim0 i)
    simpa only [iSup_of_empty] using h

private theorem support_smul
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] (r : Λ) (s : F.obj.obj (op V))
    (hs : SectionHasProperSupport Λ F V p s) :
    SectionHasProperSupport Λ F V p (r • s) := by
  apply support_of_germ_zero_imp Λ F F V p s (r • s) hs
  intro Ω _ _ v hz
  rw [map_smul, hz, smul_zero]

private theorem support_map
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (φ : F ⟶ G) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] (s : F.obj.obj (op V))
    (hs : SectionHasProperSupport Λ F V p s) :
    SectionHasProperSupport Λ G V p (φ.hom.app (op V) s) := by
  apply support_of_germ_zero_imp Λ F G V p s _ hs
  intro Ω _ _ v hz
  have h := (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber_naturality_apply
    φ.hom V (Over.homMk v) s
  rw [hz, map_zero] at h
  exact h.symm

private theorem support_add
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] (s t : F.obj.obj (op V))
    (hs : SectionHasProperSupport Λ F V p s) (ht : SectionHasProperSupport Λ F V p t) :
    SectionHasProperSupport Λ F V p (s + t) := by
  classical
  obtain ⟨Ts, hTs, hps⟩ := hs
  obtain ⟨Tt, hTt, hpt⟩ := ht
  obtain ⟨T, _, hT⟩ := etaleModuleSection_closedSupport Λ F V (s + t)
  have hu : Scheme.IsClosedSubsetProperOver p (Ts ⊔ Tt) := by
    let C : Fin 2 → TopologicalSpace.Closeds V.left := fun i => if i = 0 then Ts else Tt
    have hC : ∀ i, Scheme.IsClosedSubsetProperOver p (C i) := by
      intro i
      by_cases hi : i = 0 <;> simp only [C, hi, ite_true, ite_false] <;> assumption
    have h := (Scheme.isClosedSubsetProperOver_union_preimage p).1 2 C hC
    have he : (⨆ i, C i) = Ts ⊔ Tt := by
      apply le_antisymm
      · apply iSup_le
        intro i
        by_cases hi : i = 0 <;> simp only [C, hi, ite_true, ite_false]
        · exact le_sup_left
        · exact le_sup_right
      · apply sup_le
        · exact le_iSup_of_le (0 : Fin 2) (by simp [C])
        · exact le_iSup_of_le (1 : Fin 2) (by simp [C])
    rwa [he] at h
  refine ⟨T, hT, (Scheme.closed_subset_proper_over_base_properties p (Ts ⊔ Tt)).2.2.1
    T ?_ hu⟩
  change (T : Set V.left) ⊆ (Ts : Set V.left) ∪ Tt
  intro x hx
  obtain ⟨Ω, _, _, v, rfl, hg⟩ := hT ▸ hx
  by_contra hn
  have hs0 : (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
      (Over.homMk v) F.obj s = 0 := by
    by_contra h
    exact hn (Or.inl (hTs.symm ▸ ⟨Ω, inferInstance, inferInstance, v, rfl, h⟩))
  have ht0 : (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
      (Over.homMk v) F.obj t = 0 := by
    by_contra h
    exact hn (Or.inr (hTt.symm ▸ ⟨Ω, inferInstance, inferInstance, v, rfl, h⟩))
  exact hg (by rw [map_add, hs0, ht0, zero_add])

/-- Proper-support sections are closed under the module operations, restriction and
sheaf morphisms, and membership is local on the base. Their support can equivalently
be tested at every separably closed geometric point.

Source: Stacks Project, Tags 04FR, 04FT and 0F4X.
(auxiliary; not a blueprint node)

Proof:
1. Apply the zero-open theorem to the underlying abelian sheaf. Its open zero locus
has closed complement T, and the geometric-germ criterion identifies T at every
separably closed geometric point. Every scheme point has an algebraically closed
geometric point above it, so this also identifies the support in SectionHasProperSupport.
2. The zero section has empty support. A sum has support contained in the union of
its summands' supports, and a scalar multiple has support contained in the original
support. Closed subsets and finite unions preserve properness over the base.
3. A restriction is pullback along the base-change map of etale objects. The germ
formula identifies its support with the inverse image of the original support.
Closed proper-support locality gives properness after this base change.
4. A covering sieve contains a jointly surjective etale family. Apply the same support
formula to this family and descend properness by closed proper-support locality.
5. A linear sheaf morphism carries zero germs to zero, so its section has closed support
contained in the original support. Properness passes to that closed subset. -/
theorem properSupportSectionCalculus (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] :
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale),
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) 0 ∧
      (∀ s t, SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s →
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) t →
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) (s + t)) ∧
      (∀ (r : Λ) s,
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s →
        SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) (r • s))) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (V W : Y.Etale) (h : W ⟶ V) s,
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s →
      SectionHasProperSupport Λ F (f.Etale.obj W) (pullback.fst W.hom f)
        (F.obj.map (f.Etale.map h).op s)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (V : Y.Etale) s (S : Sieve V), S ∈ Y.smallEtaleTopology V →
      (∀ (W : Y.Etale) (h : W ⟶ V), S h →
        SectionHasProperSupport Λ F (f.Etale.obj W) (pullback.fst W.hom f)
          (F.obj.map (f.Etale.map h).op s)) →
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (φ : F ⟶ G) (V : Y.Etale) s,
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s →
      SectionHasProperSupport Λ G (f.Etale.obj V) (pullback.fst V.hom f)
        (φ.hom.app (op (f.Etale.obj V)) s)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) s,
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s ↔
        ∃ T : TopologicalSpace.Closeds (f.Etale.obj V).left,
          (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
            (v : Spec (.of Ω) ⟶ (f.Etale.obj V).left),
            v default ∈ T ↔
              (Scheme.pointSmallEtale (v ≫ (f.Etale.obj V).hom)).toPresheafFiber
                (f.Etale.obj V) (Over.homMk v) F.obj s ≠ 0) ∧
          IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
            pullback.fst V.hom f)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) s,
      ∃ T : TopologicalSpace.Closeds (f.Etale.obj V).left,
        (T : Set (f.Etale.obj V).left) =
          {x | ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
            (v : Spec (.of Ω) ⟶ (f.Etale.obj V).left), v default = x ∧
              (Scheme.pointSmallEtale (v ≫ (f.Etale.obj V).hom)).toPresheafFiber
                (f.Etale.obj V) (Over.homMk v) F.obj s ≠ 0}) := by
  refine ⟨?_, (properSupportSectionLocality Λ f).1,
    (properSupportSectionLocality Λ f).2, ?_, ?_, ?_⟩
  · intro F V
    exact ⟨support_zero Λ F (f.Etale.obj V) (pullback.fst V.hom f),
      support_add Λ F (f.Etale.obj V) (pullback.fst V.hom f),
      support_smul Λ F (f.Etale.obj V) (pullback.fst V.hom f)⟩
  · intro F G φ V s hs
    exact support_map Λ F G φ (f.Etale.obj V) (pullback.fst V.hom f) s hs
  · intro F V s
    exact sectionHasProperSupport_iff Λ F (f.Etale.obj V) (pullback.fst V.hom f) s
  · intro F V s
    obtain ⟨T, _, hT⟩ := etaleModuleSection_closedSupport Λ F (f.Etale.obj V) s
    exact ⟨T, hT⟩

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
  (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]

/-- The actual submodule of sections whose support is proper over the base. -/
def properSupportSections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) :
    Submodule Λ (F.obj.obj (op (f.Etale.obj V))) where
  carrier := {s | SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s}
  zero_mem' := (properSupportSectionCalculus Λ f).1 F V |>.1
  add_mem' := fun {s t} => (properSupportSectionCalculus Λ f).1 F V |>.2.1 s t
  smul_mem' := (properSupportSectionCalculus Λ f).1 F V |>.2.2

/-- The presheaf of actual proper-support sections, before proving its sheaf condition. -/
noncomputable def properSupportPresheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj V := ModuleCat.of Λ (properSupportSections Λ f F V.unop)
  map {V W} h := ModuleCat.ofHom
    { toFun := fun s => ⟨F.obj.map (f.Etale.map h.unop).op s.1,
        (properSupportSectionCalculus Λ f).2.1 F V.unop W.unop h.unop s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (map_add _ _ _)
      map_smul' := fun r s => Subtype.ext (map_smul _ _ _) }
  map_id V := by ext s; simp
  map_comp h k := by ext s; simp

/-- Forgetting the module operations gives this literal subfunctor of the direct image. -/
def properSupportSubfunctor
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Subfunctor (((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ⋙
      forget (ModuleCat.{u + 1} Λ)) where
  obj V := {s | SectionHasProperSupport Λ F (f.Etale.obj V.unop)
    (pullback.fst V.unop.hom f) s}
  map {V W} h s hs :=
    (properSupportSectionCalculus Λ f).2.1 F V.unop W.unop h.unop s hs

/-- The proper-support presheaf is a sheaf because support properness is local on the base. -/
theorem properSupportPresheaf_isSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Presheaf.IsSheaf Y.smallEtaleTopology (properSupportPresheaf Λ f F) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{u + 1} Λ))).2
  change Presheaf.IsSheaf _ (properSupportSubfunctor Λ f F).toFunctor
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{u + 1} Λ))).1
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).property)
  apply (Subfunctor.isSheaf_iff _ hF).2
  intro V s hs
  exact (properSupportSectionCalculus Λ f).2.2.1 F V.unop s
    ((properSupportSubfunctor Λ f F).sieveOfSection s) hs (fun W h hh => hh)

/-- The subsheaf of sections with proper support; its data are constructed, not chosen. -/
noncomputable def properSupportSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ⟨properSupportPresheaf Λ f F, properSupportPresheaf_isSheaf Λ f F⟩

/-- The inclusion of actual proper-support sections into ordinary direct-image sections. -/
noncomputable def properSupportInclusion
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    properSupportSheaf Λ f F ⟶ (lowerStar (ModuleCat.{u + 1} Λ) f).obj F :=
  ⟨{ app V := ModuleCat.ofHom (properSupportSections Λ f F V.unop).subtype
     naturality _ _ _ := by ext s; rfl }⟩

/-- A sheaf morphism acts on the underlying sections of the proper-support subsheaf. -/
noncomputable def properSupportMap
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) :
    properSupportSheaf Λ f F ⟶ properSupportSheaf Λ f G :=
  ⟨{ app V := ModuleCat.ofHom
       { toFun := fun s => ⟨φ.hom.app (op (f.Etale.obj V.unop)) s.1,
           (properSupportSectionCalculus Λ f).2.2.2.1 F G φ V.unop s.1 s.2⟩
         map_add' := fun s t => Subtype.ext (map_add _ _ _)
         map_smul' := fun r s => Subtype.ext (map_smul _ _ _) }
     naturality V W h := by
       ext s
       apply Subtype.ext
       exact ConcreteCategory.congr_hom (φ.hom.naturality (f.Etale.map h.unop).op) s.1 }⟩

/-- Direct image with proper support, constructed sectionwise. -/
noncomputable def properSupportLowerStar :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj := properSupportSheaf Λ f
  map := properSupportMap Λ f
  map_id F := by ext V s; rfl
  map_comp φ ψ := by ext V s; rfl

/-- The natural inclusion of proper-support direct image into ordinary direct image. -/
noncomputable def properSupportLowerStarInclusion :
    properSupportLowerStar Λ f ⟶ lowerStar (ModuleCat.{u + 1} Λ) f where
  app := properSupportInclusion Λ f
  naturality F G φ := by ext V s; rfl

/-- The sectionwise inclusion is injective and its image is exactly proper support. -/
theorem properSupportLowerStarInclusion_range
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) :
    Function.Injective (((properSupportLowerStarInclusion Λ f).app F).hom.app (op V)) ∧
    ∀ s, (∃ t, (((properSupportLowerStarInclusion Λ f).app F).hom.app (op V)) t = s) ↔
      SectionHasProperSupport Λ F (f.Etale.obj V) (pullback.fst V.hom f) s := by
  refine ⟨Subtype.val_injective, fun s => ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    exact t.2
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

/-- For a proper map every section belongs to the proper-support subsheaf. -/
theorem properSupportLowerStarInclusion_isIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((properSupportLowerStarInclusion Λ f).app F) := by
  have hsur (V : Y.Etale) :
      Function.Surjective (((properSupportLowerStarInclusion Λ f).app F).hom.app (op V)) := by
    intro s
    apply (properSupportLowerStarInclusion_range Λ f F V).2 s |>.2
    obtain ⟨T, hT⟩ := (properSupportSectionCalculus Λ f).2.2.2.2.2 F V s
    refine ⟨T, hT, ?_⟩
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
      pullback.fst V.hom f)
    infer_instance
  have hcomp (V : Y.Etaleᵒᵖ) :
      IsIso (((properSupportLowerStarInclusion Λ f).app F).hom.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨(properSupportLowerStarInclusion_range Λ f F V.unop).1, hsur V.unop⟩
  have : IsIso ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((properSupportLowerStarInclusion Λ f).app F)) := by
    change IsIso ((properSupportLowerStarInclusion Λ f).app F).hom
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso ((properSupportLowerStarInclusion Λ f).app F)
    (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end AlgebraicGeometry.Etale
