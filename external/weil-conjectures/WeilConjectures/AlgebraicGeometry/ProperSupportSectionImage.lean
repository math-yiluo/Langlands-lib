/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen

/-! # Support of a section of the proper-support direct image

Source: Stacks Project, Tag 0F50.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- A module-sheaf section with zero germs at every separably closed geometric point is zero.

Source: Stacks Project, Tags 04FR and 04FT; the zero-open criterion.
(auxiliary; not a blueprint node)

Proof: Apply the additive zero-open criterion after forgetting scalars. At each point
of the etale object choose an algebraic closure of its residue field. The zero germ
lifts this geometric point to the zero open, so that open contains every point.
The zero-open criterion applied to the identity then makes the original section zero. -/
theorem module_section_zero_of_germs
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V))
    (hs : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left),
      (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.obj s = 0) :
    s = 0 := by
  let FA := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  obtain ⟨W, i, _, hz, hg⟩ := Scheme.etale_section_zero_open X FA V s
  have hr : Set.range i.left = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let Ω := AlgebraicClosure (V.left.residueField x)
    let v : Spec (.of Ω) ⟶ V.left := V.left.algClosurePoint x
    have hv : v default = x := Scheme.algClosurePoint_base _ _ _
    have h0 := (etaleModuleGerm_zero Λ F V s Ω v).1 (hs Ω v)
    obtain ⟨w, hw⟩ := (hg Ω v).1 h0
    exact ⟨w default, (congrArg (fun k => k default) hw).trans hv⟩
  have h0 := (hz V (𝟙 V)).2 (show Set.range ((𝟙 V : V ⟶ V).left) ⊆ Set.range i.left by
    rw [hr]
    exact Set.subset_univ _)
  change F.obj.map (𝟙 V).op s = 0 at h0
  simpa using h0

private theorem germ_zero_off_support_image
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (s : ((properSupportLowerStar Λ f).obj F).obj.obj (op V))
    (T : TopologicalSpace.Closeds (f.Etale.obj V).left)
    (hT : ∀ (K : Type u) [Field K] [IsSepClosed K]
      (k : Spec (.of K) ⟶ (f.Etale.obj V).left), k default ∈ T ↔
      (Scheme.pointSmallEtale (k ≫ (f.Etale.obj V).hom)).toPresheafFiber
        (f.Etale.obj V) (Over.homMk k) F.obj s.val ≠ 0)
    (I : TopologicalSpace.Closeds V.left)
    (hI : (I : Set V.left) =
      (fun x : (f.Etale.obj V).left => pullback.fst V.hom f x) '' (T : Set _))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left)
    (hnv : v default ∉ I) :
    (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v)
      ((properSupportLowerStar Λ f).obj F).obj s = 0 := by
  classical
  let G := (properSupportLowerStar Λ f).obj F
  let Φ := Scheme.pointSmallEtale (v ≫ V.hom)
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
    change w ≫ O.ι ≫ V.hom = v ≫ V.hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac])
  have hw : Φ.fiber.map h w' = Over.homMk v := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac O.ι v hvr
  have eg := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w h w' G.obj) s
  change Φ.toPresheafFiber W w' G.obj (G.obj.map h.op s) =
    Φ.toPresheafFiber V (Φ.fiber.map h w') G.obj s at eg
  rw [hs0, map_zero, hw] at eg
  exact eg.symm

/-- The support of a section of the proper-support direct image is the closed image
of the support of its underlying section.

Source: Stacks Project, Tag 0F50, support-image argument.
(auxiliary; not a blueprint node)

Proof:
Choose the closed support T of the underlying section. It is proper over V by the
section's subtype property, so its image I is closed. Off I restrict to its open
complement. The germ restriction formula shows that every restricted germ vanishes;
the zero-open theorem makes the section zero, and hence its direct-image germ is zero.
Conversely, a zero direct-image germ gives a Zariski zero neighbourhood W of the
marked point. If that point lies in I, choose x in T over it and an algebraically
closed geometric point k over x. Lift k's projection to W (an open neighbourhood),
then use the Cartesian restriction square to lift k itself to X_W. Restriction of the
section to W is zero, so its germ at this lift is zero. Germ compatibility contradicts
k's membership in T. Thus the direct-image germ is nonzero exactly on I. -/
theorem properSupportSectionImage (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale)
    (s : ((properSupportLowerStar Λ f).obj F).obj.obj (op V)) :
    ∃ (T : TopologicalSpace.Closeds (f.Etale.obj V).left)
      (I : TopologicalSpace.Closeds V.left),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (v : Spec (.of Ω) ⟶ (f.Etale.obj V).left), v default ∈ T ↔
        (Scheme.pointSmallEtale (v ≫ (f.Etale.obj V).hom)).toPresheafFiber
          (f.Etale.obj V) (Over.homMk v) F.obj s.val ≠ 0) ∧
      Scheme.IsClosedSubsetProperOver (pullback.fst V.hom f) T ∧
      (I : Set V.left) =
        (fun x : (f.Etale.obj V).left => pullback.fst V.hom f x) '' (T : Set _) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left),
        v default ∈ I ↔ (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
          (Over.homMk v) ((properSupportLowerStar Λ f).obj F).obj s ≠ 0) := by
  classical
  let G := (properSupportLowerStar Λ f).obj F
  obtain ⟨T, hT, hp⟩ := (sectionHasProperSupport_iff Λ F (f.Etale.obj V)
    (pullback.fst V.hom f) s.val).1 s.property
  have : LocallyOfFiniteType (𝟙 V.left) := MorphismProperty.id_mem _ _
  have : IsSeparated (𝟙 V.left) := MorphismProperty.id_mem _ _
  obtain ⟨I, hI, _⟩ :=
    (Scheme.closed_subset_proper_over_base_properties (pullback.fst V.hom f) T).2.2.2
      (pullback.fst V.hom f) (𝟙 V.left) (by simp) hp
  change TopologicalSpace.Closeds V.left at I
  refine ⟨T, I, hT, hp, hI, ?_⟩
  intro Ω _ _ v
  constructor
  · intro hvI hz
    let GA := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
    obtain ⟨W, i, hi, hzero, hg⟩ := Scheme.etale_section_zero_open Y GA V s
    have : IsOpenImmersion i.left := hi
    obtain ⟨w, hw⟩ := (hg Ω v).1 ((etaleModuleGerm_zero Λ G V s Ω v).1 hz)
    change v default ∈ (I : Set V.left) at hvI
    rw [hI] at hvI
    obtain ⟨x, hxT, hx⟩ := hvI
    let K := AlgebraicClosure ((f.Etale.obj V).left.residueField x)
    let k : Spec (.of K) ⟶ (f.Etale.obj V).left :=
      (f.Etale.obj V).left.algClosurePoint x
    have hk : k default = x := Scheme.algClosurePoint_base _ _ _
    have hpr : Set.range (k ≫ pullback.fst V.hom f) ⊆ Set.range i.left := by
      rintro _ ⟨a, rfl⟩
      have ha : a = default := Subsingleton.elim _ _
      rw [Scheme.Hom.comp_apply, ha, hk]
      exact hx.symm ▸ ⟨w default, congrArg (fun a => a default) hw⟩
    let w' := IsOpenImmersion.lift i.left (k ≫ pullback.fst V.hom f) hpr
    let sq := etaleObjectPullbackSquare f i
    let k' := sq.lift k w' (IsOpenImmersion.lift_fac _ _ _).symm
    have h0 : G.obj.map i.op s = 0 := (hzero W i).2 (Set.Subset.refl _)
    have h00 : F.obj.map (f.Etale.map i).op s.val = 0 := by
      exact congrArg Subtype.val h0
    have hkg :
        (Scheme.pointSmallEtale (k' ≫ (f.Etale.obj W).hom)).toPresheafFiber
          (f.Etale.obj W) (Over.homMk k') F.obj
          (F.obj.map (f.Etale.map i).op s.val) = 0 := by rw [h00, map_zero]
    have ho := (etaleModuleGerm_restrict_zero Λ F (f.Etale.map i) s.val K k').1 hkg
    apply ((hT K (k' ≫ (f.Etale.map i).left)).1 ?_) ho
    rw [sq.lift_fst, hk]
    exact hxT
  · intro hn
    by_contra hvI
    exact hn (germ_zero_off_support_image Λ f F V s T hT I hI Ω v hvI)

end AlgebraicGeometry.Etale
