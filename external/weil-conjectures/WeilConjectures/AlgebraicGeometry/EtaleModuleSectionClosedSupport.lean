/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen

/-! # Closed support of sections of module sheaves

Source: Stacks Project, Tags 04FR, 04FT and 0F4X
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Forgetting the scalar action detects vanishing of a geometric germ.
Source: Stacks Project, Tag 04FR.
(auxiliary; not a blueprint node). -/
theorem etaleModuleGerm_zero
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (v : Spec (.of Ω) ⟶ V.left) :
    (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.obj s = 0 ↔
      (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v)
        (F.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) s = 0 := by
  let Φ := Scheme.pointSmallEtale (v ≫ V.hom)
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : PreservesFilteredColimitsOfSize.{u, u} U :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} U
  let e := (Φ.presheafFiberCompIso U).app F.obj
  have he := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app U V (Over.homMk v) F.obj) s
  change e.hom (Φ.toPresheafFiber V (Over.homMk v) (F.obj ⋙ U) s) =
    Φ.toPresheafFiber V (Over.homMk v) F.obj s at he
  have hinj : Function.Injective e.hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (by infer_instance) |>.1
  constructor
  · intro h
    apply hinj
    rw [map_zero]
    exact he.trans h
  · intro h
    rw [← he, h, map_zero]

/-- The nonzero geometric germs of a module-sheaf section form a closed subset.
Source: Stacks Project, Tags 04FR and 04FT.
(auxiliary; not a blueprint node). -/
theorem etaleModuleSection_closedSupport
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (s : F.obj.obj (op V)) :
    ∃ T : TopologicalSpace.Closeds V.left,
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left),
        v default ∈ T ↔
          (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
            (Over.homMk v) F.obj s ≠ 0) ∧
      (T : Set V.left) =
        {x | ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
          (v : Spec (.of Ω) ⟶ V.left), v default = x ∧
            (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
              (Over.homMk v) F.obj s ≠ 0} := by
  classical
  let FA := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  obtain ⟨W, i, hi, _, hg⟩ := Scheme.etale_section_zero_open X FA V s
  have : IsOpenImmersion i.left := hi
  let T : TopologicalSpace.Closeds V.left :=
    ⟨(Set.range i.left)ᶜ, i.left.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have hT (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left) :
      v default ∈ T ↔
        (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
          (Over.homMk v) F.obj s ≠ 0 := by
    change v default ∉ Set.range i.left ↔ _
    rw [ne_eq, etaleModuleGerm_zero Λ F V s Ω v]
    change v default ∉ Set.range i.left ↔
      ¬ (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) FA.obj s = 0
    rw [hg Ω v]
    apply not_congr
    constructor
    · rintro ⟨x, hx⟩
      have hr : Set.range v ⊆ Set.range i.left := by
        rintro z ⟨q, rfl⟩
        have hq : q = default := Subsingleton.elim _ _
        exact ⟨x, hx.trans (congrArg v hq).symm⟩
      exact ⟨IsOpenImmersion.lift i.left v hr, IsOpenImmersion.lift_fac _ _ _⟩
    · rintro ⟨y, hy⟩
      exact ⟨y default, congrArg (fun k => k default) hy⟩
  refine ⟨T, hT, ?_⟩
  ext x
  constructor
  · intro hx
    let Ω := AlgebraicClosure (V.left.residueField x)
    let v : Spec (.of Ω) ⟶ V.left := V.left.algClosurePoint x
    have hv : v default = x := Scheme.algClosurePoint_base _ _ _
    refine ⟨Ω, inferInstance, inferInstance, v, hv, ?_⟩
    exact (hT Ω v).1 (hv.symm ▸ hx)
  · rintro ⟨Ω, _, _, v, rfl, hs⟩
    exact (hT Ω v).2 hs

/-- Proper support is independent of testing at algebraically closed or at all separably
closed geometric points.
Source: Stacks Project, Tags 04FR and 04FT
(auxiliary; not a blueprint node). -/
theorem sectionHasProperSupport_iff
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (p : V.left ⟶ S) [LocallyOfFiniteType p] (s : F.obj.obj (op V)) :
    SectionHasProperSupport Λ F V p s ↔
      ∃ T : TopologicalSpace.Closeds V.left,
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V.left),
          v default ∈ T ↔
            (Scheme.pointSmallEtale (v ≫ V.hom)).toPresheafFiber V
              (Over.homMk v) F.obj s ≠ 0) ∧
        IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ p) := by
  classical
  obtain ⟨T, hT, hTa⟩ := etaleModuleSection_closedSupport Λ F V s
  constructor
  · rintro ⟨U, hU, hp⟩
    have hUT : U = T := TopologicalSpace.Closeds.ext (hU.trans hTa.symm)
    subst U
    exact ⟨T, hT, hp⟩
  · rintro ⟨U, hU, hp⟩
    refine ⟨U, ?_, hp⟩
    ext x
    constructor
    · intro hx
      let Ω := AlgebraicClosure (V.left.residueField x)
      let v : Spec (.of Ω) ⟶ V.left := V.left.algClosurePoint x
      have hv : v default = x := Scheme.algClosurePoint_base _ _ _
      exact ⟨Ω, inferInstance, inferInstance, v, hv, (hU Ω v).1 (hv.symm ▸ hx)⟩
    · rintro ⟨Ω, _, _, v, rfl, hs⟩
      exact (hU Ω v).2 hs

end AlgebraicGeometry.Etale
