/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ScalarExtensionMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Normalized oplax data for global section scalar extension

This auxiliary statement isolates the sectionwise tensor comparison and its unit
normalization.  The main module turns invertible oplax data into a strong monoidal
structure using the standard categorical constructor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive

private theorem bottom_unit_isIso
    {D : Type u} [SmallCategory D]
    (R : Sheaf (⊥ : GrothendieckTopology D) RingCat.{u})
    (M : PresheafOfModules.{u} R.obj) :
    IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf R.obj)]
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact CategoryTheory.isIso_toSheafify _ (Presheaf.isSheaf_bot _)

@[instance_reducible]
private noncomputable def bottomForgetMonoidal
    {D : Type u} [SmallCategory D]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{u}) :
    letI := SheafOfModules.monoidalCategory O
    (SheafOfModules.forget.{u} ((sheafCompose ⊥
      (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⋙
      PresheafOfModules.restrictScalars (𝟙 _)).Monoidal := by
  letI := SheafOfModules.monoidalCategory O
  let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj O
  let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let V := SheafOfModules.forget.{u} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  letI := SheafOfModules.sheafificationMonoidal O
  letI := adj.rightAdjointLaxMonoidal
  haveI (M : PresheafOfModules.{u} R.obj) : IsIso (adj.unit.app M) :=
    bottom_unit_isIso R M
  haveI : IsIso (Functor.LaxMonoidal.ε V) := by
    dsimp only [Adjunction.rightAdjointLaxMonoidal_ε]
    rw [Adjunction.homEquiv_unit]
    infer_instance
  haveI : IsIso adj.counit := by dsimp only [adj]; infer_instance
  haveI (M N : SheafOfModules.{u} R) :
      IsIso (Functor.LaxMonoidal.μ V M N) := by
    dsimp only [Adjunction.rightAdjointLaxMonoidal_μ]
    rw [Adjunction.homEquiv_unit]
    haveI : IsIso (Functor.OplaxMonoidal.δ L (V.obj M) (V.obj N)) := inferInstance
    haveI : IsIso (adj.counit.app M) := inferInstance
    haveI : IsIso (adj.counit.app N) := inferInstance
    haveI : IsIso (adj.counit.app M ⊗ₘ adj.counit.app N) :=
      (asIso (adj.counit.app M) ⊗ᵢ asIso (adj.counit.app N)).isIso_hom
    rw [V.map_comp]
    infer_instance
  exact Functor.Monoidal.ofLaxMonoidal _

private theorem bottomForgetMonoidal_unit
    {D : Type u} [SmallCategory D]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{u}) :
    letI := SheafOfModules.monoidalCategory O
    letI := bottomForgetMonoidal O
    Functor.OplaxMonoidal.η (SheafOfModules.forget.{u} ((sheafCompose ⊥
      (forget₂ CommRingCat.{u} RingCat.{u})).obj O) ⋙
      PresheafOfModules.restrictScalars (𝟙 _)) = 𝟙 _ := by
  letI := SheafOfModules.monoidalCategory O
  let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj O
  let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let V := SheafOfModules.forget.{u} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  letI := SheafOfModules.sheafificationMonoidal O
  letI := adj.rightAdjointLaxMonoidal
  have hη : Functor.OplaxMonoidal.η L = adj.counit.app (𝟙_ _) := rfl
  have hε : Functor.LaxMonoidal.ε V = 𝟙 _ := by
    change adj.unit.app _ ≫ V.map (Functor.OplaxMonoidal.η L) = _
    rw [hη]
    exact adj.right_triangle_components (SheafOfModules.unit R)
  haveI : IsIso (Functor.LaxMonoidal.ε V) := by rw [hε]; infer_instance
  change inv (Functor.LaxMonoidal.ε V) = _
  apply (cancel_mono (Functor.LaxMonoidal.ε V)).1
  simp only [IsIso.inv_hom_id, hε]
  exact (Category.id_comp _).symm

attribute [irreducible] bottomForgetMonoidal

private noncomputable def constantComparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    let A := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
    let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
    (SheafOfModules.forget.{u} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
      PresheafOfModules.pushforward₀OfCommRingCat
        ((Functor.const C).obj (Discrete.mk PUnit.unit)) A.obj ≅
          ringFamilyConstantPresheaf O := by
  refine NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk (fun X ↦ Iso.refl _)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change M.val.map (𝟙 (op (Discrete.mk PUnit.unit))) x = x
      simp)) ?_
  · intro M N f
    ext X x
    rfl

@[instance_reducible]
private noncomputable def constantPresheafMonoidal
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    MonoidalCategory (PresheafOfModules.{u}
      ((Functor.const Cᵒᵖ).obj (RingCat.of (ringFamilyGlobalRing O)))) :=
  PresheafOfModules.monoidalCategory
    (R := (Functor.const Cᵒᵖ).obj (ringFamilyGlobalRing O))

@[instance_reducible]
private noncomputable def constantMonoidal
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    letI := SheafOfModules.monoidalCategory
      (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
    letI := constantPresheafMonoidal O
    (ringFamilyConstantPresheaf O).Monoidal := by
  letI := constantPresheafMonoidal O
  let A := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
  letI := SheafOfModules.monoidalCategory A
  letI := bottomForgetMonoidal A
  let P := PresheafOfModules.pushforward₀OfCommRingCat
    ((Functor.const C).obj (Discrete.mk PUnit.unit)) A.obj
  letI : P.Monoidal := inferInstance
  exact Functor.Monoidal.transport (constantComparison O)

private theorem constantMonoidal_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    letI := SheafOfModules.monoidalCategory
      (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
    letI := constantPresheafMonoidal O
    letI := constantMonoidal O
    Functor.OplaxMonoidal.η (ringFamilyConstantPresheaf O) = 𝟙 _ := by
  let A := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
  letI := SheafOfModules.monoidalCategory A
  letI := bottomForgetMonoidal A
  letI := constantPresheafMonoidal O
  change (constantComparison O).inv.app _ ≫
    (PresheafOfModules.pushforward₀OfCommRingCat
      ((Functor.const C).obj (Discrete.mk PUnit.unit)) A.obj).map
        (Functor.OplaxMonoidal.η _) ≫ _ = _
  rw [bottomForgetMonoidal_unit A]
  ext X
  rfl

attribute [irreducible] constantMonoidal

/-- The scalar extension has invertible oplax tensor data normalized by the fixed
multiplication morphism.  This is the sectionwise tensor calculation used by the
main monoidal theorem.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E.
(auxiliary; not a blueprint node).
-/
theorem ringFamilyGlobalExtension_oplax_normalized
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.monoidalCategory
      (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
    ∃ oplax : (ringFamilyGlobalExtension O).OplaxMonoidal,
      IsIso oplax.η ∧ (∀ M N, IsIso (oplax.δ M N)) ∧
        oplax.η = ringFamilyGlobalExtensionUnit O := by
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.monoidalCategory
    (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
  let R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
  letI := constantPresheafMonoidal O
  let K := (Functor.const Cᵒᵖ).obj (ringFamilyGlobalRing O)
  let φ := ringFamilyGlobalEvaluation O
  let F := ringFamilyConstantPresheaf O
  let P := PresheafOfModules.pullback.{u} φ
  let S := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let a := PresheafOfModules.pullbackPushforwardAdjunction.{u} φ
  let b := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  obtain ⟨mon, hmon⟩ := PresheafOfModules.exists_pullback_monoidal_normalized K O.obj φ
  letI : P.Monoidal := mon
  letI : F.Monoidal := constantMonoidal O
  letI : S.Monoidal := SheafOfModules.sheafificationMonoidal O
  -- Unfold the functor before composing, so its coherence data stay shared.
  letI : (ringFamilyGlobalExtension O).Monoidal := by
    change (F ⋙ P ⋙ S).Monoidal
    infer_instance
  refine ⟨inferInstance, inferInstance, fun M N ↦ inferInstance, ?_⟩
  change S.map (P.map (Functor.OplaxMonoidal.η F)) ≫
    S.map (Functor.OplaxMonoidal.η P) ≫ Functor.OplaxMonoidal.η S = _
  rw [constantMonoidal_unit O, P.map_id, S.map_id, Category.id_comp]
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  have hηS : Functor.OplaxMonoidal.η S = b.counit.app (SheafOfModules.unit R) := rfl
  rw [hηS]
  erw [← b.homEquiv_symm_id (SheafOfModules.unit R), Equiv.apply_symm_apply]
  erw [Category.comp_id]
  dsimp only [ringFamilyGlobalExtensionUnit]
  erw [Equiv.apply_symm_apply]
  apply (a.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  ext1 X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact hmon X r

end CategoryTheory
