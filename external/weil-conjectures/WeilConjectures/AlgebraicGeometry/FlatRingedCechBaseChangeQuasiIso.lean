/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech
public import WeilConjectures.AlgebraicGeometry.RingedScalarExtensionComplexAdjunction
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.FlatRingedCechLocalComparison

/-! Quasi-isomorphism of the scalar-extended augmented model.

Source: Stacks Project, Algebraization, Tags 099I and 099H.
(auxiliary; not a blueprint node).

The canonical unit of termwise scalar extension is a quasi-isomorphism on a
locally extended Čech model. On finite generating slices this follows from the
quotient comparison, torsion of finite ordered Koszul stages, and exact filtered
colimits. Exact slice restriction and locality of isomorphisms globalize the result.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local irreducible] SheafOfModules.RingedTensor.tensorAdjunction
  SheafOfModules.RingedTensor.tensorFunctor Adjunction.mapHomologicalComplex

private theorem map_homology_isIso
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : ShortComplex D} (f : S ⟶ T)
    [ShortComplex.QuasiIso (F.mapShortComplex.map f)] :
    IsIso (F.map (ShortComplex.homologyMap f)) := by
  have he := ShortComplex.mapHomologyIso_hom_naturality f F
  have : IsIso ((S.mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap f)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_left (S.mapHomologyIso F).hom _

private theorem quasiIso_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {A : Type u} (X : A → C)
    (hX : J.CoversTop X) {K L : ringedSiteComplex R} (f : K ⟶ L)
    (hf : ∀ a, QuasiIso (((SheafOfModules.overFunctor.{u}
      (siteModuleRings R) (X a)).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  let S := HomologicalComplex.shortComplexFunctor
    (SheafOfModules.{u} (siteModuleRings R)) (.up ℤ) q
  have : IsIso ((SheafOfModules.toSheaf (siteModuleRings R)).map
      (ShortComplex.homologyMap (S.map f))) := by
    apply Sheaf.isIso_of_coversTop hX
    intro a
    let F := SheafOfModules.overFunctor.{u} (siteModuleRings R) (X a)
    have : QuasiIso (((F.mapHomologicalComplex (.up ℤ))).map f) := hf a
    have : ShortComplex.QuasiIso (F.mapShortComplex.map (S.map f)) :=
      (quasiIsoAt_iff ((F.mapHomologicalComplex (.up ℤ)).map f) q).mp inferInstance
    have := map_homology_isIso F (S.map f)
    change IsIso ((SheafOfModules.toSheaf ((siteModuleRings R).over (X a))).map
      (F.map (ShortComplex.homologyMap (S.map f))))
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (siteModuleRings R))

/-- The canonical scalar-extension unit on a locally extended Čech model is a
quasi-isomorphism. Source: Stacks Project, Algebraization, Tags 099H and 099I.
(auxiliary; not a blueprint node).

Proof: restrict to finite generating slices and apply the local scalar-unit theorem,
which uses torsion in ordered Koszul homology and exact filtered colimits. Exact
restriction and locality of isomorphisms then conclude on every homology sheaf.
-/
theorem flat_ringedCech_baseChange_data_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε) :
    QuasiIso ((ringedScalarExtensionComplexAdjunction φ).unit.app K) := by
  obtain ⟨σ, hσ⟩ := hI.exists_localGeneratorsData
  apply quasiIso_of_cover R σ.X σ.coversTop
  intro a
  have := hσ.isFiniteType a
  let τ := σ.generators a
  let := Fintype.ofFinite τ.I
  let e := Fintype.equivFin τ.I
  let f : Fin (Fintype.card τ.I) → R.obj.obj (Opposite.op (σ.X a)) := fun j ↦
    (SheafOfModules.sectionsMap (I.inclusion.over (σ.X a)) (τ.s (e.symm j))).val
      (Opposite.op (Over.mk (𝟙 (σ.X a))))
  have hf : IsRingedIdealGeneratingList R I.module I.inclusion (σ.X a)
      (Fintype.card τ.I) f := by
    refine ⟨τ, e, ?_⟩
    intro i
    simp only [f, Equiv.symm_apply_apply]
  obtain ⟨α, _⟩ := hK (σ.X a) (Fintype.card τ.I) f hf
  exact flat_ringedCech_local_unit_quasiIso φ I hflat hquot (σ.X a) _ f hf K α

end CategoryTheory
