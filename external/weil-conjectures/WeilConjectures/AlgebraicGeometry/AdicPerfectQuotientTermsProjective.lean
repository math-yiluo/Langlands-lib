/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelComplexes
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Projectivity of ordinary quotient terms -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] adicResidueLocalReductionStep
  adicResidueConstantPerfect adicResidueRestriction
  adicPerfectLocalComplex derivedExtension extend change
  adicPerfectQuotientComplex adicPerfectQuotientStep

private theorem slice_unit_projective {D : Type v} [SmallCategory D]
    (T : GrothendieckTopology D) (U : D) (R : Sheaf (T.over U) RingCat.{v})
    (hU : ∀ (F G : Sheaf (T.over U) (Type v)) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (Over.mk (𝟙 U))))) :
    Projective (SheafOfModules.unit R) := by
  let W : Over U := Over.mk (𝟙 U)
  let ev := SheafOfModules.evaluation.{v} R (op W)
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf.{v} R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v} g).mpr inferInstance
    let g' := (sheafCompose (T.over U) (CategoryTheory.forget AddCommGrpCat.{v})).map g
    have : Epi g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hU _ _ g' inferInstance)
  let a (V : Over U) : V ⟶ W := Over.homMk V.hom
  have ha {V Z : Over U} (f : V ⟶ Z) : f ≫ a Z = a V :=
    Over.OverMorphism.ext (Over.w f)
  constructor
  intro M N f e he
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (ev.map e)).mp inferInstance
    ((N.unitHomEquiv f).val (op W))
  change e.val.app (op W) x = _ at hx
  let s : M.sections := M.val.sectionsMk
    (fun V ↦ M.val.map (a V.unop).op x) (by
      intro V Z g
      rw [← M.val.map_comp_apply]
      have h : (a V.unop).op ≫ g = (a Z.unop).op :=
        congrArg Quiver.Hom.op (ha g.unop)
      rw [h])
  refine ⟨M.unitHomEquiv.symm s, ?_⟩
  apply N.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro V
  change e.val.app V (M.val.map (a V.unop).op x) = (N.unitHomEquiv f).val V
  rw [PresheafOfModules.naturality_apply, hx]
  exact PresheafOfModules.sections_property _ _

private noncomputable def restrict_unit_iso {D : Type v} [SmallCategory D]
    {T : GrothendieckTopology D} {R S : Sheaf T RingCat.{v}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars e.inv).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  apply (SheafOfModules.fullyFaithfulForget S).preimageIso
  refine PresheafOfModules.isoMk
    (fun V ↦ ModuleCat.restrictScalarsIsoOfEquiv ((sheafToPresheaf T RingCat).mapIso
      e.symm |>.app V |>.ringCatIsoToRingEquiv)) ?_
  intro V W f
  ext x
  exact ConcreteCategory.congr_hom (e.hom.hom.naturality f) x

open scoped ChangeOfRings in
private noncomputable def change_unit_iso {D : Type v} [SmallCategory D]
    {T : GrothendieckTopology D} {R S : Sheaf T CommRingCat.{v}} (φ : R ⟶ S) :
    (change φ).obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S) := by
  unfold change
  let O := siteModuleRings R
  let A := siteModuleRings S
  let e (V : Dᵒᵖ) :
      (SheafOfModules.changeOfRingsPresheaf.{v, v, v} φ (SheafOfModules.unit O)).obj V ≅
        (SheafOfModules.unit A).val.obj V := by
    let := (φ.hom.app V).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj V)
      (S.obj.obj V) (S.obj.obj V)).toModuleIso
  let ep : SheafOfModules.changeOfRingsPresheaf.{v, v, v} φ (SheafOfModules.unit O) ≅
      (SheafOfModules.unit A).val :=
    PresheafOfModules.isoMk e (by
      intro X Y f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (e Y).hom (SheafOfModules.changeOfRingsMap.{v, v, v} φ (SheafOfModules.unit O) f
        ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x)) =
          S.obj.map f ((e X).hom
            ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x))
      erw [Classical.choose_spec
        (SheafOfModules.exists_changeOfRingsMap.{v, v, v} φ (SheafOfModules.unit O) f) 1 x, map_one]
      change (φ.hom.app Y) (R.obj.map f x) * 1 =
        S.obj.map f ((φ.hom.app X) x * 1)
      simp only [mul_one]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) x)
  exact (PresheafOfModules.sheafification.{v} (R := A) (𝟙 _)).mapIso ep ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).counit.app
      (SheafOfModules.unit A))

/-- Each term of the actual ordinary quotient complex is projective on the slice.
Source: Stacks Project, Tags 09C5 and 09C6 (exact sections on weakly contractible
objects and finite-projective constant models).
(auxiliary; not a blueprint node).

Proof: choose a splitting of each finite projective A-module P.X i from a finite
free A-module. The composite of termwise constant realization, restriction of
scalars along the constant-ring isomorphism, extension to the completed ring,
slice restriction and ordinary quotient extension is a functor, so it preserves
this retraction. It sends the finite free module to the corresponding finite sum
of the quotient ring's unit sheaf: constant realization has its canonical free
basis, extension sends the unit to the unit and preserves finite sums, and slice
restriction preserves the same finite free basis. The slice hypothesis makes
terminal sections of every epimorphism of module sheaves surjective, by forgetting
to set sheaves. A morphism from the unit is such a terminal section, so it lifts
against every epimorphism. Thus the unit is projective. Finite sums and retracts
of projectives are projective, proving the assertion in every degree. The zero
module, zero ring, unit ideal and empty slice are included by the same argument;
no nonzero or nonempty basis is used. -/
theorem adicPerfectQuotientComplex_terms_projective (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) :
    let R := fun n : ℕ ↦
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U
    let C : (n : ℕ) → Cx (R n) := fun n ↦ adicPerfectQuotientComplex.{u, v} X J U P n
    ∀ (n : ℕ) (i : ℤ), Projective ((C n).X i) := by
  dsimp only
  intro n i
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := (constantSheaf T RingCat.{max v (u + 1)}).obj (RingCat.of A)
  let S := completed T A J
  let Q := (finite T A J n).over U
  let H : SheafOfModules.{max v (u + 1)} B ⥤ Mod Q :=
    SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv ⋙
      change (coefficientMap T A J) ⋙ SheafOfModules.overFunctor _ U ⋙
        change (adicResidueLocalProjection.{u, v} X J U n)
  let : (SheafOfModules.overFunctor (siteModuleRings S) U).Additive :=
    ringedOverFunctor_additive S U
  have : (change (coefficientMap T A J)).Additive := change_additive _
  have : (change (adicResidueLocalProjection.{u, v} X J U n)).Additive := change_additive _
  have : (SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv).Additive :=
    inferInstance
  have : H.Additive := by
    dsimp only [H]
    infer_instance
  let F := SheafOfModules.strictPerfectConstantSheaf T A ⋙ H
  unfold adicPerfectQuotientComplex adicPerfectLocalComplex
  change Projective (F.obj (P.X i))
  let e₁ : (change (coefficientMap T A J)).obj
      ((SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv).obj
        (SheafOfModules.unit B)) ≅ SheafOfModules.unit (siteModuleRings S) :=
    (change (coefficientMap T A J)).mapIso
      (restrict_unit_iso (constantModuleHomRingIso T A)) ≪≫
        change_unit_iso (coefficientMap T A J)
  let e₂ : H.obj (SheafOfModules.unit B) ≅ SheafOfModules.unit (siteModuleRings Q) :=
    (change (adicResidueLocalProjection.{u, v} X J U n)).mapIso
      ((SheafOfModules.overFunctor _ U).mapIso e₁) ≪≫
        change_unit_iso (adicResidueLocalProjection.{u, v} X J U n)
  have hunit : Projective (SheafOfModules.unit (siteModuleRings Q)) :=
    slice_unit_projective T U (siteModuleRings Q) _hU
  let := (_hP i).1
  let := (_hP i).2
  obtain ⟨k, p, hp⟩ := Module.Finite.exists_fin' A (P.X i)
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  let r : Retract (P.X i) (ModuleCat.of A (Fin k → A)) :=
    { i := ModuleCat.ofHom s
      r := ModuleCat.ofHom p
      retract := by
        apply ModuleCat.hom_ext
        exact hs }
  let e : F.obj (ModuleCat.of A (Fin k → A)) ≅
      ∏ᶜ fun _ : Fin k ↦ SheafOfModules.unit (siteModuleRings Q) :=
    H.mapIso (asIso (SheafOfModules.strictPerfectConstantFiniteFreeComparison T A k)) ≪≫
      PreservesProduct.iso H (fun _ : Fin k ↦ SheafOfModules.unit B) ≪≫
        Pi.mapIso (fun _ : Fin k ↦ e₂)
  let : HasFiniteBiproducts (Mod Q) := HasFiniteBiproducts.of_hasFiniteProducts
  let := hunit
  have : Projective (∏ᶜ fun _ : Fin k ↦ SheafOfModules.unit (siteModuleRings Q)) :=
    Projective.of_iso (biproduct.isoProduct
      (fun _ : Fin k ↦ SheafOfModules.unit (siteModuleRings Q))) ⟨by
        intro M N f e he
        refine ⟨biproduct.desc (fun j ↦ Projective.factorThru
          (biproduct.ι (fun _ : Fin k ↦ SheafOfModules.unit (siteModuleRings Q)) j ≫ f)
            e), ?_⟩
        apply biproduct.hom_ext'
        intro j
        simp⟩
  have : Projective (F.obj (ModuleCat.of A (Fin k → A))) :=
    Projective.of_iso e.symm inferInstance
  exact (r.map F).projective

end AlgebraicGeometry.Scheme
