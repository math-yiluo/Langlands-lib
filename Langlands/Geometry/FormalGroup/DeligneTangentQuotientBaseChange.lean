import Langlands.Geometry.FormalGroup.DeligneAdmissibility
import Langlands.Geometry.FormalGroup.DelignePreDatumBaseChange
import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Actual tangent Pi quotient and residue-fibre comparisons -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace

section QuotientExtension

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- Actual scalar extension commutes with quotient by a morphism's range. -/
def extendScalarsRangeQuotientIso (ρ : R →+* R') {M N : ModuleCat.{u} R} (p : M ⟶ N) :
    (ModuleCat.extendScalars ρ).obj (ModuleCat.of R (N ⧸ LinearMap.range p.hom)) ≅
      ModuleCat.of R' ((ModuleCat.extendScalars ρ).obj N ⧸
        LinearMap.range ((ModuleCat.extendScalars ρ).map p).hom) :=
  (ModuleCat.extendScalars ρ).mapIso (ModuleCat.cokernelIsoRangeQuotient p).symm ≪≫
    PreservesCokernel.iso (ModuleCat.extendScalars ρ) p ≪≫
      ModuleCat.cokernelIsoRangeQuotient ((ModuleCat.extendScalars ρ).map p)

/-- The scalar-extension quotient comparison respects the actual quotient projections. -/
theorem extendScalarsRangeQuotientIso_mkQ (ρ : R →+* R')
    {M N : ModuleCat.{u} R} (p : M ⟶ N) :
    (ModuleCat.extendScalars ρ).map (ModuleCat.ofHom (LinearMap.range p.hom).mkQ) ≫
        (extendScalarsRangeQuotientIso ρ p).hom =
      ModuleCat.ofHom (LinearMap.range ((ModuleCat.extendScalars ρ).map p).hom).mkQ := by
  simp only [extendScalarsRangeQuotientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, ← Category.assoc, ← Functor.map_comp,
    ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv]
  rw [Category.assoc, PreservesCokernel.π_iso_hom_assoc,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

end QuotientExtension

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- The actual total tangent stalk of pullback is extension along the actual stalk map. -/
def tangentStalkPullbackIso (x : S') :
    ModuleCat.of (S'.presheaf.stalk x) ((D.pullback f).tangentStalk x) ≅
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
        (ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentStalk (f x))) :=
  (Langlands.AlgebraicGeometry.Modules.StalkPullback.pullbackStalkIso f x).app
    D.tangent.graded.module

/-- Naturality of the actual structural comparison gives its Pi square. -/
theorem tangentStalkPullbackIso_pi (x : S') :
    ModuleCat.ofHom ((D.pullback f).tangentStalkPi x) ≫
        (D.tangentStalkPullbackIso f x).hom =
      (D.tangentStalkPullbackIso f x).hom ≫
        (ModuleCat.extendScalars (f.stalkMap x).hom).map
          (ModuleCat.ofHom (D.tangentStalkPi (f x))) := by
  exact (Langlands.AlgebraicGeometry.Modules.StalkPullback.pullbackStalkIso f x).hom.naturality
    D.tangent.graded.pi

/-- The actual pulled tangent Pi range is the extended Pi operator's range. -/
theorem tangentStalkPullbackIso_range (x : S') :
    (LinearMap.range ((D.pullback f).tangentStalkPi x)).map
        (D.tangentStalkPullbackIso f x).toLinearEquiv.toLinearMap =
      LinearMap.range
        ((ModuleCat.extendScalars (f.stalkMap x).hom).map
          (ModuleCat.ofHom (D.tangentStalkPi (f x)))).hom := by
  have h (t : (D.pullback f).tangentStalk x) :=
    congrArg (fun k => k t) (D.tangentStalkPullbackIso_pi f x)
  ext y
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨(D.tangentStalkPullbackIso f x).hom t, (h t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨t, rfl⟩ := (D.tangentStalkPullbackIso f x).toLinearEquiv.surjective t
    exact ⟨(D.pullback f).tangentStalkPi x t, ⟨t, rfl⟩, h t⟩

/-- The actual tangent Pi quotient commutes with arbitrary scheme base change. -/
def tangentPiQuotientPullbackIso (x : S') :
    ModuleCat.of (S'.presheaf.stalk x) ((D.pullback f).tangentPiQuotient x) ≅
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
        (ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentPiQuotient (f x))) :=
  (Submodule.Quotient.equiv _ _ (D.tangentStalkPullbackIso f x).toLinearEquiv
    (D.tangentStalkPullbackIso_range f x)).toModuleIso ≪≫
      (extendScalarsRangeQuotientIso (f.stalkMap x).hom
        (ModuleCat.ofHom (D.tangentStalkPi (f x)))).symm

/-- The inverse tangent quotient comparison respects the actual quotient projections. -/
theorem tangentPiQuotientPullbackIso_inv_mkQ (x : S') :
    (ModuleCat.extendScalars (f.stalkMap x).hom).map
        (ModuleCat.ofHom (LinearMap.range (D.tangentStalkPi (f x))).mkQ) ≫
        (D.tangentPiQuotientPullbackIso f x).inv =
      (D.tangentStalkPullbackIso f x).inv ≫
        ModuleCat.ofHom (LinearMap.range ((D.pullback f).tangentStalkPi x)).mkQ := by
  dsimp only [tangentPiQuotientPullbackIso, Iso.trans_inv, Iso.symm_inv]
  rw [← Category.assoc]
  erw [extendScalarsRangeQuotientIso_mkQ (f.stalkMap x).hom
    (ModuleCat.ofHom (D.tangentStalkPi (f x)))]
  ext t
  rfl

/-- The actual pulled residue fibre is residue-field extension of the original one. -/
def tangentPiQuotientFibrePullbackIso (x : S') :
    (D.pullback f).tangentPiQuotientFibre x ≅
      (ModuleCat.extendScalars (f.residueFieldMap x).hom).obj
        (D.tangentPiQuotientFibre (f x)) := by
  let M := ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentPiQuotient (f x))
  let ρ := (f.stalkMap x).hom
  let σ := (S'.residue x).hom
  let α := (S.residue (f x)).hom
  let β := (f.residueFieldMap x).hom
  have h : σ.comp ρ = β.comp α :=
    congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x).symm
  let i₁ := (ModuleCat.extendScalars σ).mapIso (D.tangentPiQuotientPullbackIso f x)
  let i₂ := ((ModuleCat.extendScalarsComp ρ σ).app M).symm
  let i₃ : (ModuleCat.extendScalars (σ.comp ρ)).obj M ≅
      (ModuleCat.extendScalars (β.comp α)).obj M :=
    eqToIso (congrArg (fun γ => (ModuleCat.extendScalars γ).obj M) h)
  let i₄ := (ModuleCat.extendScalarsComp α β).app M
  exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄

end SheafPreDatum

end Langlands.DeligneFormalSpace
