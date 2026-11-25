/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffineFreeTerminalSectionsReconstruction
import WeilConjectures.AlgebraicGeometry.AffineResidueScalarTransport
import WeilConjectures.AlgebraicGeometry.Affine.AffineKFlatResiduePullbackModel
/-! # Derived residue model from affine free sections

Source: Stacks Project, Tags 064K, 06YB, 06YI, 06YJ and 0098.
(blueprint: lem-sc-affine-free-residue-sections-derived-model)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- A K-flat finite free section complex represents the derived residue pullback.
Source: Stacks Project, Tags 064K, 06YB, 06YI, 06YJ and 0098.
(blueprint: lem-sc-affine-free-residue-sections-derived-model)

Proof: Transport K across the over-site equivalence to modules on U.toScheme.
Finite free terms are quasi-coherent. The affine associated-sheaf counit identifies
this complex with the associated sheaf of its terminal-object section complex;
naturality gives compatibility with differentials. The section complex is finite free
termwise. Its K-flatness is supplied as a hypothesis. Apply the affine K-flat pullback
comparison to the residue point, which factors through U. Derived
pullback composition and exact open restriction identify the pullback of the
restricted representative with the pullback of E using he. The coefficient map
is the residue of the section germ, namely W.evaluation U w hwU. The associated
sheaf of its termwise scalar extension is therefore the stated representative.
This comparison is before homology and asserts no finiteness or dimension formula.
For rank zero and the zero complex the same counit and pullback comparisons apply. -/
theorem affineFree_residueSections_derivedModel
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W) (U : W.Opens) (hwU : w ∈ U)
    (hU : IsAffineOpen U) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (r : ℤ → ℕ)
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U) (ULift.{v} (Fin (r j)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤ ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let P : CochainComplex (ModuleCat.{v} Γ(W, U)) ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj K
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let L := tilde.functor (W.residueField w)
    letI : L.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    (HomologicalComplex.quasiIso (ModuleCat.{v} Γ(W, U)) (.up ℤ)).kFlat P →
    Nonempty ((derivedPullback (W.fromSpecResidueField w)).obj E ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj C)) := by
  classical
  dsimp only
  intro hP
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  let : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let P := (F.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨a⟩ := affineFree_terminalSections_reconstruction W U hU K r hrank
  obtain ⟨b⟩ := he
  have hmodel : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification W U hU).mapHomologicalComplex (.up ℤ)).obj P)) :=
    ⟨b ≪≫ DerivedCategory.Q.mapIso a.symm⟩
  obtain ⟨c⟩ := affine_kFlat_residuePullback_model W E U hU P hP hmodel ⟨w, hwU⟩
  obtain ⟨δ⟩ := affine_residue_scalar_transport W U hU ⟨w, hwU⟩
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  let : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let L := tilde.functor (W.residueField w)
  let : L.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let S := ModuleCat.extendScalars.{v, v, v}
    (algebraMap Γ(W, U) (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.ResidueField)
  let : S.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let e := asIso (U.ι.residueFieldMap ⟨w, hwU⟩) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap ⟨w, hwU⟩)).symm ≪≫
      Spec.residueFieldIso Γ(W, U) (hU.isoSpec.hom ⟨w, hwU⟩)
  let R := ModuleCat.restrictScalars.{v, v, v} e.hom.hom
  let d : (R.mapHomologicalComplex (.up ℤ)).obj
      ((S.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (T.mapHomologicalComplex (.up ℤ)).obj P :=
    (NatIso.mapHomologicalComplex δ (.up ℤ)).app P
  exact ⟨c ≪≫ DerivedCategory.Q.mapIso ((L.mapHomologicalComplex (.up ℤ)).mapIso d)⟩
end AlgebraicGeometry.Scheme
