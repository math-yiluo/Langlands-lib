/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Affine.AffineFreeResidueSectionsDerivedModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Residue cohomology of an affine bounded free representative

Source: Stacks Project, Tags 0BCD, 064K, 06YB and 0098.
(blueprint: lem-sc-affine-free-residue-sections-cohomology)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Residue extension of the section complex computes the derived residue fibre
cohomology by a linear equivalence.
Source: Stacks Project, Tags 0BCD (minimal free models), 064K (bounded free
K-flatness), 06YB (stalkwise K-flatness), 06YI and 06YJ (derived pullback),
and 0098 (stalks of pullback).
(blueprint: lem-sc-affine-free-residue-sections-cohomology)

Proof: The localized-site equivalence transports K to a bounded finite free
complex on U. On an affine scheme, finite free sheaves are the sheaves associated
to their finite free section modules. Evaluation of the given term isomorphisms
therefore gives section modules of ranks r j. Tensor these free modules along
W.evaluation U w hwU; their residue extensions are finite dimensional of the
same ranks, including rank zero. The bounded free complex is K-flat, so its
termwise pullback to the residue-field point represents the derived pullback
of Q(K). The residue point factors through U. Compatibility of derived pullback
with this factorization and exact open restriction identifies this derived
object with the derived fibre of E, using he. On the one-point residue spectrum,
sections are exact, and GammaSpecIso transports scalars to W.residueField w.
The affine module/sheaf tensor comparison identifies these sections termwise
with the explicitly displayed scalar extension of the section complex, and
naturality makes this a chain comparison. Homology thus has a linear equivalence
with derivedFiberCohomology W E j w, as asserted.
No vanishing of any differential or choice of a section frame is used. -/
theorem affineFree_residueSections_cohomologyLinearEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (r : ℤ → ℕ)
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (r j)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _
      (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∀ j : ℤ, Nonempty (derivedFiberCohomology W E j w ≃ₗ[W.residueField w]
      C.homology j) := by
  dsimp only
  classical
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let P₀ : CochainComplex (ModuleCat.{v} Γ(W, U)) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj K
  have hP₀ : (HomologicalComplex.quasiIso (ModuleCat.{v} Γ(W, U)) (.up ℤ)).kFlat P₀ := by
    obtain ⟨a, b, hbound⟩ := hb
    have : P₀.IsStrictlyLE b := (P₀.isStrictlyLE_iff b).2
      (fun j hj ↦ F.map_isZero (hbound j (Or.inr hj)))
    have hflat (j : ℤ) : ObjectProperty.flat (P₀.X j) := by
      let e : (P₀.X j) ≃ₗ[Γ(W, U)] (ULift.{v} (Fin (r j)) → Γ(W, U)) :=
        SheafOfModules.sectionsLinearEquivOfIsoFree (hrank j).some
          (.op (Over.mk (𝟙 U)))
      have : Module.Free Γ(W, U) (P₀.X j) := Module.Free.of_equiv e.symm
      exact (ModuleCat.flat_iff_flat (P₀.X j)).2 Module.Flat.of_free
    have (X : ModuleCat.{v} Γ(W, U)) : PreservesColimitsOfShape ℤ
        ((MonoidalCategory.curriedTensor (ModuleCat.{v} Γ(W, U))).flip.obj X) :=
      inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight X))
    have : HasExactColimitsOfShape ℤ (ModuleCat.{v} Γ(W, U)) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{v} Γ(W, U))
        (AsSmall.equiv (C := ℤ)).symm
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat P₀ b hflat
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  have : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let C := ((F ⋙ T).mapHomologicalComplex (.up ℤ)).obj K
  let L := tilde.functor (W.residueField w)
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let P := (L.mapHomologicalComplex (.up ℤ)).obj C
  let Y := Spec (W.residueField w)
  let B := SheafOfModules.{v} (moduleRings Y.toRingedSpace)
  let Γ := moduleSpecΓFunctor (R := W.residueField w)
  have : Γ.IsEquivalence := isEquivalence_moduleSpecΓFunctor (Field.toIsField _)
  have : Γ.PreservesHomology := inferInstance
  obtain ⟨e⟩ := affineFree_residueSections_derivedModel W E w U hwU hU K r hrank he hP₀
  intro j
  let h : derivedFiberCohomology W E j w ≅ Γ.obj (P.homology j) :=
    Γ.mapIso ((DerivedCategory.homologyFunctor B j).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors B j).app P)
  let hΓ : Γ.obj (P.homology j) ≅
      ((Γ.mapHomologicalComplex (.up ℤ)).obj P).homology j :=
    ((P.sc j).mapHomologyIso Γ).symm
  let t : ((Γ.mapHomologicalComplex (.up ℤ)).obj P) ≅ C :=
    (NatIso.mapHomologicalComplex tilde.toTildeΓNatIso.symm (.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{v} (W.residueField w)) (.up ℤ)).app C
  exact ⟨(h ≪≫ hΓ ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w))
      (.up ℤ) j).mapIso t).toLinearEquiv⟩

end AlgebraicGeometry.Scheme
