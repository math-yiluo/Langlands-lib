/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizedMixedDerivedPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel

/-! # Termwise finite-free models under localized derived pullback

## References

* Stacks Project, Tags 06YD, 06YJ and 08DW
* Stacks Project, Tag 03ER
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wT wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Finite free terms are flat. -/
private theorem finiteFreeTerms_are_flat
    {T : Scheme.{u}}
    (P : CochainComplex (SheafOfModules.{u} (moduleRings T.toRingedSpace)) ℤ)
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := moduleRings T.toRingedSpace) (ULift.{u} (Fin r)))) :
    ∀ i : ℤ, SheafOfModules.IsFlat (P.X i) := by
  let := SheafOfModules.monoidalCategory T.sheaf
  intro i
  obtain ⟨r, ⟨e⟩⟩ := hfree i
  have hu : SheafOfModules.IsFlat (SheafOfModules.unit (moduleRings T.toRingedSpace)) := by
    change exactFunctor _ _
      (MonoidalCategory.tensorRight (SheafOfModules.unit (moduleRings T.toRingedSpace)))
    exact (exactFunctor _ _).prop_of_iso (MonoidalCategory.rightUnitorNatIso _).symm
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)
  have hf := SheafOfModules.isFlat_coproduct T.sheaf
    (fun _ : ULift.{u} (Fin r) ↦ SheafOfModules.unit (moduleRings T.toRingedSpace))
    (fun _ ↦ hu)
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.tensoringRight
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))).mapIso e.symm) hf

private theorem tensor_derived_model {X Y : Scheme.{u}} (g : X ⟶ Y)
    [(Scheme.Modules.tensorPullback g).Additive]
    [HasDerivedCategory.{wT} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wT} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) P) :
    Nonempty ((derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hderived, htri, hε⟩ :=
    (derivedPullback_spec g)
  let e : F ≅ Scheme.Modules.tensorPullback g := NatIso.ofComponents
    (fun M ↦ eqToIso (hF M)) (by
      intro M N a
      simp only [eqToIso.hom, hFmap, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id]
      rfl)
  have := hε P hP
  exact ⟨(derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso _).symm.app P) ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (.up ℤ)).app P)⟩

/-- Compute the localized derived pullback of an exact open restriction termwise. -/
theorem localizedMixedDerivedPullback_finiteFree_model
    {S T : Scheme.{u}}
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (U : S.Opens) (V : U.toScheme.Opens) (W : T.Opens)
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (g : V.toScheme ⟶ W.toScheme)
    (L : T.Modules ⥤ SheafOfModules.{u}
      ((moduleRings U.toScheme.toRingedSpace).over V))
    (eL : Nonempty (L ≅ Scheme.Modules.tensorPullback (g ≫ W.ι) ⋙
      (Scheme.Modules.overEquiv V).inverse)) [L.Additive]
    (P : CochainComplex T.Modules ℤ)
    (hP : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := moduleRings T.toRingedSpace) (ULift.{u} (Fin r))))
 :
    Nonempty ((localizedMixedDerivedPullback U V W g).obj
      ((schemeOpenRestriction T W).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  by
    classical
    let R := schemeOpenRestriction T W
    let E : SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) ⥤
        SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V) :=
      (Scheme.Modules.overEquiv V).inverse
    let : E.Additive := by
      change (Scheme.Modules.overEquiv V).inverse.Additive
      exact Functor.additive_of_preserves_binary_products _
    let oldW : HasDerivedCategory.{wW}
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) := inferInstance
    let QhW := DerivedCategory.Qh.{wW}
      (C := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
    let K := (R.mapHomologicalComplex (.up ℤ)).obj P
    let a := R.mapDerivedCategoryFactors.{wT, wW}.app P
    let dW := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
    let dV := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    let C := (Localization.uniq QhW (@DerivedCategory.Qh _ _ _ dW)
      (HomotopyCategory.quasiIso _ (.up ℤ))).functor
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) (.up ℤ)
    let b := C.mapIso ((@DerivedCategory.quotientCompQhIso _ _ _ oldW).symm.app K)
    let c := (Localization.compUniqFunctor QhW (@DerivedCategory.Qh _ _ _ dW)
      (HomotopyCategory.quasiIso _ (.up ℤ))).app (q.obj K)
    let := dW
    let := dV
    let b' := b ≪≫ c ≪≫ (DerivedCategory.quotientCompQhIso _).app K
    obtain ⟨adjg⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
    let : (Scheme.Modules.tensorPullback g).Additive := adjg.left_adjoint_additive
    have hPK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
      T.toRingedSpace P hP (finiteFreeTerms_are_flat P hfree)
    have hK := openRestriction_isKFlat T W P hPK
    obtain ⟨e⟩ := tensor_derived_model g K hK
    let D := @derivedPullback _ _ g dW dV
    let ED := E.mapDerivedCategory
    let left := (C ⋙ D ⋙ ED).mapIso a ≪≫
      ED.mapIso (D.mapIso b' ≪≫ e) ≪≫ E.mapDerivedCategoryFactors.app _
    obtain ⟨adjw⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction W.ι
    let rw : R ≅ Scheme.Modules.tensorPullback W.ι :=
      Scheme.Modules.overFunctorEquiv W ≪≫
        (Scheme.Modules.restrictAdjunction W.ι).leftAdjointUniq adjw
    obtain ⟨comp⟩ := Scheme.Modules.nonempty_tensorPullbackComp g W.ι
    obtain ⟨eL⟩ := eL
    let t : R ⋙ Scheme.Modules.tensorPullback g ⋙ E ≅ L :=
      Functor.isoWhiskerRight rw _ ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight comp.symm E ≪≫ eL.symm
    exact ⟨left ≪≫ DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex t (.up ℤ)).app P)⟩

end AlgebraicGeometry
