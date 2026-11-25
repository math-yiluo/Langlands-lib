/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Left-derived counits at flat single complexes -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Every left-derived counit for tensor pullback is invertible at a flat module
placed in degree zero.
Source: Stacks Project, Tags 06YD and 06YJ.
(blueprint: lem-pc-flat-single-derived-counit).

Proof: The single complex on G is bounded above by zero. Its term in degree zero
is isomorphic to G and is flat; the other terms are zero, hence flat. Apply
flatComplexDerivedPullback to obtain an invertible counit on this complex.
The specified object and map equalities identify its functor with tensorPullback.
The universal property of left-derived functors supplies an invertible natural
comparison between this counit and the given one. Its component at the single
complex expresses the given counit as a composite of isomorphisms. This argument
uses no nonzero point or term and includes the zero module and empty schemes. -/
theorem isIso_flat_single_derived_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules) (hflat : SheafOfModules.IsFlat G)
    (ε : DerivedCategory.Qh ⋙ derivedPullback a ⟶
      (Scheme.Modules.tensorPullback a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hε : (derivedPullback a).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    IsIso (ε.app ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (0 : ℤ)).obj G)) := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let K := (CochainComplex.singleFunctor A 0).obj G
  let := SheafOfModules.monoidalCategory Y.sheaf
  obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := hpreadd
  have hbounded : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (K.X q) := by
    refine ⟨0, fun q hq ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hterms : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q) := by
    intro q
    by_cases hq : q = 0
    · subst q
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso e.symm) hflat
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)).2
  obtain ⟨F, hF, hFmap, hFadd, ε₀, hε₀, ⟨e, he⟩⟩ :=
    flatComplexDerivedPullback a K hbounded hterms
  have h : F = Scheme.Modules.tensorPullback a :=
    CategoryTheory.Functor.ext hF (fun M N f ↦ hFmap f)
  subst F
  have : (derivedPullback a).IsLeftDerivedFunctor ε₀
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hε₀
  have : (derivedPullback a).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hε
  have hi : IsIso (ε₀.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)) := by
    rw [← he]
    infer_instance
  have hfac := CategoryTheory.Functor.leftDerived_fac_app
    (derivedPullback a) ε₀ (HomotopyCategory.quasiIso A (.up ℤ))
    (derivedPullback a) ε ((HomotopyCategory.quotient A (.up ℤ)).obj K)
  have hlift : IsIso ((derivedPullback a).leftDerivedLift ε₀
      (HomotopyCategory.quasiIso A (.up ℤ)) (derivedPullback a) ε) :=
    (CategoryTheory.Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (derivedPullback a) ε₀ (HomotopyCategory.quasiIso A (.up ℤ))
      (derivedPullback a) ε).mp hε
  change IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj K))
  rw [← hfac]
  infer_instance

end AlgebraicGeometry
