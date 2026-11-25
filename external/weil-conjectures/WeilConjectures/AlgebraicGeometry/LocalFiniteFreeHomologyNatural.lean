/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.AlgebraicGeometry.HomComplexRestrictSchemeNatural
import WeilConjectures.Algebra.Homology.StrictlyPerfectHomQuasiIso
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Coefficient naturality for a local finite free resolution

Source: Stacks Project, Tags 08DL and 08DM. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Scheme.Modules.overEquiv Scheme.Modules.restrictFunctor
  homComplexFunctor derivedInternalHom HomologicalComplex.homologyFunctor
  DerivedCategory.homologyFunctor Functor.mapHomologicalComplex


/-- A bounded finite free resolution on an open computes restricted Ext
naturally in every coefficient sheaf.
Source: Stacks Project, Tag 08DL (restriction of derived internal Hom), and
Tag 08DM (finite locally free computation of derived internal Hom).
(blueprint: lem-sc-local-finite-free-homology-natural).

Proof: Use the functorial K-injective resolution of each coefficient single
complex. The localization comparison for derived internal Hom is natural in
the coefficient, as is its restriction to the open. Restriction is exact and
preserves K-injectives. Transport from the over site to the open subscheme.
Precomposition with the augmentation is a quasi-isomorphism on Hom into these
K-injectives. Since E is bounded with finite free terms, internal Hom from E
preserves acyclicity: finite free internal Hom is exact and only finitely many
source terms contribute to each total degree. The cone of the coefficient
resolution is acyclic, so postcomposition with that resolution is also a
quasi-isomorphism on Hom out of E. These are natural transformations whose
components are quasi-isomorphisms. Take homology, invert their componentwise
isomorphisms, and compose with the exact restriction homology comparison.
This gives a natural isomorphism of coefficient functors. All computations use
complexes and homology in the ambient supplied derived universe; no derived
category on the open in that universe is required. The zero resolution and
empty open are included. -/
theorem local_finite_free_homology_natural
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (B : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj B)) [QuasiIso ε] (q : ℤ) :
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    Nonempty (S ⋙ (Functor.curry.obj H).obj (op (S.obj B)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q ⋙
        Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙
        CochainComplex.singleFunctor U.toScheme.Modules 0 ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj (op E) ⋙
        HomologicalComplex.homologyFunctor U.toScheme.Modules (ComplexShape.up ℤ) q) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let O := SheafOfModules.overFunctor.{u} Y.ringCatSheaf U
  let T := (Scheme.Modules.overEquiv U).functor
  let : PreservesFiniteLimits O := moduleOverFunctor_limits Y.toRingedSpace U
  let : PreservesFiniteColimits O := moduleOverFunctor_colimits Y.toRingedSpace U
  let hOTl : PreservesFiniteLimits (O ⋙ T) := comp_preservesFiniteLimits O T
  let hOTc : PreservesFiniteColimits (O ⋙ T) := comp_preservesFiniteColimits O T
  let R : A ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let eR : O ⋙ T ≅ R := Scheme.Modules.overFunctorEquiv U
  let : PreservesFiniteLimits R := @preservesFiniteLimits_of_natIso _ _ _ _ (O ⋙ T) R eR hOTl
  let : PreservesFiniteColimits R := @preservesFiniteColimits_of_natIso _ _ _ _ (O ⋙ T) R eR hOTc
  let hRadd : R.Additive := R.additive_of_preserves_binary_products
  let Rc : CochainComplex A ℤ ⥤ CochainComplex U.toScheme.Modules ℤ :=
    R.mapHomologicalComplex (.up ℤ)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let cs := CochainComplex.singleFunctor A 0
  let S := DerivedCategory.singleFunctor A 0
  let L := cs.obj B
  let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  let HL := (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op L)
  let J := cs ⋙ I
  let HY := DerivedCategory.homologyFunctor A q
  let CU := HomologicalComplex.homologyFunctor U.toScheme.Modules (.up ℤ) q
  obtain ⟨e⟩ := derivedInternalHom_comparison
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  let D := S ⋙ (Functor.curry.obj H).obj (op (S.obj B))
  let eD₀ : (cs ⋙ DerivedCategory.Q) ⋙
      (Functor.curry.obj H).obj (op (DerivedCategory.Q.obj L)) ≅
      J ⋙ HL ⋙ DerivedCategory.Q := NatIso.ofComponents
    (fun C ↦ e.app (op L, cs.obj C)) (by
      intro C C' f
      have hn := e.hom.naturality (Prod.mkHom (𝟙 (op L)) (cs.map f))
      simpa [J, HL, Functor.comp_map, Functor.curry_obj_obj_map,
        Functor.uncurry, Functor.prod] using hn)
  let eD : D ≅ J ⋙ HL ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0)
      ((Functor.curry.obj H).obj (op (S.obj B))) ≪≫ eD₀
  obtain ⟨eC⟩ := homComplex_restrict_scheme_natural U L
  let eH : D ⋙ HY ⋙ R ≅ J ⋙ Rc ⋙
      (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj (op (Rc.obj L)) ⋙
      CU :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight eD HY) R ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (J ⋙ HL)
        (DerivedCategory.homologyFunctorFactors A q)) R ≪≫
      Functor.isoWhiskerLeft (J ⋙ HL) (R.mapHomologicalComplexHomologyIso (.up ℤ) q).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft J eC) CU
  have : R.PreservesKInjectiveComplexes :=
    (openImmersion_restriction_derived_properties U.ι).2
  let eSingle := HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0
  let t : E ⟶ Rc.obj L := ε ≫ (eSingle.app B).inv
  have : QuasiIso t := by
    dsimp only [t]
    exact quasiIso_comp ε (eSingle.app B).inv
  let HE := (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj (op E)
  let α := Functor.whiskerLeft (J ⋙ Rc)
    ((homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).map t.op)
  let αq := Functor.whiskerRight α CU
  have : IsIso αq := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro C
    have : CochainComplex.IsKInjective (J.obj C) :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A (cs.obj C)
    have : CochainComplex.IsKInjective (Rc.obj (J.obj C)) :=
      Functor.PreservesKInjectiveComplexes.isKInjective_map (F := R) (J.obj C)
    have : QuasiIso (α.app C) := by
      simpa [α] using quasiIso_homComplex_map (𝟙 (Rc.obj (J.obj C))) t
    change IsIso (CU.map (α.app C))
    unfold CU HomologicalComplex.homologyFunctor
    infer_instance
  let γ := Functor.whiskerRight (Functor.whiskerLeft cs η) Rc
  let β := Functor.whiskerRight γ (HE ⋙ CU)
  have : IsIso β := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro C
    have : QuasiIso (η.app (cs.obj C)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A (cs.obj C)).2
    have : QuasiIso (γ.app C) := by
      dsimp [γ]
      infer_instance
    have : QuasiIso (HE.map (γ.app C)) :=
      quasiIso_homComplex_map_of_bounded_finiteFree U.toScheme.toRingedSpace
        E hbounded hbelow hfree (γ.app C)
    change IsIso (CU.map (HE.map (γ.app C)))
    unfold CU HomologicalComplex.homologyFunctor
    infer_instance
  exact ⟨eH ≪≫ asIso αq ≪≫ (asIso β).symm ≪≫
    Functor.isoWhiskerRight eSingle (HE ⋙ CU)⟩

end AlgebraicGeometry
