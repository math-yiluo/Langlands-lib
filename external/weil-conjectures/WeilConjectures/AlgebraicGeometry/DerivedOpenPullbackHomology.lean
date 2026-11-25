/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Cohomology of derived pullback along an open inclusion

Source: the exact-open-restriction step of blueprint lem-pc-derived-single-open-locus.
(blueprint: lem-pc-derived-open-pullback-homology).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Derived open pullback cohomology is ordinary restriction of cohomology.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--3, cohomology-sheaf gluing
paragraph; step 3 of lem-pc-derived-single-open-locus, exactness of open restriction.
(blueprint: lem-pc-derived-open-pullback-homology).

Proof: tensor pullback along W.ι is naturally isomorphic to ordinary module
pullback by uniqueness of left adjoints to pushforward. For an open immersion,
ordinary pullback is naturally isomorphic to restrictFunctor W.ι and is exact.
Represent E by a cochain complex G and take a K-flat resolution P → G. The
specification of the chosen derivedPullback gives an invertible derived counit
at P. Compose it with the localization and homotopy-quotient comparisons to
identify the derived pullback of E with localized termwise tensor pullback of P.
Exactness gives the homology comparison for this termwise functor. The localized
resolution identifies H^n(P) with H^n(E). Finally the ordinary pullback/restriction
comparison identifies the resulting sheaf with restriction of H^n(E).
No boundedness, connectivity or quasi-coherence is required, and the argument
works for every integer n and for the empty open. -/
theorem nonempty_homology_derivedOpenPullback_iso_restrict
    {T : Scheme.{u}} (W : T.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory T) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) n).obj
        ((AlgebraicGeometry.derivedPullback W.ι).obj E) ≅
      (restrictFunctor W.ι).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E)) := by
  classical
  let A := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec W.ι
  have h : F = tensorPullback W.ι := CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  let η : tensorPullback W.ι ≅ restrictFunctor W.ι :=
    (nonempty_tensorPullbackAdjunction W.ι).some.leftAdjointUniq
      (pullbackPushforwardAdjunction W.ι) ≪≫ (restrictFunctorIsoPullback W.ι).symm
  have : PreservesFiniteLimits (tensorPullback W.ι) :=
    preservesFiniteLimits_of_natIso η.symm
  have : PreservesFiniteColimits (tensorPullback W.ι) :=
    preservesFiniteColimits_of_natIso η.symm
  let G := DerivedCategory.Q.objPreimage E
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := T.sheaf) G
  have : QuasiIso s := hs
  have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := hK P hP
  let e : (AlgebraicGeometry.derivedPullback W.ι).obj E ≅
      DerivedCategory.Q.obj ((tensorPullback W.ι).mapHomologicalComplex (.up ℤ) |>.obj P) :=
    (AlgebraicGeometry.derivedPullback W.ι).mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      ((AlgebraicGeometry.derivedPullback W.ι).mapIso (asIso (DerivedCategory.Q.map s))).symm ≪≫
      (AlgebraicGeometry.derivedPullback W.ι).mapIso
        ((DerivedCategory.quotientCompQhIso A).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((tensorPullback W.ι).mapHomotopyCategoryFactors
        (.up ℤ) |>.app P) ≪≫
      (DerivedCategory.quotientCompQhIso B).app _
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  exact ⟨(DerivedCategory.homologyFunctor B n).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _ ≪≫
    ((tensorPullback W.ι).mapHomologicalComplexHomologyIso (.up ℤ) n).app P ≪≫
    (tensorPullback W.ι).mapIso
      ((DerivedCategory.homologyFunctorFactors A n).symm.app P ≪≫
        (DerivedCategory.homologyFunctor A n).mapIso eP) ≪≫ η.app _⟩

end AlgebraicGeometry.Scheme.Modules
