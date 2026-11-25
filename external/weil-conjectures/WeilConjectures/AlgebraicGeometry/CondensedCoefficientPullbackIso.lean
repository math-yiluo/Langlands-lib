/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections

/-! Pullback transport for an ordinary condensed coefficient comparison.

Source: latest blueprint, lemma-fourier-transform-constant-sheaf proof, coefficient paragraph
(blueprint: lem-fd-unit-punctured-kernel-coefficient-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Pullback transports a coefficient comparison, for an arbitrary coefficient map. -/
private theorem coefficient_pullback_iso_of_isMonHom
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))
    (e : (Mod.extendScalars (coefficientMap a Y)).obj M ≅ N) :
    Nonempty ((Mod.extendScalars (coefficientMap a X)).obj
        ((CondensedRing.upperStar Λ f).obj M) ≅ (CondensedRing.upperStar Λ' f).obj N) :=
  ⟨(CondensedRing.pullIso a f).app M ≪≫ (CondensedRing.upperStar Λ' f).mapIso e⟩

/-- A coefficient comparison on the affine Artin–Schreier sheaf transports through ordinary
pullback along any morphism of schemes. -/
theorem condensed_coefficient_pullback_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))
    (e : (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y)).obj M ≅ N) :
    Nonempty ((Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).obj
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) f).obj M) ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj N) :=
  coefficient_pullback_iso_of_isMonHom _ f M N e

end AlgebraicGeometry.ProEtale
