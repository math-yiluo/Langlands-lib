/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.BoundedFreeStalkComplexLift
import WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedIsoSpread

/-! # Spreading a prescribed bounded free stalk model

Source: Stacks Project, Tag 0BCD, spreading paragraph, with Tags 0BC7 and 09RE.
(blueprint: lem-sc-bounded-free-stalk-model-spread).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A given bounded finite-free stalk model of a locally strictly perfect object spreads
with its specified ranks to an affine neighbourhood. No residue rank computation is made.

Source: Stacks Project, Tag 0BCD, spreading paragraph; Tags 00CR, 0BC7 and 09RE.
(blueprint: lem-sc-bounded-free-stalk-model-spread).

Proof:
1. Lift F as a complex by exists_boundedFree_stalk_complex_lift, giving an affine
   neighbourhood U and a bounded global auxiliary complex H. On U its terms are
   free of ranks d i, and the stalk complex of H is isomorphic to F. This uses finite
   differential matrices directly, retaining the specified bases and ranks.
2. The bounds of H and its termwise free isomorphisms make its restriction to U
   strictly perfect: each free isomorphism supplies the required retraction. Compose
   eF inversely with the derived image of the stalk complex isomorphism. This identifies
   the derived stalks of G and H. Transport hlocal along eG to get a local strictly
   perfect representative for Q(G), then use
   exists_affine_restriction_iso_of_perfect_stalk_iso to extend the derived comparison
   to an affine W containing x inside U.
3. Set K equal to the termwise restriction of H to W. Restriction preserves zero objects,
   hence the bounds. The restriction-composition isomorphism identifies each K.X i
   with the restriction from U of H.X i. Apply that restriction to its given free
   isomorphism and use mapFreeIso with overMapUnitIso to identify its image with the
   rank-d i free sheaf on W. Finally compose the derived restriction of eG inverse,
   the exact restriction comparison for Q, and the derived isomorphism on W.
The two intermediate theorems separate construction of a complex from comparison of
existing perfect models. Zero ranks, empty degree intervals and nonseparated schemes
are allowed. No finite-projective standard free cover or residue rank computation is used.
-/
theorem spread_boundedFree_stalkModel
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i))
    (hfree : ∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x))))
    (eF : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj K) := by
  obtain ⟨U, hxU, _hU, H, hHbounded, hHfree, ⟨eH⟩⟩ :=
    exists_boundedFree_stalk_complex_lift X x d F hbounded hfree
  let R := moduleRings X.toRingedSpace
  let A := SheafOfModules.overFunctor.{u} R U
  have hHstrict : IsStrictlyPerfect X U
      ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj H) := by
    constructor
    · obtain ⟨a, b, hab⟩ := hHbounded
      exact ⟨a, b, fun i hi => A.map_isZero (hab i hi)⟩
    · intro i
      obtain ⟨e⟩ := hHfree i
      exact ⟨d i, e.hom, e.inv, e.hom_inv_id⟩
  have hGlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u} R V).mapDerivedCategory.obj
          (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P) := by
    obtain ⟨V, hxV, P, hP, ⟨eP⟩⟩ := hlocal
    exact ⟨V, hxV, P, hP,
      ⟨(SheafOfModules.overFunctor.{u} R V).mapDerivedCategory.mapIso eG ≪≫ eP⟩⟩
  have eGH : DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G) ≅ DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H) :=
    eF.symm ≪≫ DerivedCategory.Q.mapIso eH
  obtain ⟨W, hxW, hW, hWU, ⟨eW⟩⟩ :=
    exists_affine_restriction_iso_of_perfect_stalk_iso X x G H hGlocal U hxU hHstrict eGH
  let B := SheafOfModules.overFunctor.{u} R W
  let T := SheafOfModules.overMap.{u} R (homOfLE hWU : W ⟶ U)
  let K := (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj H
  refine ⟨W, hxW, hW, K, ?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hHbounded
    exact ⟨a, b, fun i hi => B.map_isZero (hab i hi)⟩
  · intro i
    obtain ⟨e⟩ := hHfree i
    let c := (SheafOfModules.overFunctorMap.{u} R (homOfLE hWU : W ⟶ U)).app (H.X i)
    exact ⟨c.symm ≪≫ T.mapIso e ≪≫
      (SheafOfModules.mapFreeIso T (ULift.{u} (Fin (d i)))
        (SheafOfModules.overMapUnitIso (R := R) (homOfLE hWU : W ⟶ U)).symm).symm⟩
  · exact ⟨B.mapDerivedCategory.mapIso eG.symm ≪≫
      B.mapDerivedCategoryFactors.app G ≪≫ eW⟩

end
end AlgebraicGeometry.Scheme
