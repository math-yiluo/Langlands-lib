/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkChainMapLift
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Descent of derived morphisms between open perfect stalks

Source: Stacks Project, Tags 09RE (affine proof), 0BC7 (2), 00CR, and 06Z0.
(blueprint: lem-sc-perfect-open-stalk-derived-hom-descent).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem perfect_stalk_isKProjective
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) :
    CochainComplex.IsKProjective
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P) := by
  let S := openModuleStalkFunctor X U ⟨x, hxU⟩
  let L := (S.mapHomologicalComplex (.up ℤ)).obj P
  have (n : ℤ) : Projective (L.X n) := by
    obtain ⟨m, i, r, hir⟩ := hP.2 n
    have : Projective (S.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))) :=
      openModuleStalk_free_projective X U ⟨x, hxU⟩ m
    exact (show Retract (L.X n) (S.obj (SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))) from
        ⟨S.map i, S.map r, by
          change S.map i ≫ S.map r = 𝟙 (S.obj (P.X n))
          rw [← S.map_comp, hir, S.map_id]⟩).projective
  obtain ⟨a, b, hab⟩ := hP.1
  have : CochainComplex.IsStrictlyLE L b := (CochainComplex.isStrictlyLE_iff L b).2
    (fun n hn ↦ S.map_isZero (hab n (Or.inr hn)))
  exact CochainComplex.isKProjective_of_projective L b

-- Comparing the localized stalk functors with the derived factorization unfolds nested functors.
set_option backward.isDefEq.respectTransparency false in
/-- A derived morphism between the open stalks of two strictly perfect complexes descends
as a derived morphism on a smaller affine open, in the coordinates of the canonical
restriction comparison. This does not choose a chain representative
and does not involve a comparison with any global complex.

Source: Stacks Project, Tag 09RE affine proof; Tag 0BC7 (2), with Tags 00CR and 06Z0.
(blueprint: lem-sc-perfect-open-stalk-derived-hom-descent).

Proof: On U, finite-free retracts are quasi-coherent. Global sections identify P and Q
with bounded complexes of finite projective modules over A = Gamma(X,U). The stalk at x
is scalar extension to A localized at the prime corresponding to x. Present this ring
as the filtered colimit of A_f for f outside that prime (00CR). The affine perfect Hom
comparison is surjective by 09RE, affine proof, or 0BC7 (2). Thus the given arrow is
represented in the derived category of A_f for one f. The basic open D(f) is affine,
contains x, and lies in U. The affine derived equivalence (06Z0) carries this arrow to g
between the restrictions of P and Q. Restriction does not change the stalk at x: the
canonical comparison `openModuleStalkRestrictionComparison` gives cP and cQ.
Naturality of scalar extension and the localization factorization identifies
the derived stalk image of g with the transported original arrow, giving the equation.
Only Hom surjectivity is used; neither inverse descent nor Hom injectivity is needed.
The assumptions exclude an empty U, while zero complexes and zero ranks are allowed:
their Hom groups are zero and the zero arrow descends on U itself. Neither affineness
of U nor perfectness of Q is used. -/
theorem exists_affine_perfect_open_stalk_derived_hom_descent
    (X : Scheme.{u})
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (U : X.Opens) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) :
    let SU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hxU⟩
    letI : SU.PreservesZeroMorphisms :=
      AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hxU⟩
    ∀ t : DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj Q),
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      letI : S.Additive :=
        AlgebraicGeometry.openModuleStalkFunctor_additive X V ⟨x, hxV⟩
      letI : PreservesFiniteLimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteLimits X V ⟨x, hxV⟩
      letI : PreservesFiniteColimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteColimits X V ⟨x, hxV⟩
      let c : T ⋙ S.mapHomologicalComplex (.up ℤ) ≅ SU.mapHomologicalComplex (.up ℤ) :=
        Functor.mapHomologicalComplexCompIso
          (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      let cP := DerivedCategory.Q.mapIso (c.app P)
      let cQ := DerivedCategory.Q.mapIso (c.app Q)
      ∃ g : DerivedCategory.Q.obj (T.obj P) ⟶ DerivedCategory.Q.obj (T.obj Q),
        (S.mapDerivedCategoryFactors.app (T.obj P)).inv ≫
          S.mapDerivedCategory.map g ≫ (S.mapDerivedCategoryFactors.app (T.obj Q)).hom =
            cP.hom ≫ t ≫ cQ.inv := by
  dsimp only
  intro t
  let SU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hxU⟩
  have : SU.PreservesZeroMorphisms :=
    openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hxU⟩
  let TU := SU.mapHomologicalComplex (.up ℤ)
  have : CochainComplex.IsKProjective (TU.obj P) :=
    perfect_stalk_isKProjective X U x hxU P hP
  obtain ⟨f, hf'⟩ := CochainComplex.IsKProjective.exists_Q_map_eq (TU.obj P) (TU.obj Q) t
  obtain ⟨V, hxV, hV, hVU, g, hg⟩ :=
    exists_affine_perfect_open_stalk_chainMap_lift X U x hxU P Q hP f
  let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
  let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
      ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
  have : S.PreservesZeroMorphisms :=
    openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
  have : S.Additive := openModuleStalkFunctor_additive X V ⟨x, hxV⟩
  have : PreservesFiniteLimits S :=
    openModuleStalkFunctor_preservesFiniteLimits X V ⟨x, hxV⟩
  have : PreservesFiniteColimits S :=
    openModuleStalkFunctor_preservesFiniteColimits X V ⟨x, hxV⟩
  refine ⟨V, hxV, hV, hVU, DerivedCategory.Q.map g, ?_⟩
  have hn := S.mapDerivedCategoryFactors.hom.naturality g
  change S.mapDerivedCategory.map (DerivedCategory.Q.map g) ≫
      (S.mapDerivedCategoryFactors.app (R.obj Q)).hom =
    (S.mapDerivedCategoryFactors.app (R.obj P)).hom ≫
      DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map g) at hn
  change (S.mapDerivedCategoryFactors.app (R.obj P)).inv ≫
    S.mapDerivedCategory.map (DerivedCategory.Q.map g) ≫
      (S.mapDerivedCategoryFactors.app (R.obj Q)).hom = _
  rw [hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [hg, Functor.map_comp, Functor.map_comp, hf']
  rfl

end AlgebraicGeometry.Scheme
