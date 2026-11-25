/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkChainMapLift
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread

/-! # Detecting a quasi-isomorphism of strictly perfect complexes near a point

Source: Stacks Project, Tags 09RE, 0BC7 (2), and 00CR.
(blueprint: lem-sc-perfect-stalk-quasi-iso-detection).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

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

/-- A fixed chain map of strictly perfect complexes on an open which is a
quasi-isomorphism at one stalk becomes a quasi-isomorphism on a smaller affine open.

Source: Stacks Project, Tags 09RE, 0BC7 (2), and 00CR.
(blueprint: lem-sc-perfect-stalk-quasi-iso-detection).

Proof: Taking stalks carries each finite-free retraction to a retraction of a
projective stalk module. The support bounds are preserved, so both stalk complexes
are K-projective. Mathlib's quasi-isomorphism criterion gives a homotopy equivalence
whose forward map is the specified stalk map of f. Lift its inverse as a chain map
on an affine neighbourhood V. Naturality of the restriction/stalk comparison
transports both inverse homotopies to the composites of the restricted f and this
lift. Spread these two specified homotopies after shrinking again. They give a
homotopy equivalence whose forward map is exactly the restriction of f to W;
its forward map is a quasi-isomorphism. This avoids derived sheaf equivalences,
cones and a derived Hom colimit diagram. Zero complexes, disjoint bounds and
non-Noetherian rings are handled by the same finite-component descent. -/
theorem exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q) (f : P ⟶ Q)
    (hf : QuasiIso (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex
      (.up ℤ)).map f)) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      QuasiIso (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)).map f) := by
  let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
  have : CochainComplex.IsKProjective (T.obj P) :=
    perfect_stalk_isKProjective X U x hxU P hP
  have : CochainComplex.IsKProjective (T.obj Q) :=
    perfect_stalk_isKProjective X U x hxU Q hQ
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff (T.map f)).1 hf
  obtain ⟨V, hxV, -, hVU, g, hg⟩ :=
    exists_affine_perfect_open_stalk_chainMap_lift X U x hxU Q P hQ e.inv
  let c := Functor.mapHomologicalComplexCompIso
    (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
  let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
  let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
  have hfg : Nonempty (Homotopy (S.map (R.map f ≫ g)) (𝟙 _)) := by
    have h := (e.homotopyHomInvId.compLeft (c.app P).hom).compRight (c.app P).inv
    rw [he] at h
    have hc := c.hom.naturality f
    change S.map (R.map f) ≫ (c.app Q).hom = (c.app P).hom ≫ T.map f at hc
    rw [Functor.map_comp, hg, ← Category.assoc, hc]
    refine ⟨?_⟩
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    convert! h using 1
  have hgf : Nonempty (Homotopy (S.map (g ≫ R.map f)) (𝟙 _)) := by
    have h := (e.homotopyInvHomId.compLeft (c.app Q).hom).compRight (c.app Q).inv
    rw [he] at h
    have hc := c.inv.naturality f
    change T.map f ≫ (c.app Q).inv = (c.app P).inv ≫ S.map (R.map f) at hc
    rw [Functor.map_comp, hg, Category.assoc, Category.assoc, ← hc]
    refine ⟨?_⟩
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    convert! h using 1
  obtain ⟨W, hxW, hW, hWU, gW, ⟨hfgW⟩, ⟨hgfW⟩⟩ :=
    exists_affine_perfect_open_stalk_inverse_homotopies_spread
      X U x P Q hP hQ f V hxV hVU g hfg hgf
  exact ⟨W, hxW, hW, hWU,
    (show HomotopyEquiv _ _ from
      ⟨_, gW, hfgW, hgfW⟩).quasiIso_hom⟩

end
end AlgebraicGeometry.Scheme
