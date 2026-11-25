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
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation

/-! # Lifting a perfect stalk chain map

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-open-stalk-chain-map-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- An arbitrary chain map of perfect stalk complexes lifts on an affine neighbourhood,
in the coordinates of the canonical restriction comparison.
Source: Stacks Project, Tag 09RE, affine proof's finite-presentation calculation;
Tag 0BC7 (2), chain representatives, and Tag 00CR.
(blueprint: lem-sc-perfect-open-stalk-chain-map-lift).

Proof: Extend the degreewise stalk maps by
`exists_affine_perfect_open_stalk_degreewise_lift`. The given chain map makes
their stalks commute with the differentials, by conjugating with the comparison
isomorphism. Apply `exists_affine_perfect_open_stalk_degreewise_shrink`, assemble
its components with `CochainComplex.ofHom`, and cancel the intermediate
comparison isomorphisms degreewise. The two component lemmas implement the
finite-presentation argument: only finitely many components and differential
defects have nonzero source, their germs have common representatives, and the
zero defect germs vanish on a common smaller neighbourhood. Only strict
perfectness of P is needed. No inverse or quasi-isomorphism condition is required.
Empty source support and zero ranks use zero maps. -/
theorem exists_affine_perfect_open_stalk_chainMap_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (t : ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      let e : R ⋙ S ≅ T := Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      ∃ g : R.obj P ⟶ R.obj Q,
        S.map g = (e.app P).hom ≫ t ≫ (e.app Q).inv := by
  obtain ⟨W, hxW, _, hWU, g, hg⟩ :=
    exists_affine_perfect_open_stalk_degreewise_lift X U x hxU P Q hP t.f
  let eW := Functor.mapHomologicalComplexCompIso
    (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) (.up ℤ)
  let RW := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
  let SW := (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)
  have hcomm (n : ℤ) :
      (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) ≫
        (SW.obj (RW.obj Q)).d n (n + 1) =
      (SW.obj (RW.obj P)).d n (n + 1) ≫
        (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g (n + 1)) := by
    rw [hg n, hg (n + 1)]
    change (eW.app P).hom.f n ≫ t.f n ≫ (eW.app Q).inv.f n ≫
        (SW.obj (RW.obj Q)).d n (n + 1) = _
    exact ((eW.app P).hom ≫ t ≫ (eW.app Q).inv).comm n (n + 1)
  obtain ⟨V, hxV, hV, _, hVU, k, hk, hkg⟩ :=
    exists_affine_perfect_open_stalk_degreewise_shrink
      X U x hxU P Q hP W hxW hWU g hcomm
  let fV := CochainComplex.ofHom k hk
  refine ⟨V, hxV, hV, hVU, fV, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  change (openModuleStalkFunctor X V ⟨x, hxV⟩).map (k n) = _
  rw [hkg n, hg n]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  simp only [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id, Category.comp_id]

end
end AlgebraicGeometry.Scheme
