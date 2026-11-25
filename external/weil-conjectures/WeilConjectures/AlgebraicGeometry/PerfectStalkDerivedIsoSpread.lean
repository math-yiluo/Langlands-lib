/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedHomLift
import WeilConjectures.AlgebraicGeometry.PerfectStalkQuasiIsoDetection

/-! # Extending a derived stalk isomorphism between existing local perfect models

Source: Stacks Project, Tag 09RE, affine full faithfulness, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-stalk-derived-iso-spread).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private theorem restrict_strictlyPerfect_for_stalk_spread
    (X : Scheme.{u}) (U V : X.Opens) (h : V ≤ U)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K) :
    IsStrictlyPerfect X V
      (((SheafOfModules.overMap.{u}
        (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K) := by
  let T := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE h)
  constructor
  · obtain ⟨a, b, hab⟩ := hK.1
    exact ⟨a, b, fun n hn ↦ T.map_isZero (hab n hn)⟩
  · intro n
    obtain ⟨m, i, r, hir⟩ := hK.2 n
    let e := (SheafOfModules.mapFreeIso T (ULift.{u} (Fin m))
      (SheafOfModules.overMapUnitIso (R := moduleRings X.toRingedSpace)
        (homOfLE h)).symm).symm
    refine ⟨m, T.map i ≫ e.hom, e.inv ≫ T.map r, ?_⟩
    change (T.map i ≫ e.hom) ≫ e.inv ≫ T.map r = 𝟙 (T.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact T.map_id _

private theorem restrict_model_for_stalk_spread (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U V : X.Opens) (h : V ≤ U) (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj
        (((SheafOfModules.overMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let T := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE h)
  let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have : PreservesFiniteLimits (A ⋙ T) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (A ⋙ T) := comp_preservesFiniteColimits _ _
  exact ⟨(Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE h))).symm.app E ≪≫
    (Functor.mapDerivedCategoryCompIso A T).symm.app E ≪≫ T.mapDerivedCategory.mapIso e ≪≫
      T.mapDerivedCategoryFactors.app K⟩

set_option backward.isDefEq.respectTransparency false in
/-- Existing local perfect models with isomorphic derived stalks are isomorphic nearby.

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2), with Tags 00CR and 06Z0.
(blueprint: lem-sc-perfect-stalk-derived-iso-spread).

Proof:
1. Intersect U with the neighbourhood V supplied for Q(G), and take an affine
   neighbourhood of x inside that intersection. Restrict P and H to it. These are
   strictly perfect complexes. Their terms are retracts of finite free sheaves, hence
   quasi-coherent; the affine correspondence gives bounded finite projective complexes
   over the section ring A. Exactness of stalks and the local comparison for G identify
   their prime-localized derived objects with the derived stalks of G and H.
2. Present the prime localization as the filtered colimit of the A_f outside the prime.
   Full faithfulness for perfect complexes (09RE, or 0BC7 (2)) descends the given
   isomorphism and its inverse to one common principal neighbourhood. Injectivity
   of the Hom comparison descends both inverse identities after a further shrinking.
   This gives an actual derived isomorphism on an affine open W containing x inside U.
3. Use the affine derived sheaf equivalence and the restriction comparisons to identify
   the two descended objects with Q(G restricted to W) and Q(H restricted to W).
   Compose with these identifications to obtain the conclusion. No terms, ranks or
   differentials of H are changed. The argument also works for zero complexes and any
   bounds, and only takes principal opens inside one affine chart, so no separatedness
   hypothesis is required. The derived-category universes on sheaves and stalk modules
   may differ: comparisons are transported through their localization equivalences.
-/
theorem exists_affine_restriction_iso_of_perfect_stalk_iso
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
            (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P))
    (U : X.Opens) (hxU : x ∈ U)
    (hH : IsStrictlyPerfect X U
      (((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapHomologicalComplex (.up ℤ)).obj H))
    (e : DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ≅
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H)) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ W ≤ U ∧
      Nonempty (DerivedCategory.Q.obj
          (((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapHomologicalComplex (.up ℤ)).obj G) ≅
        DerivedCategory.Q.obj
          (((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapHomologicalComplex (.up ℤ)).obj H)) := by
  obtain ⟨O, hxO, P₀, hP₀, ⟨iG₀⟩⟩ := hlocal
  obtain ⟨A, -, hxA, hAO⟩ := exists_isAffineOpen_mem_and_subset (U := O ⊓ U) ⟨hxO, hxU⟩
  have hAP : A ≤ O := hAO.trans inf_le_left
  have hAU : A ≤ U := hAO.trans inf_le_right
  let R := moduleRings X.toRingedSpace
  let L := SheafOfModules.overMap.{u} R (homOfLE hAP : A ⟶ O)
  let M := SheafOfModules.overMap.{u} R (homOfLE hAU : A ⟶ U)
  let P := (L.mapHomologicalComplex (.up ℤ)).obj P₀
  let H₀ := ((SheafOfModules.overFunctor.{u} R U).mapHomologicalComplex (.up ℤ)).obj H
  let Q := (M.mapHomologicalComplex (.up ℤ)).obj H₀
  have hP : IsStrictlyPerfect X A P := restrict_strictlyPerfect_for_stalk_spread X O A hAP P₀ hP₀
  have hQ : IsStrictlyPerfect X A Q := restrict_strictlyPerfect_for_stalk_spread X U A hAU H₀ hH
  obtain ⟨iG⟩ := restrict_model_for_stalk_spread X O A hAP (DerivedCategory.Q.obj G) P₀ iG₀
  obtain ⟨iH⟩ := restrict_model_for_stalk_spread X U A hAU (DerivedCategory.Q.obj H) H₀
    ((SheafOfModules.overFunctor.{u} R U).mapDerivedCategoryFactors.app H)
  obtain ⟨V, hxV, -, hVA, f, hf⟩ :=
    exists_affine_perfect_stalk_hom_lift X x G H A hxA P Q hP hQ iG iH e.hom
  let N := SheafOfModules.overMap.{u} R (homOfLE hVA : V ⟶ A)
  let P' := (N.mapHomologicalComplex (.up ℤ)).obj P
  let Q' := (N.mapHomologicalComplex (.up ℤ)).obj Q
  have hP' : IsStrictlyPerfect X V P' := restrict_strictlyPerfect_for_stalk_spread X A V hVA P hP
  have hQ' : IsStrictlyPerfect X V Q' := restrict_strictlyPerfect_for_stalk_spread X A V hVA Q hQ
  let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
      ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
  have : S.PreservesZeroMorphisms :=
    AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
  have hfiso : IsIso (DerivedCategory.Q.map
      ((S.mapHomologicalComplex (.up ℤ)).map f)) := by
    rw [hf]
    infer_instance
  have hfquasi : QuasiIso
      ((S.mapHomologicalComplex (.up ℤ)).map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hfiso
  obtain ⟨W, hxW, hW, hWV, hfW⟩ :=
    exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso
      X V x hxV P' Q' hP' hQ' f hfquasi
  obtain ⟨iG'⟩ := restrict_model_for_stalk_spread X A V hVA (DerivedCategory.Q.obj G) P iG
  obtain ⟨iH'⟩ := restrict_model_for_stalk_spread X A V hVA (DerivedCategory.Q.obj H) Q iH
  obtain ⟨g⟩ := restrict_model_for_stalk_spread X V W hWV (DerivedCategory.Q.obj G) P' iG'
  obtain ⟨h⟩ := restrict_model_for_stalk_spread X V W hWV (DerivedCategory.Q.obj H) Q' iH'
  let T := SheafOfModules.overMap.{u} R (homOfLE hWV : W ⟶ V)
  let B := SheafOfModules.overFunctor.{u} R W
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f) := hfW
  let ef := asIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f))
  exact ⟨W, hxW, hW, hWV.trans (hVA.trans hAU),
    ⟨(B.mapDerivedCategoryFactors.app G).symm ≪≫ g ≪≫ ef ≪≫ h.symm ≪≫
      B.mapDerivedCategoryFactors.app H⟩⟩

end
end AlgebraicGeometry.Scheme
