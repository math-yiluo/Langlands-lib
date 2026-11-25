/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSums
import WeilConjectures.AlgebraicGeometry.ModuleHigherDirectImageCoproductEpi
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private noncomputable def homologyCofanIsColimit
    (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, E i ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (r : ℤ) :
    IsColimit (Cofan.mk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).obj S)
      (fun i ↦ (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map (ι i))) := by
  classical
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let K := fun i ↦ Q.objPreimage (E i)
  let e := fun i ↦ Q.objObjPreimageIso (E i)
  let c : Cofan E := Cofan.mk (Q.obj (∐ K))
    (fun i ↦ (e i).inv ≫ Q.map (Sigma.ι K i))
  have hsum := derivedAmbientDirectSums X I E K e
  let hc₀ := hsum.1.some
  have hH := hsum.2
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r
  have : IsIso (Sigma.desc (fun i ↦ H.map (c.inj i))) := hH r
  let d := hc₀.coconePointUniqueUpToIso hc
  have heq : Sigma.desc (fun i ↦ H.map (ι i)) =
      Sigma.desc (fun i ↦ H.map (c.inj i)) ≫ H.map d.hom := by
    apply Sigma.hom_ext
    intro i
    simp only [colimit.ι_desc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as,
      colimit.ι_desc_assoc]
    rw [← H.map_comp]
    exact congrArg H.map (hc₀.comp_coconePointUniqueUpToIso_hom hc ⟨i⟩).symm
  have : IsIso (Sigma.desc (fun i ↦ H.map (ι i))) := by
    rw [heq]
    infer_instance
  exact ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).2 (by
    change IsIso (Sigma.desc (fun i ↦ H.map (ι i)))
    infer_instance)).some

private noncomputable def truncatedHomologyCofanIsColimit
    (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, E i ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a r : ℤ) :
    IsColimit (Cofan.mk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).obj
          ((DerivedCategory.TStructure.t.truncGE a).obj S))
      (fun i ↦ (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))) := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r
  let T := DerivedCategory.TStructure.t (C := SheafOfModules.{u}
    (moduleRings X.toRingedSpace))
  by_cases h : a ≤ r
  · have hπ (Z : schemeDerivedCategory X) : IsIso (H.map ((T.truncGEπ a).app Z)) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app Z a r h
    let e : H ≅ T.truncGE a ⋙ H := NatIso.ofComponents
      (fun Z ↦ asIso (H.map ((T.truncGEπ a).app Z))) (by
        intro Z W g
        simpa only [Functor.comp_map, asIso_hom, Functor.id_map, ← H.map_comp] using
          congrArg H.map ((T.truncGEπ a).naturality g))
    have hH := homologyCofanIsColimit X I E S ι hc r
    have hH' : IsColimit (H.mapCocone (Cofan.mk S ι)) :=
      (isColimitMapCoconeCofanMkEquiv H E ι).symm hH
    exact isColimitMapCoconeCofanMkEquiv (T.truncGE a ⋙ H) E ι
      (IsColimit.mapCoconeEquiv e hH')
  · have hz (Z : schemeDerivedCategory X) : IsZero (H.obj ((T.truncGE a).obj Z)) :=
      DerivedCategory.isZero_of_isGE _ a r (lt_of_not_ge h)
    exact IsColimit.ofIsZero _ ((Functor.isZero_iff _).2 (fun i ↦ hz (E i.as))) (hz S)

/-- The second-page coproduct comparison is an epimorphism.
Source: Stacks Project, Tag 08DZ, second-page direct-sum reduction, using
Tag 07TB for filtered colimits and hence direct sums of module sheaves. Tag 015J identifies
these ordinary higher images as second-page terms. This is the surjectivity half only.
(blueprint: lem-pc-truncated-direct-image-second-page-coproduct-epi).

Proof: Put M_i = H^r(tau_GE(a) E_i) and M = H^r(tau_GE(a) S). Choose complex
representatives of the E_i and their termwise coproduct. Exact direct sums in
module sheaves compute its cohomology as the coproduct of the individual
cohomology sheaves. The universal property hc transports this computation to
S, naturally in the given coprojections. If r >= a, the natural cohomology
identifications for lower truncation give the same coproduct cofan on M_i and
M; if r < a all these sheaves are zero. Each M_i is quasi-coherent since E_i
has quasi-coherent cohomology; the coproduct M is quasi-coherent as well.
On an affine open V of Y, f^(-1)(V) is qcqs. Restriction of module sheaves to
this open preserves their coproduct. The qcqs cohomology direct-sum theorem
makes the map from the direct sum of H^p(f^(-1)(V), M_i) onto
H^p(f^(-1)(V), M) surjective. These maps commute with restriction and with
the coefficient morphisms. Ordinary R^p f_* is the sheafification of the
cohomology presheaf V |-> H^p(f^(-1)(V), -), and module sheafification
preserves coproducts. Since affine opens form a basis, the sectionwise
surjectivity just proved on that basis gives local surjectivity of the
sheafified comparison, hence an epimorphism of module sheaves. Finally,
compute each degree-zero module by an ordinary injective resolution, viewed
as a bounded-below K-injective complex. This gives the natural identification
of the ordinary R^p f_* with schemeModuleHigherDirectImage f p; naturality
identifies the sheafified comparison with the displayed Sigma.desc map.
For an empty family or r < a both sides are zero, and for p = 0 the same
presheaf computation is the ordinary direct image. No assertion that
arbitrary sheaf coproducts are sectionwise coproducts is used. -/
theorem truncated_directImage_secondPage_coproduct_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a : ℤ) (p : ℕ) (r : ℤ) :
    Epi (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) := by
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r
  let T := (DerivedCategory.TStructure.t (C := SheafOfModules.{u}
    (moduleRings X.toRingedSpace))).truncGE a
  let M := fun i ↦ H.obj (T.obj (E i).obj)
  let N := H.obj (T.obj S)
  let j := fun i ↦ H.map (T.map (ι i))
  let hM : IsColimit (Cofan.mk N j) :=
    truncatedHomologyCofanIsColimit X I (fun i ↦ (E i).obj) S ι hc a r
  let F := schemeModuleHigherDirectImage f (p : ℤ)
  let R := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p
  have hR : Epi (Sigma.desc (fun i ↦ R.map (j i))) :=
    moduleHigherDirectImage_coproduct_epi f I M N j hM p
  have he : Nonempty (F ≅ R) :=
    (sheafCohomologyAndHigherDirectImages X).2 Y f p
  obtain ⟨e'⟩ := he
  have : IsIso (Limits.Sigma.map (fun i ↦ e'.hom.app (M i))) := by infer_instance
  have heq : Sigma.desc (fun i ↦ F.map (j i)) =
      Limits.Sigma.map (fun i ↦ e'.hom.app (M i)) ≫
        Sigma.desc (fun i ↦ R.map (j i)) ≫ e'.inv.app N := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_map_assoc, Sigma.ι_comp_desc_assoc]
    rw [← e'.hom.naturality_assoc]
    simp
  change Epi (Sigma.desc (fun i ↦ F.map (j i)))
  rw [heq]
  infer_instance

end AlgebraicGeometry
