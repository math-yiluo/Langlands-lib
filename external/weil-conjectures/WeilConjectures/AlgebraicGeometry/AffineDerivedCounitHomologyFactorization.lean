/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import WeilConjectures.AlgebraicGeometry.AffineDerivedUnitIsomorphism
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison

/-! # The derived affine counit on cohomology

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
(blueprint: new-affine-derived-counit-homology-factorization).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- On cohomology the derived affine counit is the ordinary tilde-sections counit,
after identifying its source with associated sheaf of sections of cohomology.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, counit calculation.
(blueprint: new-affine-derived-counit-homology-factorization).

Proof: Global sections, being right adjoint, preserves products; transport of scalars
through ΓSpecIso is exact and preserves products. Affine vanishing gives the bound
N = 1 on quasi-coherent sheaves. The same holds after forgetting to abelian groups,
an exact conservative functor. Apply the unbounded cohomological bound to the negative
truncation and use its truncation triangle to identify degree-zero derived sections
with ordinary sections of degree-zero cohomology. Shifts give this comparison in every
degree. Exact associated sheaf commutes with cohomology. For the adjunction induced
from ordinary tilde and sections, these comparisons identify the derived counit with
the ordinary counit: on a K-injective representative this is the evaluation map,
and the truncation comparisons are natural for that map. For the functors F and G
of the statement, descend the given comparison for F through Q and use the comparison
for G. Uniqueness of right adjoints supplies an isomorphism between the transported
canonical adjunction and adj; absorb its image on cohomology into the source comparison.
The target remains the same cohomology sheaf, giving exactly the displayed equation.
No boundedness of K is assumed: the uniform bound and products are what justify the
negative-truncation passage. The zero object and the zero ring give the zero-map
identity between zero objects, so neither is excluded.
-/
theorem affineDerivedCounit_homology_factorization (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (adj : F ⊣ G)
    (hF : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor))
    (K : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
          ((F.obj (G.obj K)).obj) ≅
        (tilde.functor (.of A)).obj ((moduleSpecΓFunctor (R := .of A)).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj K.obj)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).map
          ((schemeDerivedQCohProperty (Spec (.of A))).ι.map (adj.counit.app K)) =
        e.hom ≫ Scheme.Modules.fromTildeΓ (R := .of A)
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj K.obj) := by
  have hreflect {M N : schemeDerivedQCohCategory (Spec (.of A))} (f : M ⟶ N)
      (hf : IsIso (G.map f)) : IsIso f := by
    suffices h : IsIso ((schemeDerivedQCohProperty (Spec (.of A))).ι.map f) from
      isIso_of_reflects_iso _ (schemeDerivedQCohProperty (Spec (.of A))).ι
    apply (DerivedCategory.isIso_iff _ _).2
    intro i
    obtain ⟨e⟩ := affineDerivedSections_homology_comparison A G hG i
    have hmap : IsIso ((G ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map f) := by
      change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (G.map f))
      infer_instance
    have hΓ := (NatIso.isIso_map_iff e f).1 hmap
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
    let g := H.map ((schemeDerivedQCohProperty (Spec (.of A))).ι.map f)
    have hM := M.property i
    have hN := N.property i
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) (H.obj M.obj)) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) _
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) (H.obj N.obj)) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) _
    change IsIso ((moduleSpecΓFunctor (R := .of A)).map g) at hΓ
    let : IsIso ((moduleSpecΓFunctor (R := .of A)).map g) := hΓ
    have heq := (tilde.adjunction (R := .of A)).counit.naturality g
    have ht : IsIso ((tilde.functor (.of A)).map
        ((moduleSpecΓFunctor (R := .of A)).map g)) :=
      Functor.map_isIso (tilde.functor (.of A)) _
    change (tilde.functor (.of A)).map ((moduleSpecΓFunctor (R := .of A)).map g) ≫
      Scheme.Modules.fromTildeΓ (R := .of A) (H.obj N.obj) =
      Scheme.Modules.fromTildeΓ (R := .of A) (H.obj M.obj) ≫ g at heq
    have : IsIso g := IsIso.of_isIso_fac_left heq.symm
    exact this
  have hu := affineDerivedUnit_isIso A F G adj hF hG (G.obj K)
  have hGc : IsIso (G.map (adj.counit.app K)) :=
    isIso_of_hom_comp_eq_id _ (adj.right_triangle_components K)
  have hc := hreflect (adj.counit.app K) hGc
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n
  let c := H.map ((schemeDerivedQCohProperty (Spec (.of A))).ι.map (adj.counit.app K))
  have hK := K.property n
  have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) (H.obj K.obj)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) _
  refine ⟨asIso c ≪≫ (asIso (Scheme.Modules.fromTildeΓ (R := .of A)
    (H.obj K.obj))).symm, ?_⟩
  change c = (c ≫ inv (Scheme.Modules.fromTildeΓ (R := .of A) (H.obj K.obj))) ≫
    Scheme.Modules.fromTildeΓ (R := .of A) (H.obj K.obj)
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]


end AlgebraicGeometry
