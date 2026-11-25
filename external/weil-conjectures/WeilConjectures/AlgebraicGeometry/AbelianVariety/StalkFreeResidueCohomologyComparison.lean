/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.AbelianVariety.KFlatStalkResidueCohomology
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Residue cohomology computed by a free stalk representative

Source: Stacks Project, Tags 06YB, 064K and 0098.
(blueprint: lem-sc-stalk-free-residue-cohomology-comparison).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every bounded-above free complex representing the stalk derived object
computes the derived residue fibre, degree by degree, by a linear equivalence.

Source: Stacks Project, Cohomology of Sheaves, Tag 06YB; More on Algebra, Tag 064K;
Sheaves, Tag 0098.
(blueprint: lem-sc-stalk-free-residue-cohomology-comparison).

Proof:
1. Take a K-flat sheaf resolution of G. Its stalk is K-flat by Tag 06YB, and
   exactness of stalks preserves its comparison to G_x. Pulling this resolution
   back to the residue-field point computes Li_x^*E using eG. On the one-point
   spectrum, sections are exact. The pullback tensor product of a sheaf has
   sections kappa(x) tensor over O_X,x its stalk by Tag 0098. The scalar and vector
   germs restrict to the residue point, and their balanced bilinear map
   induces this canonical identification. The identification is functorial in
   the sheaf, hence is an identification of the corresponding complexes.
2. The bounded-above free K is K-flat by Tag 064K. Its derived comparison
   eK with G_x identifies their derived residue tensor products, since derived
   tensor inverts quasi-isomorphisms and therefore respects derived isomorphisms.
   The termwise residue extension of K is a representative of this product.
3. Apply degree-i homology to this comparison. Sections on Spec kappa(x) and
   transport along GammaSpecIso give exactly derivedFiberCohomology. The residue
   field of the scheme point is definitionally IsLocalRing.ResidueField O_X,x.
   The comparisons commute with its scalar action, so give a linear equivalence,
   not merely an additive equivalence. This is independent of the chosen K.
No finiteness of the cohomology or local strict perfection is assumed or concluded.
In particular the statement includes zero complexes and arbitrary upper bounds;
unbounded below K and free terms of infinite rank are allowed by bounded-above K-flatness. -/
theorem nonempty_stalkFree_residueCohomology_linearEquiv
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (K : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (b : ℤ) (hb : K.IsStrictlyLE b)
    (hfree : ∀ j : ℤ, Module.Free (X.presheaf.stalk x) (K.X j))
    (eK : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)) (i : ℤ) :
    Nonempty (derivedFiberCohomology X E i x ≃ₗ[IsLocalRing.ResidueField
      (X.presheaf.stalk x)]
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homology i)) := by
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) G
  have : QuasiIso s := hs
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  let eP : DerivedCategory.Q.obj P ≅ E := asIso (DerivedCategory.Q.map s) ≪≫ eG
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have : S.PreservesHomology := Functor.preservesHomology_of_map_exact S (by
    intro T hT
    exact ((RingedSpace.module_stalk_exact X.toRingedSpace T.f).2.2.2.2
      T.X₃ T.f T.g T.zero).mp hT x)
  let Sc := S.mapHomologicalComplex (ComplexShape.up ℤ)
  have hSs : QuasiIso (Sc.map s) := inferInstance
  have : IsIso (DerivedCategory.Q.map (Sc.map s)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (Sc.map s)).2 hSs
  let eKP : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj (Sc.obj P) :=
    eK ≪≫ (asIso (DerivedCategory.Q.map (Sc.map s))).symm
  have hPK := (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace P).mp hP x
  have hKK := CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat K
    ⟨b, (K.isStrictlyLE_iff b).mp hb⟩ (by
      intro j
      have := hfree j
      exact Module.Flat.of_free)
  obtain ⟨e₁⟩ := nonempty_kFlat_stalk_residueCohomology_linearEquiv X E x P hP eP i
  obtain ⟨e₂⟩ := CochainComplex.nonempty_kFlat_scalarExtension_homology_linearEquiv
    (IsLocalRing.residue (X.presheaf.stalk x)) K (Sc.obj P) hKK hPK eKP i
  exact ⟨e₁.trans e₂.symm⟩

end AlgebraicGeometry.Scheme
