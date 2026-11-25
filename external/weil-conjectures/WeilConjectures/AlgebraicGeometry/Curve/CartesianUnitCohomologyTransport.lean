/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.Cohomology.CartesianUnitCohomologyPullbackComposition

/-! # Transport of ordinary unit cohomology across a displayed cartesian square

Source: Stacks Project, Tags 01F7 and 02KH; Mathlib unit-module pullback.
(blueprint: lem-pbc-cartesian-unit-cohomology-transport)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The displayed unit module and the canonical pulled-back unit have the same
ordinary cohomology, compatibly with structural scalars and pullback.
Source: Mathlib `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`;
Stacks Project, Tag 01F7, cohomology-equation-functorial; Tag 02KH, the canonical
base-change map before tensor extension.
(blueprint: lem-pbc-cartesian-unit-cohomology-transport)

Proof: The universal property gives an isomorphism from C' to the categorical
pullback, commuting with both projections. The adjoint structure-sheaf map from
the pullback of the unit module to the unit module is an isomorphism. Invert its
cohomology map, and transport cohomology along the scheme isomorphism, to obtain
t. Both maps commute with multiplication by the structural image of a scalar;
the second projection identity identifies those images, hence t is k'-linear.
The unit characterization of the unit-module isomorphism identifies the
coefficient map unitToPushforwardObjUnit with the baseChangeUnit after this
transport. Naturality of exact inverse image on Ext, including the constant
integer sheaf comparison, then gives the displayed equality. This is a comparison
of untensored maps; neither flatness nor a cohomological base-change isomorphism
is used. It applies to zero rings, empty schemes and degree zero as well. -/
theorem exists_cartesian_unit_cohomology_transport
    {k k' : Type u} [CommRing k] [CommRing k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (n : ℕ) :
    ∃ t : HOver f' (SheafOfModules.unit C'.ringCatSheaf) n ≃ₗ[k']
        HOver (baseChangeSnd (S := k') f)
          (baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf)) n,
      ∀ x : HOver f (SheafOfModules.unit C.ringCatSheaf) n,
        t (Sheaf.H.map (coeff ι' (SheafOfModules.unitToPushforwardObjUnit
            ι'.toRingCatSheafHom)) n
          (Sheaf.H.mapFunctor (invImage ι') (constIso ι').symm
            ((SheafOfModules.toSheaf C.ringCatSheaf).obj
              (SheafOfModules.unit C.ringCatSheaf)) n x)) =
          H.baseChangeLinear (S := k') f (SheafOfModules.unit C.ringCatSheaf) n x :=
  by
    let d := h.isoPullback.hom
    have hd : d ≫ baseChangeSnd (S := k') f = f' := h.isoPullback_hom_snd
    let M := baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf)
    let e : M ≅ SheafOfModules.unit (baseChangedScheme (S := k') f).ringCatSheaf :=
      pullbackObjUnitIso (baseChangeFst (S := k') f)
    let L := unitCohomologyPullbackLinear (baseChangeSnd (S := k') f) f' d hd M
      (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom) n
    have hb : Function.Bijective L :=
      unitCohomologyPullbackLinear_bijective _ _ _ _ _ e n
    let E := LinearEquiv.ofBijective L hb
    refine ⟨E.symm, fun x ↦ ?_⟩
    apply E.injective
    rw [E.apply_symm_apply]
    exact (cartesian_unit_cohomology_pullback_comp f h n x).symm

end AlgebraicGeometry.Scheme.Modules
