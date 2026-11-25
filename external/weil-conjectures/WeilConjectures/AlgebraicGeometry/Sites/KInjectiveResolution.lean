/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# K-injective resolutions of complexes of étale sheaves of modules

Every complex of sheaves of `R`-modules on the small étale site of a scheme admits a
K-injective resolution, functorially; two K-injective resolutions of the same complex are
homotopy equivalent compatibly with the resolution maps; and a bounded below complex of
injective objects is K-injective.

## Main statements

- `CochainComplex.IsKInjective.exists_homotopyEquiv`: two K-injective resolutions of the same
  complex are homotopy equivalent, compatibly with the resolution maps up to homotopy.
- `AlgebraicGeometry.Scheme.kInjectiveResolutions_smallEtale`: the three statements above for
  sheaves of modules on the small étale site.
-/

@[expose] public section

universe w v u

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKInjective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Uniqueness of K-injective resolutions.** If `s : K ⟶ I` and `t : K ⟶ J` are two
K-injective resolutions of the same cochain complex `K`, there is a homotopy equivalence
`e : I ≃ J` with `s ≫ e` homotopic to `t`. -/
theorem exists_homotopyEquiv {K I J : CochainComplex C ℤ} (s : K ⟶ I) (t : K ⟶ J)
    [QuasiIso s] [QuasiIso t] [I.IsKInjective] [J.IsKInjective] :
    ∃ e : HomotopyEquiv I J, Nonempty (Homotopy (s ≫ e.hom) t) := by
  let := HasDerivedCategory.standard C
  let qu := HomotopyCategory.quotient C (.up ℤ)
  let e : Qh.obj (qu.obj I) ≅ Qh.obj (qu.obj J) :=
    (quotientCompQhIso C).app I ≪≫ (asIso (Q.map s)).symm ≪≫ asIso (Q.map t) ≪≫
      (quotientCompQhIso C).symm.app J
  obtain ⟨a, ha⟩ := (Qh_map_bijective (qu.obj I) J).2 e.hom
  obtain ⟨b, hb⟩ := (Qh_map_bijective (qu.obj J) I).2 e.inv
  let e' : qu.obj I ≅ qu.obj J :=
    ⟨a, b, (Qh_map_bijective _ I).1 (by
        rw [Functor.map_comp, ha, hb, e.hom_inv_id, CategoryTheory.Functor.map_id]),
      (Qh_map_bijective _ J).1 (by
        rw [Functor.map_comp, ha, hb, e.inv_hom_id, CategoryTheory.Functor.map_id])⟩
  refine ⟨HomotopyCategory.homotopyEquivOfIso e', ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (Qh_map_bijective (qu.obj K) J).1
  have hs := quotientCompQhIso_hom_naturality s
  have ht := quotientCompQhIso_hom_naturality t
  change Qh.map (qu.map (s ≫ Quot.out a)) = Qh.map (qu.map t)
  rw [Functor.map_comp, HomotopyCategory.quotient_map_out, Functor.map_comp, ha]
  rw [← cancel_mono ((quotientCompQhIso C).hom.app J), ht]
  simp only [e, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% hs, IsIso.hom_inv_id_assoc]

end CochainComplex.IsKInjective

namespace AlgebraicGeometry.Scheme

open CochainComplex

/-- **Existence of K-injective resolutions.** Let `T` be a scheme and `R` a commutative ring.
In the category of complexes of sheaves of `R`-modules on the small étale site of `T`:
1. every complex `K` admits a K-injective resolution `K ⟶ I K`, functorially in `K`
   (`CochainComplex.kInjectiveResolutionFunctor`, `CochainComplex.toKInjectiveResolution`);
2. two K-injective resolutions `s: K ⟶ I`, `t: K ⟶ J` of the same complex are homotopy
   equivalent, by a homotopy equivalence `e` with `s ≫ e` homotopic to `t`;
3. a bounded below complex of injective objects is K-injective. -/
theorem kInjectiveResolutions_smallEtale (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    (∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ,
      ((kInjectiveResolutionFunctor.{u + 1} _).obj K).IsKInjective ∧
        Mono ((toKInjectiveResolution.{u + 1} _).app K) ∧
        QuasiIso ((toKInjectiveResolution.{u + 1} _).app K)) ∧
    (∀ {K I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ}
      (s : K ⟶ I) (t : K ⟶ J), QuasiIso s → QuasiIso t → I.IsKInjective → J.IsKInjective →
        ∃ e : HomotopyEquiv I J, Nonempty (Homotopy (s ≫ e.hom) t)) ∧
    (∀ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) (d : ℤ),
      I.IsStrictlyGE d → (∀ n, Injective (I.X n)) → I.IsKInjective) := by
  refine ⟨fun K ↦ ⟨inferInstance, (monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ K).1,
    (monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ K).2⟩, fun s t _ _ _ _ ↦
      IsKInjective.exists_homotopyEquiv s t, fun I d _ _ ↦ isKInjective_of_injective I d⟩

end AlgebraicGeometry.Scheme
