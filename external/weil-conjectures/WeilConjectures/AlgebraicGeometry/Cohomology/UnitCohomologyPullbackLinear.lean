/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Sites.Equivalence

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The cohomology map of a module morphism over the displayed common affine base.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
(blueprint: def-pbc-unit-cohomology-pullback-linear)

The map is the adjoint coefficient map after exact inverse image on Ext. The
projection identity identifies the structural scalars; coefficient naturality
therefore proves linearity. No equivalence or witness is chosen. -/
def unitCohomologyPullbackLinear
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (f' : X ⟶ Spec (.of R)) (d : X ⟶ Y)
    (hd : d ≫ f = f') (M : Y.Modules)
    (φ : M ⟶ (pushforward d).obj (SheafOfModules.unit X.ringCatSheaf)) (n : ℕ) :
    HOver f M n →ₗ[R] HOver f' (SheafOfModules.unit X.ringCatSheaf) n :=
  cohomologyComparisonLinear (R := R) (invImage d) (constIso d).symm (coeff d φ)
    ((scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom))
    ((scalarRep (SheafOfModules.unit X.ringCatSheaf)).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ f'.appTop).hom)) (fun a ↦ by
        have hs : d.appTop (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom a) =
            ((Scheme.ΓSpecIso (.of R)).inv ≫ f'.appTop).hom a := by
          have he := congrArg Scheme.Hom.appTop hd
          rw [Scheme.Hom.comp_appTop] at he
          exact ConcreteCategory.congr_hom
            (congrArg ((Scheme.ΓSpecIso (.of R)).inv ≫ ·) he) a
        change (invImage d).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map
            (M.smulHom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom a))) ≫
            coeff d φ = coeff d φ ≫
              (SheafOfModules.toSheaf X.ringCatSheaf).map
                ((smulHom (X := X) (SheafOfModules.unit X.ringCatSheaf))
                  (((Scheme.ΓSpecIso (.of R)).inv ≫ f'.appTop).hom a))
        rw [← hs]
        apply coeff_naturality
        rw [pushforward_map_smulHom]
        exact smulHom_naturality φ _) n

/-- Transport through a scheme isomorphism and a specified unit-module isomorphism
is bijective on ordinary cohomology.
Source: Stacks Project, Tag 01F7; `Sheaf.H.mapFunctor_bijective`.
(blueprint: lem-pbc-unit-cohomology-pullback-linear-bijective)

Proof: Inverse image along d is an equivalence of abelian sheaf categories: its
inverse is inverse image along the inverse scheme morphism, with unit and counit
from the inverse-image composition and identity comparisons. Thus it is fully
faithful and preserves injectives, and mapFunctor_bijective applies to its action
on Ext. The adjoint of the structural unit map is an isomorphism because d is an
isomorphism of ringed spaces. Precomposing the structural map by e.hom transports
this adjoint by the forgotten isomorphism e, so coeff d of the displayed composite
is an isomorphism too. Its cohomology map is bijective by functoriality on
isomorphisms. Compose these two bijections. The defined linear map has exactly
this underlying composite. No flatness hypothesis is needed; zero rings, empty
schemes and all nonnegative degrees are included. -/
theorem unitCohomologyPullbackLinear_bijective
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (f' : X ⟶ Spec (.of R)) (d : X ⟶ Y) [IsIso d]
    (hd : d ≫ f = f') (M : Y.Modules) (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (n : ℕ) :
    Function.Bijective (unitCohomologyPullbackLinear f f' d hd M
      (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom) n) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} d.base
  let E := TopologicalSpace.Opens.mapMapIso (asIso d.base)
  have hE : E.functor.IsCocontinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
      (coverPreserving_opens_map (inv d.base))
  have hE' : E.inverse.IsCocontinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    (E.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
      (coverPreserving_opens_map d.base)
  have hdense := E.isDenseSubsite_inverse_of_isCocontinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have hr : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} d.base).IsEquivalence :=
    (E.sheafCongr (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).isEquivalence_inverse
  have hl : (invImage d).IsEquivalence := a.isEquivalence_left_of_isEquivalence_right
  let φ := e.hom ≫ SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom
  have hu : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom) := by
    apply Hom.isIso_iff_isIso_app.mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ConcreteCategory.bijective_of_isIso (d.app U)
  have hφ : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) := by
    dsimp only [φ]
    infer_instance
  have hc : IsIso (coeff d φ) := by
    change IsIso (a.homEquiv _ _ |>.symm _)
    rw [Adjunction.homEquiv_counit]
    infer_instance
  change Function.Bijective (fun x ↦ Sheaf.H.map (coeff d φ) n
    (Sheaf.H.mapFunctor (invImage d) (constIso d).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) n x))
  exact (ConcreteCategory.bijective_of_isIso
    ((Sheaf.functorH _ n).map (coeff d φ))).comp
    (Sheaf.H.mapFunctor_bijective (invImage d) (constIso d).symm _ n)

end
end AlgebraicGeometry.Scheme.Modules
