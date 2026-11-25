/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars

import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed

/-! # Exact scalar extension preserves bounded constructible module objects

If extension of scalars along a morphism `φ : R ⟶ S` of commutative ring objects of abelian
pro-étale sheaves on `X` preserves finite limits, its left derived functor sends bounded
constructible complexes to bounded constructible complexes
(`AlgebraicGeometry.ProEtale.boundedConstructible_leftDerivedExtendScalars_obj`).
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable {X : Scheme.{u}}
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [IsCommMonObj S] in
private lemma constructible_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : IsConstructibleModuleObject R M) :
    IsConstructibleModuleObject S ((Mod.extendScalars φ).obj M) := by
  rcases h with ⟨U, hU⟩
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.immersion i)
  exact IsLocallyFinitelyPresented.of_iso
    ((pullbackExtendScalarsComparison (U.immersion i) R S φ).app M).symm
    (lfp_extend (F.obj R) (F.obj S) (F.map φ) (hU i))

/-- Exact extension of scalars preserves bounded constructible complexes of module objects.
(auxiliary; not a blueprint node)

Proof: scalar extension preserves colimits and sends the regular module to the regular
module, hence preserves finite free presentations. Monoidal pullback commutes with scalar
extension: the two left adjoints have canonically isomorphic right adjoints, by naturality
of the pullback adjunction unit. Thus the same presentation covers and stratification
witness constructibility after scalar extension. Exact scalar extension commutes with
derived cohomology. It preserves zero objects, so the old cohomological bounds remain
valid; its preservation of constructible sheaves applies to each cohomology object.
This also includes zero rings, rank-zero presentations, and the empty scheme. -/
theorem boundedConstructible_leftDerivedExtendScalars_obj
    [PreservesFiniteLimits (Mod.extendScalars φ)]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (hK : boundedConstructible R K) :
    boundedConstructible S ((Mod.extendScalars φ).leftDerivedFunctor.obj K) := by
  rw [mem_boundedConstructible_iff] at hK ⊢
  obtain ⟨⟨a, b, hab⟩, hK⟩ := hK
  let F := Mod.extendScalars φ
  refine ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact (F.map_isZero (hab i hi)).of_iso
      ((F.leftDerivedFunctorHomologyFunctorIso i).app K).symm
  · exact IsConstructibleModuleObject.of_iso ((F.leftDerivedFunctorHomologyFunctorIso n).app K)
      (constructible_extend R S φ (hK n))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [IsCommMonObj S] in
private noncomputable def pullbackExtendScalarsIso :
    Mod.extendScalars φ ⋙ (upperStar Ab.{u + 1} g).mapMod S ≅
      (upperStar Ab.{u + 1} g).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} g).map φ) := by
  let F := upperStar Ab.{u + 1} g
  let G := lowerStar Ab.{u + 1} g
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} g
  let a := (Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction S)
  let b := (adj.mapModAdjunction R).comp
    (Mod.extendRestrictAdjunction (F.map φ))
  have : IsMonHom (adj.unitAlgHom R) := Adjunction.isMonHom_unitAlgHom adj R
  have : IsMonHom (adj.unitAlgHom S) := Adjunction.isMonHom_unitAlgHom adj S
  have hφ : adj.unitAlgHom R ≫ G.map (F.map φ) = φ ≫ adj.unitAlgHom S :=
    (adj.unit.naturality φ).symm
  have e : Mod.comap (F.map φ) ⋙
      (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)) ≅
      (G.mapMod (F.obj S) ⋙ Mod.comap (adj.unitAlgHom S)) ⋙ Mod.comap φ :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr hφ) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm
  exact a.leftAdjointUniq (b.ofNatIsoRight e)

end

end AlgebraicGeometry.ProEtale
