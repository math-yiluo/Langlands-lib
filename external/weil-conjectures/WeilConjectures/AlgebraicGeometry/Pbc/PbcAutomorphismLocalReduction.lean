/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalComplex
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization

/-! Compatible finite reductions of the transported local complex.

## References

* Stacks Tags 06YY and 09BT
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (g : U ⟶ Y)

/-- The relabeled local complex computes the reductions of ordinary pullback, and
these identifications intertwine every comparable pair of levels. -/
theorem pbcIsoLocalComplex_reduction_comparison
    (K : PbcCompletedDerived Y d) (M : AdicTower Y d)
    (eK : ∀ n, M.level n ≅ (pbcCompletedReduction Y d n).obj K)
    (heK : ∀ (b a : ℕ) (hab : a ≤ b),
      adicTowerSemilinearTransition Y d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient Y d b a hab)).map (eK a).hom =
        (eK b).hom ≫ pbcReductionTransition (pbcAdicProjection Y d b)
          (pbcAdicQuotient Y d b a hab) (pbcAdicProjection Y d a)
          (pbcAdicProjection_comp Y d b a hab) K)
    (a b : ℤ) (L : AdicTowerLocalModel d g M a b) :
    ∃ e : ∀ n : ℕ,
      (adicTowerPullback (g ≫ inv f) ((pbcAdicRings X d).obj (op n))).obj
          ((pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K)).level n) ≅
        adicTowerLocalReduction d (g ≫ inv f) (pbcIsoLocalComplex f d g L.complex) n,
      ∀ (j i : ℕ) (hij : i ≤ j),
        adicTowerRestrictedTransition d (g ≫ inv f)
            (pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K)) j i hij ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (g ≫ inv f)).map
            (pbcAdicQuotient X d j i hij))).map (e i).hom =
        (e j).hom ≫ adicTowerLocalTransition d (g ≫ inv f)
          (pbcIsoLocalComplex f d g L.complex) j i hij := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Λ' Λ'' : ScalarSixRing.{u}} {X Y U : Scheme.{u}}

/-- The normalized scalar comparison data. Its `thetaNormalization` fixes every hom
component to `scalarSixPullHom`, hence fixes its inverse and the entire data uniquely.
This choice therefore selects no arbitrary comparison. -/
def pbcLocalScalarData : ScalarSixPullbackData.{u} :=
  Classical.choice scalarSixPullbackData_exists

/-- The specified local coefficient comparison: inverse geometric compositor, inverse
scalar comparison, and scalar extension of the given local identification. -/
def pbcLocalReductionComparison (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N) :
    (scalarSixPull Λ' h).obj ((scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj K)) ≅
      (scalarSixChange a U).obj N :=
  ((scalarSixPullComp Λ' h f).app ((scalarSixChange a Y).obj K)).symm ≪≫
    ((pbcLocalScalarData.theta a (h ≫ f)).app K).symm ≪≫
      (scalarSixChange a U).mapIso e

/-- The comparison between a composite scalar change and successive local changes. -/
def pbcLocalReductionTower (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixPull Λ'' h).obj
        ((scalarSixPull Λ'' f).obj ((scalarSixChange (a ≫ b) Y).obj K)) ≅
      (scalarSixChange b U).obj
        ((scalarSixPull Λ' h).obj ((scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj K))) :=
  (scalarSixPull Λ'' f ⋙ scalarSixPull Λ'' h).mapIso
      ((scalarSixTower a b Y).app K).symm ≪≫
    (scalarSixPull Λ'' h).mapIso
      ((pbcLocalScalarData.theta b f).app ((scalarSixChange a Y).obj K)).symm ≪≫
    ((pbcLocalScalarData.theta b h).app
      ((scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj K))).symm

private theorem local_composition (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixPullComp Λ' h f).inv.app ((scalarSixChange a Y).obj K) ≫
        (pbcLocalScalarData.theta a (h ≫ f)).inv.app K =
      (scalarSixPull Λ' h).map ((pbcLocalScalarData.theta a f).inv.app K) ≫
        (pbcLocalScalarData.theta a h).inv.app ((scalarSixPull Λ f).obj K) ≫
          (scalarSixChange a U).map ((scalarSixPullComp Λ h f).inv.app K) := by
  have q := IsIso.inv_eq_inv.mpr (pbcLocalScalarData.composition a h f K)
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    Category.assoc] using q

/-- The specified local comparison equals the iterated inverse-image/scalar comparison. -/
theorem pbcLocalReductionComparison_iterated (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N) :
    (pbcLocalReductionComparison a f h K e).hom =
      (scalarSixPull Λ' h).map ((pbcLocalScalarData.theta a f).inv.app K) ≫
        (pbcLocalScalarData.theta a h).inv.app ((scalarSixPull Λ f).obj K) ≫
          (scalarSixChange a U).map ((scalarSixPullComp Λ h f).inv.app K ≫ e.hom) := by
  dsimp only [pbcLocalReductionComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [← Category.assoc, local_composition]
  simp only [Functor.map_comp, Category.assoc]

/-- Naturality in the specified local identification. -/
theorem pbcLocalReductionComparison_naturality (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    {K K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)}
    {N N' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N)
    (e' : (scalarSixPull Λ (h ≫ f)).obj K' ≅ N') (v : K ⟶ K') (w : N ⟶ N')
    (he : e.hom ≫ w = (scalarSixPull Λ (h ≫ f)).map v ≫ e'.hom) :
    (pbcLocalReductionComparison a f h K e).hom ≫ (scalarSixChange a U).map w =
      (scalarSixPull Λ' h).map ((scalarSixPull Λ' f).map ((scalarSixChange a Y).map v)) ≫
        (pbcLocalReductionComparison a f h K' e').hom := by
  dsimp only [pbcLocalReductionComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp, he, Functor.map_comp]
  have q := (pbcLocalScalarData.theta a (h ≫ f)).inv.naturality v
  dsimp only [Functor.comp_map] at q
  rw [← reassoc_of% q]
  have r := (scalarSixPullComp Λ' h f).inv.naturality ((scalarSixChange a Y).map v)
  dsimp only [Functor.comp_map] at r
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (pbcLocalScalarData.theta a (h ≫ f)).inv.app K' ≫
      (scalarSixChange a U).map e'.hom) r.symm

/-- Scalar-tower compatibility of the local comparison, for arbitrary coefficient maps. -/
theorem pbcLocalReductionComparison_tower (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N) :
    (pbcLocalReductionComparison (a ≫ b) f h K e).hom =
      (pbcLocalReductionTower a b f h K).hom ≫
        (scalarSixChange b U).map (pbcLocalReductionComparison a f h K e).hom ≫
          (scalarSixTower a b U).hom.app N := by
  have q := IsIso.inv_eq_inv.mpr (pbcLocalScalarData.tower a b (h ≫ f) K)
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    Category.assoc] at q
  dsimp only [pbcLocalReductionComparison, pbcLocalReductionTower, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (local_composition b f h ((scalarSixChange a Y).obj K))]
  rw [reassoc_of% ((scalarSixPullComp Λ'' h f).inv.naturality
    ((scalarSixTower a b Y).inv.app K))]
  rw [← reassoc_of% q]
  have r := (scalarSixTower a b U).hom.naturality e.hom
  dsimp only [Functor.comp_map] at r
  rw [r]
  simp only [Iso.inv_hom_id_app_assoc]

/-- Natural local coefficient change under isomorphism transport, with its iterated
formula and scalar-tower coherence. The local map is parametrized as `h: U ⟶ X`;
for a map `g: U ⟶ Y`, take `h = g ≫ f.inv`, since `h ≫ f.hom = g`. -/
theorem pbcIsoLocalComplex_reduction_comparison (a : Λ ⟶ Λ') (f : X ≅ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f.hom)).obj K ≅ N) :
    (pbcLocalReductionComparison a f.hom h K e).hom =
        (scalarSixPull Λ' h).map ((pbcLocalScalarData.theta a f.hom).inv.app K) ≫
          (pbcLocalScalarData.theta a h).inv.app ((scalarSixPull Λ f.hom).obj K) ≫
            (scalarSixChange a U).map
              ((scalarSixPullComp Λ h f.hom).inv.app K ≫ e.hom) ∧
      (∀ {K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)}
        {N' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
        (e' : (scalarSixPull Λ (h ≫ f.hom)).obj K' ≅ N') (v : K ⟶ K') (w : N ⟶ N'),
        e.hom ≫ w = (scalarSixPull Λ (h ≫ f.hom)).map v ≫ e'.hom →
          (pbcLocalReductionComparison a f.hom h K e).hom ≫ (scalarSixChange a U).map w =
            (scalarSixPull Λ' h).map
                ((scalarSixPull Λ' f.hom).map ((scalarSixChange a Y).map v)) ≫
              (pbcLocalReductionComparison a f.hom h K' e').hom) ∧
      (∀ {Λ'' : ScalarSixRing.{u}} (b : Λ' ⟶ Λ''),
        (pbcLocalReductionComparison (a ≫ b) f.hom h K e).hom =
          (pbcLocalReductionTower a b f.hom h K).hom ≫
            (scalarSixChange b U).map (pbcLocalReductionComparison a f.hom h K e).hom ≫
              (scalarSixTower a b U).hom.app N) := by
  exact ⟨pbcLocalReductionComparison_iterated a f.hom h K e,
    fun e' v w he ↦ pbcLocalReductionComparison_naturality a f.hom h e e' v w he,
    fun b ↦ pbcLocalReductionComparison_tower a b f.hom h K e⟩

end AlgebraicGeometry.ProEtale.CondensedRing
