/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Constructible generators under the specified native encoding
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace AlgebraicGeometry.ProEtale.NativeEncoding

private noncomputable def regularIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).obj (Mod.regular (adicConstantSheaf l T)) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T) :=
  (Mod.comap (coefficientIso l T).hom).mapIso
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) ≪≫
      (Mod.regularIsoComapRegular (coefficientIso l T).hom).symm

private noncomputable def freeIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (r : ℕ) :
    (encoding l T).obj (Mod.finiteFree (adicConstantSheaf l T) r) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) T) r :=
  (encoding l T).mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ regularIso l T

private noncomputable def rawPullbackIso (l : ℕ) [Fact l.Prime]
    {S T : Scheme.{u}} (f : S ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)) :
    (Mod.comap (condensedPullbackHom (Profinite.padicAlgClRingObj l) f)).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) ≅
      ((upperStar Ab.{u + 1} f).mapMod _).obj M := by
  let α := condensedPullbackHom (Profinite.padicAlgClRingObj l) f
  exact (Mod.comap α).mapIso
      ((Mod.extendScalarsIsoComapInv α).app _) ≪≫
    ((Mod.comapComp α (inv α)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id α) ≪≫ Mod.comapId _).app _

private theorem lisse_localPresentation (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (M : AdicSheaf l T) (hM : IsAdicLisseSheaf M) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj l) T)
      ((encoding l T).obj M) := by
  classical
  have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
    inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
  obtain ⟨R, hR, H⟩ := hM
  obtain ⟨V, hV⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  let U := V.restrictIndexOfSmall.{u}
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨r, ⟨e⟩⟩ := H (U.f i) (by
    rw [hV]
    exact V.presieve₀_f (Precoverage.ZeroHypercover.Small.restrictFun V i))
  let d := (pullComparison l (U.f i)).symm.app M ≪≫
    (encoding l (U.X i)).mapIso e ≪≫ freeIso l (U.X i) r
  have hfree : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i))
      (Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r) :=
    ⟨r, r, 0, ⟨(cokernelZeroIsoTarget (X := Mod.finiteFree _ r)
      (Y := Mod.finiteFree _ r)).symm⟩⟩
  have hd := Mod.IsFinitelyPresented.of_iso d.symm hfree
  exact Mod.IsFinitelyPresented.of_iso (rawPullbackIso l (U.f i) _)
    (hd.comap (condensedPullbackHom (Profinite.padicAlgClRingObj l) (U.f i)))

private theorem constructible_encoding (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [IsNoetherian T] (M : AdicSheaf l T)
    (hM : IsAdicConstructibleSheaf M) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj l) T)
      ((encoding l T).obj M) := by
  classical
  obtain ⟨idx, hι, Z, j, hj, hc, H, hL⟩ := hM.isAdicStratifiedLisseSheaf
  have := hι
  let := Fintype.ofFinite idx
  let e := (Fintype.equivFin idx).symm
  let S : Scheme.Stratification T :=
    { n := Fintype.card idx
      stratum := fun a ↦ Set.range (j (e a)).base
      isLocallyClosed_stratum := fun a ↦ by
        have := hj (e a)
        exact (j (e a)).isLocallyClosed_range
      isConstructible_stratum := fun a ↦ hc (e a)
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨a, ha, _⟩ := H x
        refine Set.mem_iUnion.mpr ⟨e.symm a, ?_⟩
        rw [e.apply_symm_apply]
        exact ha
      pairwise_disjoint_stratum := by
        intro a b hab
        apply Set.disjoint_left.mpr
        intro x ha hb
        exact hab (e.injective ((H x).unique ha hb))
      domain := fun a ↦ Z (e a)
      immersion := fun a ↦ j (e a)
      isImmersion := fun a ↦ hj (e a)
      range_immersion := fun _ ↦ rfl }
  refine ⟨S, fun a ↦ ?_⟩
  have h := lisse_localPresentation l (S.domain a)
    ((adicUpperStar l (S.immersion a)).obj M) (hL (e a))
  have h' := localFinitePresentation_of_iso ((pullComparison l (S.immersion a)).app M) h
  exact localFinitePresentation_of_iso (rawPullbackIso l (S.immersion a) _)
    (localFinitePresentation_comap
      (condensedPullbackHom (Profinite.padicAlgClRingObj l) (S.immersion a)) h')

/-- The specified native coefficient encoding takes bounded native constructible
complexes to bounded constructible complexes of condensed module objects. -/
theorem encoding_boundedConstructible (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [IsNoetherian T] :
    DerivedCategory.boundedAdicConstructible l T ≤
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T)).inverseImage
        (derivedEncoding l T) := by
  intro K hK
  refine ⟨(encoding l T).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact (constructible_encoding l T _ (hK.2 n)).of_iso
    (((encoding l T).mapDerivedCategoryHomologyFunctorIso n).app K)

end AlgebraicGeometry.ProEtale.NativeEncoding
