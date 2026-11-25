/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Nakayama

/-! # Affine comparison for the restriction source

## References

* Stacks Project, Tags 01LC, 01HV and 008C
* Stacks Project, Tags 0AV8, 0AVN, 0E9I, 01LC, 05AM and 00LL
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Depth is invariant under a semilinear equivalence of finite modules.
The one-sided regular-sequence transport is applied in both directions. -/
private theorem depth_eq_of_semilinear_equiv
    {R S M P : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [AddCommGroup M] [AddCommGroup P] [Module R M] [Module S P]
    [Module.Finite R M] [Module.Finite S P]
    (e : R ≃+* S) (a : M ≃+ P) (ha : ∀ r m, a (r • m) = e r • a m) :
    IsLocalRing.depth (R := R) M = IsLocalRing.depth (R := S) P := by
  have hle {R S M P : Type u}
      [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
      [AddCommGroup M] [AddCommGroup P] [Module R M] [Module S P]
      [Module.Finite R M] [Module.Finite S P]
      (e : R ≃+* S) (a : M ≃+ P)
      (ha : ∀ r m, a (r • m) = e r • a m) :
      IsLocalRing.depth (R := R) M ≤ IsLocalRing.depth (R := S) P := by
    classical
    cases subsingleton_or_nontrivial P with
    | inl hP =>
      have := hP
      have ht : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P) = ⊤ :=
        Subsingleton.elim _ _
      simp [IsLocalRing.depth, Ideal.depth, ht]
    | inr hP =>
      have := hP
      have : Nontrivial M := a.surjective.nontrivial
      have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _)).symm
      have hP' : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P) ≠ ⊤ :=
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson _)).symm
      simp only [IsLocalRing.depth, Ideal.depth, hM, hP', ↓reduceIte]
      apply sSup_le
      rintro n ⟨rs, hreg, hmem, rfl⟩
      apply le_sSup
      refine ⟨rs.map e, ?_, ?_, by simp⟩
      · apply (a.isRegular_congr ?_).mp hreg
        exact List.forall₂_map_right_iff.mpr
          (List.forall₂_same.mpr (fun r _ m ↦ ha r m))
      · intro r hr
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
        rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
        exact Ideal.mem_map_of_mem e (hmem t ht)
  apply le_antisymm (hle e a ha)
  apply hle e.symm a.symm
  intro r m
  apply a.injective
  simp only [a.apply_symm_apply]
  rw [ha, e.apply_symm_apply, a.apply_symm_apply]



set_option backward.isDefEq.respectTransparency false in
private theorem affine_section_depth
    {L : Scheme.{u}} (N : L.Modules) (hqc : N.IsQuasicoherent)
    (V : L.Opens) (hV : IsAffineOpen V) (y : V)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hp : (hV.primeIdealOf y).asIdeal = p)
    (hfinite : Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hfinitey : Module.Finite (L.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) :
    letI := hfinite
    letI := hfinitey
    IsLocalRing.depth (R := Localization.AtPrime p)
      (LocalizedModule.AtPrime p (N.val.obj (op V))) =
    IsLocalRing.depth (R := L.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) := by
  subst p
  classical
  have := hfinite
  have := hfinitey
  let R := L.presheaf.obj (op V)
  let p := (hV.primeIdealOf y).asIdeal
  let T := TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y
  let : Module R T := Module.compHom _ (L.presheaf.germ V y y.2).hom
  obtain ⟨f, hf, hloc⟩ := isLocalizedModule_affine_germ N hqc V hV y
  have := hloc
  have := hV.isLocalization_stalk y
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (L.presheaf.stalk y)
  let : Module (Localization.AtPrime p) T := Module.compHom T e.toRingHom
  have : IsScalarTower R (Localization.AtPrime p) T :=
    IsScalarTower.of_algebraMap_smul (by
      intro r m
      change e (algebraMap R (Localization.AtPrime p) r) • m =
        L.presheaf.germ V y y.2 r • m
      rw [e.commutes]
      rfl)
  let a := (IsLocalizedModule.iso p.primeCompl f).extendScalarsOfIsLocalization
    p.primeCompl (Localization.AtPrime p)
  exact depth_eq_of_semilinear_equiv e.toRingEquiv a.toAddEquiv
    (fun r m ↦ a.map_smul r m)

private theorem unit_stalk_surjective
    {L : Scheme.{u}} (U : L.Opens) (N : L.Modules) (y : L) (hy : y ∈ U) :
    Function.Surjective (((Modules.toPresheaf L ⋙ stalkFunctor Ab.{u} y).map
      ((Modules.restrictAdjunction U.ι).unit.app N))) := by
  let z : U := ⟨y, hy⟩
  let η := (Modules.restrictAdjunction U.ι).unit.app N
  let F' := Modules.toPresheaf U.toScheme ⋙ stalkFunctor Ab.{u} z
  have : IsIso ((Modules.restrictFunctor U.ι).map η) := inferInstance
  have hi' : IsIso (F'.map ((Modules.restrictFunctor U.ι).map η)) := inferInstance
  have hnat := (Modules.restrictStalkNatIso U.ι z).hom.naturality η
  have : IsIso ((Modules.restrictFunctor U.ι ⋙
      Modules.toPresheaf U.toScheme ⋙ stalkFunctor Ab.{u} z).map η) := hi'
  have : IsIso ((Modules.toPresheaf L ⋙ stalkFunctor Ab.{u} y).map η) :=
    IsIso.of_isIso_fac_left hnat.symm
  exact (ConcreteCategory.bijective_of_isIso
    ((Modules.toPresheaf L ⋙ stalkFunctor Ab.{u} y).map η)).2

set_option backward.isDefEq.respectTransparency false in
private theorem localization_surjective_of_stalk_surjective
    {L : Scheme.{u}} (N G : L.Modules) (η : N ⟶ G)
    (hqc : N.IsQuasicoherent) (hG : G.IsQuasicoherent)
    (V : L.Opens) (hV : IsAffineOpen V) (y : V)
    (hs : Function.Surjective ((Modules.toPresheaf L ⋙ stalkFunctor Ab.{u} (y : L)).map η)) :
    Function.Surjective (LocalizedModule.map (hV.primeIdealOf y).asIdeal.primeCompl
      (η.val.app (op V)).hom) := by
  let R := L.presheaf.obj (op V)
  let T := TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y
  let T' := TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) G.val.presheaf y
  let : Module R T := Module.compHom _ (L.presheaf.germ V y y.2).hom
  let : Module R T' := Module.compHom _ (L.presheaf.germ V y y.2).hom
  obtain ⟨f, hf, hloc⟩ := isLocalizedModule_affine_germ N hqc V hV y
  obtain ⟨g, hg, hloc'⟩ := isLocalizedModule_affine_germ G hG V hV y
  have := hloc
  have := hloc'
  have : IsScalarTower R (L.presheaf.stalk y) T :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have : IsScalarTower R (L.presheaf.stalk y) T' :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let h : T →ₗ[R] T' :=
    ((RingedSpace.moduleStalkMap L.toRingedSpace y η).hom).restrictScalars R
  have hh : IsLocalizedModule.map (hV.primeIdealOf y).asIdeal.primeCompl f g
      (η.val.app (op V)).hom = h := by
    apply IsLocalizedModule.linearMap_ext (hV.primeIdealOf y).asIdeal.primeCompl f g
    ext m
    dsimp only [LinearMap.comp_apply]
    erw [IsLocalizedModule.map_apply, hf, hg]
    exact (stalkFunctor_map_germ_apply V (y : L) y.2 ((Modules.toPresheaf L).map η) m).symm
  have hhs : Function.Surjective h := hs
  exact (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    f g (l := (η.val.app (op V)).hom)).mp (by rw [hh]; exact hhs)

set_option backward.isDefEq.respectTransparency false in
/-- The restriction unit is surjective after localization at an interior prime. -/
private theorem localized_restriction_unit_surjective
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules) (hqc : N.IsQuasicoherent)
    (V : L.Opens) (hV : IsAffineOpen V)
    (y : V) (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime]
    (hp : (hV.primeIdealOf y).asIdeal = p)
    (hy : (y : L) ∈ U) :
    Function.Surjective (LocalizedModule.map p.primeCompl
      (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom) := by
  subst p
  have := hqc
  let G := (Modules.pushforward U.ι).obj ((Modules.restrictFunctor U.ι).obj N)
  have hG : G.IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated U.ι _
  exact localization_surjective_of_stalk_surjective N G _ hqc hG V hV y
    (unit_stalk_surjective U N y hy)

-- The nested subtype and stalk comparisons elaborate several scalar structures.
set_option backward.isDefEq.respectTransparency false in
/-- Affine comparison for the restriction source. -/
theorem affine_restriction_source_depth_comparison
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) 
    (hinj : ∀ V : L.Opens,
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app V))
    (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG)
    (hMS : LinearMap.range
      (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom ≤ S)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime] :
    ∃ hfinite : Module.Finite (Localization.AtPrime p)
      (LocalizedModule.AtPrime p
        ((LinearMap.range
          (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
            S.subtype)),
      letI := hfinite
      (hV.fromSpec ⟨p, inferInstance⟩ ∈ U →
        Subsingleton (LocalizedModule.AtPrime p
          (S ⧸ (LinearMap.range
            (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
              S.subtype))) ∧
      (hV.fromSpec ⟨p, inferInstance⟩ ∉ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
          (LocalizedModule.AtPrime p
            ((LinearMap.range
              (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
                S.subtype))) := by
  classical
  let R := L.presheaf.obj (op V)
  let M := N.val.obj (op V)
  let P := (((Modules.pushforward U.ι).obj
    ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V))
  let a : M →ₗ[R] P :=
    (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom
  let K : Submodule R S := (LinearMap.range a).comap S.subtype
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite R S := Module.Finite.of_fg hS
  have : Module.Finite R K := Module.Finite.of_fg (IsNoetherian.noetherian K)
  have : Module.Finite R M := hsections V hV
  let b : M →ₗ[R] S := a.codRestrict S (fun m ↦ hMS ⟨m, rfl⟩)
  let c : M →ₗ[R] K := b.codRestrict K (fun m ↦ ⟨m, rfl⟩)
  have hcI : Function.Injective c := by
    intro m n h
    apply hinj V
    exact congrArg (fun k : K ↦ (k : S).val) h
  have hcS : Function.Surjective c := by
    rintro ⟨s, m, hm⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hm
  let e := LinearEquiv.ofBijective c ⟨hcI, hcS⟩
  let ep := IsLocalizedModule.mapEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)
    (LocalizedModule.mkLinearMap p.primeCompl K) (Localization.AtPrime p) e
  let y : V := hV.isoSpec.inv ⟨p, inferInstance⟩
  have hp : (hV.primeIdealOf y).asIdeal = p := by
    have he : hV.primeIdealOf y = (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
      change (hV.isoSpec.inv ≫ hV.isoSpec.hom) _ = _
      simp
    exact congrArg PrimeSpectrum.asIdeal he
  have hey : hV.fromSpec ⟨p, inferInstance⟩ = (y : L) := by
    have he := hV.fromSpec_primeIdealOf y
    rw [← he]
    apply congrArg hV.fromSpec
    exact PrimeSpectrum.ext hp.symm
  refine ⟨inferInstance, ?_, ?_⟩
  · intro hy
    have ha := localized_restriction_unit_surjective U N hqc V hV y p hp
      (by simpa only [hey] using hy)
    let i := LocalizedModule.map p.primeCompl S.subtype
    have hi : Function.Injective i :=
      LocalizedModule.map_injective _ _ S.subtype_injective
    have hcomp : i.comp (LocalizedModule.map p.primeCompl b) =
        LocalizedModule.map p.primeCompl a := by
      ext x
      induction x using LocalizedModule.induction_on with
      | h m s =>
        dsimp only [LinearMap.comp_apply, i]
        simp only [LocalizedModule.map_mk]
        exact (LocalizedModule.map_mk p.primeCompl a m s).symm
    have hb : Function.Surjective (LocalizedModule.map p.primeCompl b) := by
      intro s
      obtain ⟨m, hm⟩ := ha (i s)
      refine ⟨m, hi ?_⟩
      exact (LinearMap.congr_fun hcomp m).trans hm
    have hbc : (LocalizedModule.map p.primeCompl K.subtype).comp
        (LocalizedModule.map p.primeCompl c) =
        LocalizedModule.map p.primeCompl b := by
      ext x
      induction x using LocalizedModule.induction_on with
      | h m s =>
        dsimp only [LinearMap.comp_apply]
        simp only [LocalizedModule.map_mk]
        rfl
    have hK : Function.Surjective (LocalizedModule.map p.primeCompl K.subtype) := by
      intro s
      obtain ⟨m, hm⟩ := hb s
      exact ⟨LocalizedModule.map p.primeCompl c m,
        (LinearMap.congr_fun hbc m).trans hm⟩
    let q := LocalizedModule.map p.primeCompl K.mkQ
    have hqS : Function.Surjective q :=
      LocalizedModule.map_surjective _ _ K.mkQ_surjective
    have hex := LocalizedModule.map_exact p.primeCompl K.subtype K.mkQ
      (LinearMap.exact_subtype_mkQ K)
    refine ⟨fun x z ↦ ?_⟩
    have hz (x : LocalizedModule.AtPrime p (S ⧸ K)) : x = 0 := by
      obtain ⟨s, rfl⟩ := hqS x
      obtain ⟨k, hk⟩ := hK s
      exact (hex s).mpr ⟨k, hk⟩
    exact (hz x).trans (hz z).symm
  · intro hy
    obtain ⟨hf, hd⟩ := hdepth y (by simpa only [hey] using hy)
    have heq := affine_section_depth N hqc V hV y p hp (hsections V hV) hf
    have hM : (2 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
        (LocalizedModule.AtPrime p M) := hd.trans_eq heq.symm
    exact hM.trans_eq (depth_eq_of_semilinear_equiv (RingEquiv.refl _) ep.toAddEquiv
      (fun r m ↦ ep.map_smul r m))

end AlgebraicGeometry.Scheme
