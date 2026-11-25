/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.RingTheory.AffineFiniteProjectivePrimeMembership
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Ideal.Maps
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Affine dictionary for an invertible module and its section

Source: literature/stacks-project/schemes.tex, Schemes, Lemmas 01IA and 01IB,
together with Modules, Lemma 01CY (blueprint: lem-sc-affine-cap-section-open-dictionary).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.QuasicoherentTilde

namespace AlgebraicGeometry.Scheme.Modules

private theorem invertible_global_sections
    {R : Type u} [CommRing R]
    (M : (Spec (.of R)).Modules) [M.IsInvertible] :
    Module.Invertible R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M) := by
  let A : Type u := Γ(Spec (.of R), ⊤)
  let N : Type u := Γ(M, ⊤)
  let : Module R N :=
    ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M).isModule
  have : Module.Invertible A N :=
    invertible_sections_of_isAffineOpen M (isAffineOpen_top _)
  let e : A ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let : Algebra A R := e.toRingHom.toAlgebra
  have : IsScalarTower A R N := ⟨fun a r n ↦ by
    change (e a * r) • n = a • (r • n)
    rw [mul_smul, smul_top_eq M]
    change (Scheme.ΓSpecIso (.of R)).inv ((Scheme.ΓSpecIso (.of R)).hom a) •
      (r • n) = a • (r • n)
    rw [Iso.hom_inv_id_apply]⟩
  let ea : A ≃ₐ[A] R := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  have : IsLocalization (⊥ : Submonoid A) A := IsLocalization.self bot_le
  have : IsLocalization (⊥ : Submonoid A) R :=
    IsLocalization.isLocalization_of_algEquiv ⊥ ea
  have := isLocalizedModule_id (⊥ : Submonoid A) N R
  exact Module.Invertible.of_isLocalization (⊥ : Submonoid A) (LinearMap.id : N →ₗ[A] N)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The affine dictionary for an invertible module and a section of it.

Source: literature/stacks-project/schemes.tex, Schemes, Lemmas 01IA and 01IB,
together with Modules, Lemma 01CY (blueprint: lem-sc-affine-cap-section-open-dictionary).
Proof.
1. An invertible module is quasi-coherent. The affine tilde/Gamma counit
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`) identifies M with tilde(Gamma(X,M)).
2. Local rank-one trivializations (`def-sc-invertible-module`) refine to standard opens.
   Quasi-compactness (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`) gives a
   finite cover by D(f_i). On each member, `lem-weil-pbc-spec-module-tilde-sections`
   identifies N localized at f_i with R localized at f_i. The finite-cover converse
   `lem-sc-affine-standard-cover-finite-projective` makes N finite projective.
   Localizing one trivialization containing p gives N_p isomorphic to R_p.
3. `lem-weil-pbc-spec-tilde-stalk-localization` identifies M_p with N_p and the germ
   of s with s/1. Apply `lem-sc-affine-finite-projective-prime-membership` to obtain
   the displayed membership equivalence. The maximal ideal of R_p is pR_p, so
   the stalk criterion in `lem-weil-pbc-nonvanishing-section-trivializes` identifies
   the actual nonvanishing locus of s with the displayed prime-membership set.
-/
theorem affine_cap_section_open_dictionary
    {R : Type u} [CommRing R]
    (M : (Spec (.of R)).Modules) [M.IsInvertible]
    (s : ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) :
    IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) M) ∧
      (Module.Finite R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M) ∧
        Module.Projective R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) ∧
      (∀ (p : Ideal R) [p.IsPrime],
        Nonempty
            (((LocalizedModule p.primeCompl
                ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) ≃ₗ[Localization.AtPrime p]
              (Localization.AtPrime p))) ∧
        (LocalizedModule.mk s 1 ∈
            (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
              (⊤ : Submodule (Localization.AtPrime p)
                (LocalizedModule p.primeCompl
                  ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M))) ↔
          s ∈ p •
            (⊤ : Submodule R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)))) ∧
      (nonvanishingLocus M s =
        {p : PrimeSpectrum R |
          ¬ s ∈ p.asIdeal •
            (⊤ : Submodule R ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M))}) := by
  have : M.IsQuasicoherent := IsInvertible.isQuasicoherent M
  have := invertible_global_sections M
  refine ⟨isIso_fromTildeΓ_of_isQuasicoherent M,
    ⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro p hp
    have : Module.Invertible (Localization.AtPrime p)
        (LocalizedModule p.primeCompl ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj M)) :=
      Module.Invertible.of_isLocalization p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl _)
    exact ⟨Module.Invertible.free_iff_linearEquiv.mp inferInstance,
      Module.prime_mem_localized_iff s p⟩
  · ext p
    let N := (moduleSpecΓFunctor (R := CommRingCat.of R)).obj M
    let K : CommRingCat.{u} := (Spec (.of R)).presheaf.stalk p
    let T : Type u := M.presheaf.stalk p
    let : Module K T := inferInstanceAs
      (Module ((Spec (.of R)).presheaf.stalk p) (M.presheaf.stalk p))
    let : Algebra R K := StructureSheaf.stalkAlgebra R p
    have : IsLocalization.AtPrime K p.asIdeal := StructureSheaf.IsLocalization.to_stalk R p
    let : Module R T := Module.compHom T (algebraMap R K)
    have : IsScalarTower R K T := IsScalarTower.of_compHom R K T
    let c := fromTildeΓ (R := CommRingCat.of R) M
    have : IsIso c := isIso_fromTildeΓ_of_isQuasicoherent M
    let ec : (tilde N).presheaf.stalk p ≃ₗ[K] T :=
      LinearEquiv.ofBijective (c.stalkLinearMap p) (by
        change Function.Bijective
          ((TopCat.Presheaf.stalkFunctor Ab.{u} p).map c.mapPresheaf)
        change Function.Bijective
          (((toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} p).map c))
        exact ConcreteCategory.bijective_of_isIso _)
    let : Module R ((tilde N).presheaf.stalk p) :=
      tilde.instModuleCarrierCarrierStalkAbPresheaf N p
    have : IsScalarTower R K ((tilde N).presheaf.stalk p) := inferInstanceAs
      (IsScalarTower R ((structurePresheafInCommRingCat R).stalk p)
        ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R N).presheaf p))
    let ecR := ec.restrictScalars R
    let g : N →ₗ[R] T := ecR.toLinearMap ∘ₗ (tilde.toStalk N p).hom
    have : IsLocalizedModule p.asIdeal.primeCompl (tilde.toStalk N p).hom :=
      tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
        N p
    have : IsLocalizedModule p.asIdeal.primeCompl g :=
      IsLocalizedModule.of_linearEquiv _ _ ecR
    let e := IsLocalizedModule.iso p.asIdeal.primeCompl g
    have hgs : g s = M.presheaf.germ ⊤ p trivial s := by
      change c.stalkLinearMap p ((tilde N).presheaf.germ ⊤ p trivial
        (tilde.toOpen N ⊤ s)) = _
      erw [Hom.stalkLinearMap_germ]
      have h := toOpen_fromTildeΓ_app (R := CommRingCat.of R) M ⊤
      have hs := congrArg (fun f ↦ f s) h
      simp only [ConcreteCategory.comp_apply] at hs
      change c.app ⊤ (tilde.toOpen N ⊤ s) =
        M.presheaf.map (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)).op s at hs
      rw [show (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)).op =
        𝟙 (op ⊤) from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hs
      exact congrArg (M.presheaf.germ ⊤ p trivial) hs
    have hmax : Ideal.map (algebraMap R K) p.asIdeal = IsLocalRing.maximalIdeal K :=
      IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal K
    have hm : M.presheaf.germ ⊤ p trivial s ∈
        (IsLocalRing.maximalIdeal K) • (⊤ : Submodule K T) ↔
        LocalizedModule.mk s 1 ∈
          (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) •
            (⊤ : Submodule (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl N)) := by
      rw [← hmax]
      change M.presheaf.germ ⊤ p trivial s ∈
        (((Ideal.map (algebraMap R K) p.asIdeal) • (⊤ : Submodule K T)).restrictScalars R) ↔
        LocalizedModule.mk s 1 ∈
        (((Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) •
          (⊤ : Submodule (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl N))).restrictScalars R)
      rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_map_smul_eq,
        Submodule.restrictScalars_top, Submodule.restrictScalars_top, ← hgs,
        ← IsLocalizedModule.iso_mk_one p.asIdeal.primeCompl g s]
      have hmap := Submodule.map_smul'' p.asIdeal (⊤ : Submodule R
        (LocalizedModule p.asIdeal.primeCompl N)) e.toLinearMap
      rw [Submodule.map_top, LinearEquiv.range] at hmap
      rw [← hmap, Submodule.mem_map_equiv]
      change e.symm (e (LocalizedModule.mk s 1)) ∈ _ ↔ _
      rw [LinearEquiv.symm_apply_apply]
    change ¬ _ ↔ ¬ _
    exact not_congr (hm.trans (Module.prime_mem_localized_iff s p.asIdeal))

end AlgebraicGeometry.Scheme.Modules
