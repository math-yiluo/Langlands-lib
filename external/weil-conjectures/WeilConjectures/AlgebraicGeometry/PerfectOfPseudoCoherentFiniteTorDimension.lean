/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
import WeilConjectures.AlgebraicGeometry.AffineSheafificationTorAmplitude
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Finiteness.Projective
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Pseudo-coherent complexes of finite Tor dimension are perfect

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.5, Tag 08CQ
(blueprint: lem-pc-pseudo-coherent-finite-tor-perfect).
-/

@[expose] public section

universe uP wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem affine_free_iso (S : Scheme.{uP}) (U : S.Opens)
    (hU : IsAffineOpen U) (m : ℕ) :
    Nonempty ((affinePerfectSheafification S U hU).obj
      (ModuleCat.of (S.presheaf.obj (.op U))
        (ULift.{uP} (Fin m) →₀ (S.presheaf.obj (.op U)))) ≅
      SheafOfModules.free (R := (moduleRings S.toRingedSpace).over U)
        (ULift.{uP} (Fin m))) := by
  let R := S.presheaf.obj (.op U)
  let F := Modules.restrictFunctor hU.isoSpec.hom
  let G := (Modules.overEquiv U).inverse
  have : F.IsLeftAdjoint := (Modules.restrictAdjunction hU.isoSpec.hom).isLeftAdjoint
  let eF := (SheafOfModules.mapFreeIso F (ULift.{uP} (Fin m))
    (Modules.restrictUnitIso hU.isoSpec.hom).symm).symm
  let eG := (SheafOfModules.mapFreeIso G (ULift.{uP} (Fin m))
    (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf).symm).symm
  exact ⟨G.mapIso (F.mapIso (tildeFinsupp (R := R) (ULift.{uP} (Fin m))) ≪≫ eF) ≪≫ eG⟩

private theorem affine_finiteFree_model_private (S : Scheme.{uP}) (U : S.Opens)
    (hU : IsAffineOpen U)
    (P : CochainComplex
      (SheafOfModules.{uP} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (P.X i))
    (hf : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{uP} (Fin r)))) :
    ∃ M : CochainComplex (ModuleCat.{uP} (S.presheaf.obj (.op U))) ℤ,
      ∃ b : ℤ, M.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Free (S.presheaf.obj (.op U)) (M.X i) ∧
          Module.Finite (S.presheaf.obj (.op U)) (M.X i)) ∧
        Nonempty (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj M
          ≅ P) := by
  classical
  let R := S.presheaf.obj (.op U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  have : rF.IsEquivalence := e.isEquivalence_functor
  let F := affinePerfectSheafification S U hU
  have : F.Full := by unfold F affinePerfectSheafification; infer_instance
  have : F.Faithful := by unfold F affinePerfectSheafification; infer_instance
  choose r hr using hf
  let X (i : ℤ) := ModuleCat.of R (ULift.{uP} (Fin (r i)) →₀ R)
  let ei (i : ℤ) : F.obj (X i) ≅ P.X i :=
    (affine_free_iso S U hU (r i)).some ≪≫ (hr i).some.symm
  let d (i j : ℤ) : X i ⟶ X j := F.preimage ((ei i).hom ≫ P.d i j ≫ (ei j).inv)
  have hd (i j : ℤ) : F.map (d i j) = (ei i).hom ≫ P.d i j ≫ (ei j).inv :=
    F.map_preimage _
  let M : CochainComplex (ModuleCat.{uP} R) ℤ :=
    { X := X
      d := d
      shape := by
        intro i j hij
        apply F.map_injective
        rw [hd, P.shape i j hij]
        simp
      d_comp_d' := by
        intro i j k _ _
        apply F.map_injective
        rw [Functor.map_comp, hd, hd]
        simp [Category.assoc] }
  let eC : (F.mapHomologicalComplex (.up ℤ)).obj M ≅ P :=
    HomologicalComplex.Hom.isoOfComponents ei (by
      intro i j _
      change (ei i).hom ≫ P.d i j = F.map (d i j) ≫ (ei j).hom
      rw [hd]
      simp)
  obtain ⟨b, hb⟩ := hb
  refine ⟨M, b, ?_, fun _ ↦ ⟨inferInstance, inferInstance⟩, ⟨eC⟩⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply F.map_injective
  rw [F.map_id, F.map_zero]
  exact ((ei i).isZero_iff.mpr (hb i hi)).eq_of_src _ _

/-- Public export of the private `affine_finiteFree_model_private`
(used by `import all` importers; linter.privateModule). -/
alias affine_finiteFree_model := affine_finiteFree_model_private

set_option backward.isDefEq.respectTransparency false in
private theorem affine_projective_strictlyPerfect_private (S : Scheme.{uP}) (U : S.Opens)
    (hU : IsAffineOpen U)
    (P : CochainComplex (ModuleCat.{uP} (S.presheaf.obj (.op U))) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → Limits.IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite (S.presheaf.obj (.op U)) (P.X n))
    (hp : ∀ n : ℤ, Module.Projective (S.presheaf.obj (.op U)) (P.X n)) :
    IsStrictlyPerfect S U
      (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let R := S.presheaf.obj (.op U)
  let F := affinePerfectSheafification S U hU
  constructor
  · obtain ⟨a, b, hab⟩ := hb
    exact ⟨a, b, fun n hn ↦ F.map_isZero (hab n hn)⟩
  · intro n
    have : Module.Finite R (P.X n) := hf n
    have : Module.Projective R (P.X n) := hp n
    obtain ⟨m, f, g, _, _, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R (P.X n)
    let c := ((Pi.basisFun R (Fin m)).reindex Equiv.ulift.symm).repr.toModuleIso
    let e := F.mapIso c ≪≫ (affine_free_iso S U hU m).some
    have hsplit : (ModuleCat.ofHom g) ≫ (ModuleCat.ofHom f) = 𝟙 (P.X n) := by
      ext a
      exact congrArg (fun h : (P.X n) →ₗ[R] (P.X n) ↦ h a) hfg
    refine ⟨m, F.map (ModuleCat.ofHom g) ≫ e.hom,
      e.inv ≫ F.map (ModuleCat.ofHom f), ?_⟩
    change (F.map (ModuleCat.ofHom g) ≫ e.hom) ≫
      e.inv ≫ F.map (ModuleCat.ofHom f) = 𝟙 (F.obj (P.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp]
    rw [hsplit, F.map_id]

/-- A pseudo-coherent derived object of finite Tor dimension is perfect.
Source: Stacks Project, Cohomology of Sheaves, Lemma 20.49.5 (08CQ)
(blueprint: lem-pc-pseudo-coherent-finite-tor-perfect).

Proof:
1. Choose global Tor bounds `[a,b]`. Perfectness is local
(`lemma-coherent-base-change-invertible-sheaves--1`).
   Pseudo-coherence (`def-pur-pseudo-coherent-complex`) gives local bounded-above
   finite free representatives; refine to affine opens. Restriction of derived tensor
   (`lem-pc-affine-derived-pullback-tensor-tilde`, part 1), testing with the pushforward
   of any module on an open, preserves the same Tor bounds.
2. On an affine open `Spec R`, sections of the structure sheaf are `R`
   (`lem-weil-pbc-spec-module-tilde-sections`). The finite free terms and their matrix
   differentials therefore come from a bounded-above finite free R-module complex P.
   The tilde functor is exact and faithful by its localization description and recovery
   of modules by global sections. The tensor comparison
   (`lem-pc-affine-derived-pullback-tensor-tilde`, part 3) transfers the Tor bounds to P.
   The ring criterion (`lem-pc-ring-pseudo-coherent-finite-tor-perfect`) gives a bounded
   finite projective complex isomorphic to P in D(R).
3. Exact tilde carries the quasi-isomorphisms in this derived isomorphism to
   quasi-isomorphisms of sheaf complexes. Finite projective terms sheafify to direct
   summands of finite free sheaves. Thus the resulting complex is strictly perfect,
   and the local characterization (`lemma-coherent-base-change-invertible-sheaves--1`) proves
   perfectness. -/
theorem isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension (S : Scheme.{uP})
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPseudoCoherent S K)
    (hTor : HasFiniteTorDimension S K) : IsPerfect S K := by
  intro x
  obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hK x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := U) hxU
  let F := SheafOfModules.overMap.{uP} (moduleRings S.toRingedSpace) (homOfLE hVU)
  let G := SheafOfModules.overFunctor.{uP} (moduleRings S.toRingedSpace) U
  let PV := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hbV : ∃ N : ℤ, ∀ i : ℤ, N < i → Limits.IsZero (PV.X i) := by
    obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun i hi ↦ F.map_isZero (hN i hi)⟩
  have hfV (i : ℤ) : ∃ r : ℕ, Nonempty (PV.X i ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over V) (ULift.{uP} (Fin r))) := by
    obtain ⟨r, ⟨e⟩⟩ := hf i
    let ef : F.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{uP} (Fin r))) ≅
        SheafOfModules.free
          (R := (moduleRings S.toRingedSpace).over V) (ULift.{uP} (Fin r)) :=
      (asIso (Limits.sigmaComparison F (fun _ : ULift.{uP} (Fin r) ↦
        SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)))).symm ≪≫
          Limits.Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso
            (R := moduleRings S.toRingedSpace) (homOfLE hVU))
    exact ⟨r, ⟨F.mapIso e ≪≫ ef⟩⟩
  have : Limits.PreservesFiniteLimits (G ⋙ F) := Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteColimits (G ⋙ F) := Limits.comp_preservesFiniteColimits _ _
  let eV : (SheafOfModules.overFunctor.{uP}
      (moduleRings S.toRingedSpace) V).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj PV :=
    (Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{uP}
        (moduleRings S.toRingedSpace) (homOfLE hVU))).symm.app K ≪≫
      (Functor.mapDerivedCategoryCompIso G F).symm.app K ≪≫ F.mapDerivedCategory.mapIso eP ≪≫
        F.mapDerivedCategoryFactors.app P
  obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_finiteFree_model_private S V hV PV hbV hfV
  let R := S.presheaf.obj (.op V)
  let : HasDerivedCategory (ModuleCat.{uP} R) := HasDerivedCategory.standard _
  have hMpc : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
    ⟨M, b, hMb, hMf, ⟨Iso.refl _⟩⟩
  let eKM := eV ≪≫ (DerivedCategory.Q.mapIso eM).symm
  have hMtor := finiteTorAmplitude_of_affine_sheafification S V hV K M ⟨eKM⟩ hTor
  obtain ⟨E, hEb, hEf, hEp, ⟨eE⟩⟩ :=
    DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude
      (DerivedCategory.Q.obj M) hMpc hMtor
  let T := (affinePerfectSheafification S V hV).mapHomologicalComplex (.up ℤ)
  obtain ⟨D, _, ⟨c⟩⟩ := affine_localized_derived_sheafification S V hV
  refine ⟨V, hxV, T.obj E, affine_projective_strictlyPerfect_private S V hV E hEb hEf hEp, ?_⟩
  exact ⟨eKM ≪≫ (c.app M).symm ≪≫ D.mapIso eE.symm ≪≫ c.app E⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
/-- Public export of the private `affine_projective_strictlyPerfect_private` (used by `import all`
importers; linter.privateModule). -/
alias affine_projective_strictlyPerfect := affine_projective_strictlyPerfect_private

end AlgebraicGeometry.Scheme
