/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
import WeilConjectures.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import all WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Pseudo-coherent complexes of locally finite Tor dimension are perfect

Source: Stacks Project, Cohomology of Sheaves, Tag 08CQ, implication (2) to (1).
(blueprint: lem-pc-pseudo-coherent-locally-finite-tor-perfect).
-/

@[expose] public section

universe uP wP

open CategoryTheory

namespace AlgebraicGeometry.Scheme

theorem isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension (S : Scheme.{uP})
    [HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} ((moduleRings S.toRingedSpace).over U))]
    [∀ W : S.Opens,
      HasDerivedCategory.{wP} (SheafOfModules.{uP} (moduleRings W.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : IsPseudoCoherent S K)
    (hTor : HasLocallyFiniteTorDimension S K) : IsPerfect S K := by
  intro x
  obtain ⟨U, hxU, P, hb, hf, ⟨eP⟩⟩ := hK x
  obtain ⟨W, hxW, a, c, hac, hW⟩ := hTor x
  obtain ⟨V, hV, hxV, hVUW⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ W) ⟨hxU, hxW⟩
  have hVU : V ≤ U := hVUW.trans inf_le_left
  have hVW : V ≤ W := hVUW.trans inf_le_right
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
  obtain ⟨M, b, hMb, hMf, ⟨eM⟩⟩ := affine_finiteFree_model S V hV PV hbV hfV
  let R := S.presheaf.obj (.op V)
  let : HasDerivedCategory (ModuleCat.{uP} R) := HasDerivedCategory.standard _
  have hMpc : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
    ⟨M, b, hMb, hMf, ⟨Iso.refl _⟩⟩
  let eKM := eV ≪≫ (DerivedCategory.Q.mapIso eM).symm
  have hMtor := finiteTorAmplitude_of_affine_sheafification_of_open_tor S V hV K M ⟨eKM⟩
    W hVW ⟨a, c, hac, hW⟩
  obtain ⟨E, hEb, hEf, hEp, ⟨eE⟩⟩ :=
    DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude
      (DerivedCategory.Q.obj M) hMpc hMtor
  let T := (affinePerfectSheafification S V hV).mapHomologicalComplex (.up ℤ)
  obtain ⟨D, _, ⟨c⟩⟩ := affine_localized_derived_sheafification S V hV
  refine ⟨V, hxV, T.obj E, affine_projective_strictlyPerfect S V hV E hEb hEf hEp, ?_⟩
  exact ⟨eKM ≪≫ (c.app M).symm ≪≫ D.mapIso eE.symm ≪≫ c.app E⟩

end AlgebraicGeometry.Scheme
