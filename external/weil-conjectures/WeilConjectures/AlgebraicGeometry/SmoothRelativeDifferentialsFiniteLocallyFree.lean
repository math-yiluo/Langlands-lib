/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Finite local freeness of smooth relative differentials

Source: Stacks Project, Tag 02G1.
(blueprint: lem-ag-smooth-relative-differentials-finite-locally-free)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

/-- Relative differentials of a smooth morphism are finite locally free, without a
constant relative dimension assumption. Source: Stacks Project, Tag 02G1.

Proof: choose standard smooth affine charts at each point. Their differential modules
are finite free. The affine comparison for relative differentials identifies these with
restrictions of the differential sheaf, and finite local freeness descends along the cover.

(blueprint: lem-ag-smooth-relative-differentials-finite-locally-free) -/
theorem isFiniteLocallyFree_relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : f.relativeDifferentials.IsFiniteLocallyFree := by
  choose U hU V hV hx e hsm using fun x ↦
    Smooth.exists_isStandardSmooth f x
  refine Modules.isFiniteLocallyFree_of_isOpenImmersion _ (fun x ↦ (hV x).fromSpec)
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2
      ⟨x, by rw [IsAffineOpen.opensRange_fromSpec]; exact hx x⟩) fun x ↦ ?_
  let φ := f.appLE (U x) (V x) (e x)
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(S, U x) Γ(X, V x) := hsm x
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := this
  have : Finite ι := hι
  have : Finite σ := hσ
  let d := P.dimension
  have : Algebra.IsStandardSmoothOfRelativeDimension d Γ(S, U x) Γ(X, V x) :=
    P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨eΩ⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential
      (R := Γ(S, U x)) (S := Γ(X, V x)) d
  let N := (Spec.map φ).relativeDifferentials
  let T : (Modules.pullback (hV x).fromSpec).obj f.relativeDifferentials ≅ N :=
    ((Modules.restrictFunctorIsoPullback _).app _).symm ≪≫
      f.relativeDifferentialsRestrictIso (hV x).fromSpec ≪≫
      relativeDifferentialsCongr _
        (IsAffineOpen.SpecMap_appLE_fromSpec f (hU x) (hV x) (e x)).symm ≪≫
      relativeDifferentialsCompIso _ _
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, V x)).ringCatSheaf).prop_of_iso
      (relativeDifferentialsSpecIso φ).symm
      (inferInstanceAs (tilde (CommRingCat.KaehlerDifferential φ)).IsQuasicoherent)
  let E : Γ(N, ⊤) ≃ₗ[Γ(X, V x)] (Fin d → Γ(X, V x)) :=
    (relativeDifferentialsSpecΓIso φ).toLinearEquiv ≪≫ₗ eΩ
  have : Module.FinitePresentation Γ(X, V x) Γ(N, ⊤) := .of_equiv E.symm
  have : Module.Flat Γ(X, V x) Γ(N, ⊤) := .of_linearEquiv E
  have : N.IsFiniteLocallyFreeOfRank d :=
    Modules.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq N fun p ↦ by
      have := p.nontrivial
      rw [congr_fun (Module.rankAtStalk_eq_of_equiv E) p, Module.rankAtStalk_eq_finrank_of_free]
      simp
  have : N.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N d
  exact SheafOfModules.IsFiniteLocallyFree.of_iso (R := (Spec Γ(X, V x)).ringCatSheaf) T.symm

end AlgebraicGeometry.Scheme.Hom
