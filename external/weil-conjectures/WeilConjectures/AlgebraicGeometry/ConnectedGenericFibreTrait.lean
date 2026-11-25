/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.GenericFibreAffineRingModels
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Connectedness of the generic fibre of a flat degeneration

Source: Stacks Project, Tag 055J.
-/

@[expose] public section

universe u
open CategoryTheory IsLocalRing
namespace AlgebraicGeometry

private theorem generic_nonempty {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] [Nonempty X] :
    Nonempty (f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) := by
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have hη : η ⤳ f x := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hy, hyf⟩ := Flat.generalizingMap f hη
  exact ⟨(f.fiberHomeo η).symm ⟨y, hyf⟩⟩

private theorem generic_injective {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] (U : X.Opens) :
    Function.Injective ((f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).app U) := by
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let g := (Spec (.of R)).fromSpecResidueField η
  have : IsDominant g := by
    rw [isDominant_iff, denseRange_iff_closure_range, Scheme.range_fromSpecResidueField]
    apply Set.eq_univ_of_forall
    intro y
    exact (PrimeSpectrum.le_iff_mem_closure η y).mp bot_le
  have : IsSchemeTheoreticallyDominant g := .of_isDominant g
  have : QuasiCompact g := inferInstance
  have : IsSchemeTheoreticallyDominant (f.fiberι η) := by
    dsimp [Scheme.Hom.fiberι]
    infer_instance
  have : QuasiCompact (f.fiberι η) := by
    dsimp [Scheme.Hom.fiberι]
    infer_instance
  exact (f.fiberι η).app_injective U

private theorem generic_affine_extension {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [IsReduced (f.fiber (closedPoint R))] (U : X.affineOpens)
    (e : Γ(f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R),
      (f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) ⁻¹ᵁ U.1))
    (he : IsIdempotentElem e) :
    ∃ s : Γ(X, U.1), (f.fiberι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)).app U.1 s = e := by
  let ρ := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U.1 le_top
  let : Algebra R Γ(X, U.1) := ρ.hom.toAlgebra
  have hflat : ρ.hom.Flat :=
    (RingHom.Flat.of_bijective
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective).comp
        (f.flat_appLE (isAffineOpen_top _) U.2 le_top)
  have : Module.Flat R Γ(X, U.1) := RingHom.flat_algebraMap_iff.mp hflat
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨hred, ε, hε⟩ := generic_fibre_affine_ring_models f U π hπ
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem
    hπ hred (he.map ε.toRingHom)
  exact ⟨b, ε.injective ((hε b).trans hb)⟩

/-- A connected flat scheme over a DVR with reduced closed fibre has connected generic fibre.

Source: Stacks Project, Tag 055J.
Proof: Write π for a uniformizer. If the generic fibre were disconnected, its structure
sheaf would have a nontrivial idempotent e. On an affine open Spec A of the total space,
flatness makes π a nonzerodivisor, and the generic fibre has coordinate ring A[1/π].
Write the restriction of e as z/π^n with n minimal. The equation e² = e gives
z² = π^n z in A by flatness. If n were positive, z modulo π would be nilpotent in
A/πA. Reducedness of the closed fibre implies z is divisible by π, contradicting
minimality. Thus e extends to A. These extensions are unique because π is a
nonzerodivisor; they agree on overlaps and glue to a global idempotent. Connectedness
of the total space forces that idempotent to be zero or one, contradicting the choice
of e. Flatness and nonemptiness of the total space ensure the generic fibre is nonempty:
every nonzero flat R-algebra embeds into its localization at π.
(blueprint: lem-sbc-connected-generic-fibre-trait) -/
theorem connectedSpace_generic_fibre_of_flat_trait {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [ConnectedSpace X] [IsReduced (f.fiber (closedPoint R))] :
    ConnectedSpace (f.fiber (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) := by
  classical
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let i := f.fiberι η
  have : Nonempty (f.fiber η) := generic_nonempty f
  apply (Scheme.connectedSpace_iff_isIdempotentElem (f.fiber η)).mpr
  intro e he
  let V (U : X.affineOpens) := i ⁻¹ᵁ U.1
  let eU (U : X.affineOpens) : Γ(f.fiber η, V U) :=
    (f.fiber η).presheaf.map (homOfLE le_top).op e
  choose s hs using fun U : X.affineOpens ↦
    generic_affine_extension f U (eU U)
      (he.map ((f.fiber η).presheaf.map (homOfLE le_top).op).hom)
  have key (U : X.affineOpens) (W : X.Opens) (h : W ≤ U.1) :
      i.app W (X.presheaf.map (homOfLE h).op (s U)) =
        (f.fiber η).presheaf.map (homOfLE le_top).op e := by
    rw [← CommRingCat.comp_apply, i.naturality]
    rw [CommRingCat.comp_apply, hs U]
    dsimp [eU]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing'
    (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge s fun U W ↦ by
      apply generic_injective f (U.1 ⊓ W.1)
      exact (key U _ inf_le_left).trans (key W _ inf_le_right).symm
  have hbe : i.appTop b = e := by
    apply (f.fiber η).sheaf.eq_of_locally_eq' V ⊤ (fun _ ↦ homOfLE le_top)
      (show ⊤ ≤ ⨆ U, V U from by
        rw [← Scheme.Hom.preimage_iSup, (iSup_affineOpens_eq_top X)]
        simp) _ _
    intro U
    change (f.fiber η).presheaf.map (homOfLE le_top).op (i.appTop b) = eU U
    rw [← hs U, ← hb U]
    symm
    change (X.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op ≫ i.app U.1) b = _
    rw [i.naturality]
    rfl
  have hbid : IsIdempotentElem b := by
    apply generic_injective f ⊤
    change i.appTop (b * b) = i.appTop b
    simpa only [map_mul, hbe] using he.eq
  rcases (Scheme.connectedSpace_iff_isIdempotentElem X).mp inferInstance b hbid with h | h
  · left
    rw [← hbe, h, map_zero]
  · right
    rw [← hbe, h, map_one]

end AlgebraicGeometry
