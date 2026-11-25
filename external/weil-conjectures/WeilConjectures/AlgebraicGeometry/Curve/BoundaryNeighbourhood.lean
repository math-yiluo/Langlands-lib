/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Affine neighbourhoods of a closed point of a smooth curve

Let `C` be an integral scheme smooth of relative dimension one over a field. The ring of
sections `Γ(C, W)` over a nonempty affine open is a Dedekind domain
(`AlgebraicGeometry.isDedekindDomain_of_isAffineOpen`), and every closed point `z` has arbitrarily
small affine neighbourhoods `W` on which it is cut out by a single function `ϖ`: `W ∖ {z}` is the
basic open `D(ϖ)` (`AlgebraicGeometry.exists_isAffineOpen_basicOpen_eq`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
  [IsIntegral C]

include f in
/-- The sections of a smooth curve over a nonempty affine open form a Dedekind domain. -/
lemma isDedekindDomain_of_isAffineOpen {U : C.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDedekindDomain Γ(C, U) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(C, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hdimC := IsCurve.krullDim_le_one (f := f)
  have : IsIntegrallyClosed Γ(C, U) :=
    Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk
      (isIntegrallyClosed_stalk_of_smooth f hdimC) U
  have hdim : ringKrullDim Γ(C, U) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      hU.isoSpec.hom.homeomorph.isHomeomorph).symm.trans_le
      ((topologicalKrullDim_subspace_le C U).trans hdimC)
  have : Ring.KrullDimLE 1 Γ(C, U) := Ring.krullDimLE_iff.mpr (by exact_mod_cast hdim)
  have : Ring.DimensionLEOne Γ(C, U) :=
    ⟨fun {p} hp hp' ↦ Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this p hp hp'⟩
  exact { }

omit [IsCurve f] [Smooth f] [IsIntegral C] in
/-- A point of an affine open lies in the basic open of a section iff the section is not in its
prime ideal. -/
lemma IsAffineOpen.mem_basicOpen_iff {U : C.Opens} (hU : IsAffineOpen U) (x : U) (g : Γ(C, U)) :
    (x : C) ∈ C.basicOpen g ↔ g ∉ (hU.primeIdealOf x).asIdeal := by
  have h : (hU.primeIdealOf x : Spec Γ(C, U)) ∈ hU.fromSpec ⁻¹ᵁ C.basicOpen g ↔ _ :=
    Iff.of_eq (congrArg (_ ∈ ·) (hU.fromSpec_preimage_basicOpen g))
  have e : hU.fromSpec (hU.primeIdealOf x) = x := hU.fromSpec_primeIdealOf x
  change hU.fromSpec (hU.primeIdealOf x) ∈ C.basicOpen g ↔ _ at h
  rw [e] at h
  exact h

include f in
/-- **Small neighbourhoods cutting out a closed point.** A closed point `z` of a smooth curve has
affine neighbourhoods `W` inside any given open on which it is the zero locus of a single section:
`W ∖ {z} = D(ϖ)`. -/
lemma exists_isAffineOpen_basicOpen_eq [SmoothOfRelativeDimension 1 f] {z : C}
    (hz : IsClosed ({z} : Set C)) (O : C.Opens) (hzO : z ∈ O) :
    ∃ (W : C.Opens) (_ : IsAffineOpen W) (_ : z ∈ W) (ϖ : Γ(C, W)), W ≤ O ∧
      ∀ x ∈ W, x ∈ C.basicOpen ϖ ↔ x ≠ z := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsRegular.of_smooth f
  have : IsDiscreteValuationRing (C.presheaf.stalk z) :=
    IsRegularLocalRing.isDiscreteValuationRing _
      (ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one f hz)
  obtain ⟨⟨U₀, hU₀⟩, hzU₀, s, -, hs⟩ := exists_affineOpen_isRegularPrincipal_vanishingIdeal hz
  replace hU₀ : IsAffineOpen U₀ := hU₀
  let z₀ : U₀ := ⟨z, hzU₀⟩
  -- the vanishing ideal of `z` on `U₀` is the prime ideal of `z`
  have hJU : (Scheme.IdealSheafData.vanishingIdeal ⟨{z}, hz⟩).ideal ⟨U₀, hU₀⟩ =
      (hU₀.primeIdealOf z₀).asIdeal := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    have : hU₀.fromSpec ⁻¹' {z} = {hU₀.primeIdealOf z₀} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hy
        apply hU₀.fromSpec.isOpenEmbedding.injective
        rw [hy, hU₀.fromSpec_primeIdealOf]
      · rintro rfl; exact hU₀.fromSpec_primeIdealOf z₀
    erw [this]
    exact PrimeSpectrum.vanishingIdeal_singleton _
  rw [hJU] at hs
  -- `z` is the only zero of `s` on `U₀`
  have hs0 (x : U₀) : (x : C) ∈ C.basicOpen s ↔ (x : C) ≠ z := by
    rw [hU₀.mem_basicOpen_iff, not_iff_comm, not_not]
    constructor
    · intro h
      rw [show x = z₀ from Subtype.ext h]
      exact hs ▸ Ideal.mem_span_singleton_self s
    · intro hsx
      have hle : (hU₀.primeIdealOf z₀).asIdeal ≤ (hU₀.primeIdealOf x).asIdeal := by
        rw [hs, Ideal.span_le]
        simpa using hsx
      have hsp : hU₀.primeIdealOf z₀ ⤳ hU₀.primeIdealOf x :=
        (PrimeSpectrum.le_iff_specializes _ _).1 hle
      have := hsp.map hU₀.fromSpec.continuous
      rw [hU₀.fromSpec_primeIdealOf, hU₀.fromSpec_primeIdealOf] at this
      exact (this.mem_closed hz rfl : (x : C) ∈ ({z} : Set C))
  -- shrink to a basic open inside `O`
  obtain ⟨h, hhle, hzh⟩ := hU₀.exists_basicOpen_le (V := U₀ ⊓ O) ⟨z, hzU₀, hzO⟩ hzU₀
  refine ⟨C.basicOpen h, hU₀.basicOpen h, hzh,
    C.presheaf.map (homOfLE (C.basicOpen_le h)).op s, hhle.trans inf_le_right, fun x hx ↦ ?_⟩
  rw [Scheme.basicOpen_res]
  have hxU₀ : x ∈ U₀ := C.basicOpen_le h hx
  exact ⟨fun h' ↦ (hs0 ⟨x, hxU₀⟩).1 h'.2, fun h' ↦ ⟨hx, (hs0 ⟨x, hxU₀⟩).2 h'⟩⟩

end AlgebraicGeometry
