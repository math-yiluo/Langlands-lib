/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.RingTheory.DiscreteValuationRing.Dominating

/-!
# Tracing a strict specialization in a locally noetherian scheme

Source: Stacks Project, Tag 054F.
-/

@[expose] public section

universe u
open CategoryTheory Topology IsLocalRing
namespace AlgebraicGeometry

/-- A strict specialization is traced by the generic and closed points of a DVR.

Source: Stacks Project, Tag 054F. Choose an affine neighbourhood of the special point;
it also contains the general point. The corresponding primes form a strict inclusion.
Apply `Ideal.exists_isDiscreteValuationRing_of_lt` to obtain a ring map whose kernel is
the smaller prime and whose inverse image of the maximal ideal is the larger prime.
Its spectrum map, followed by the affine chart, has the required values.
(blueprint: lem-sbc-noetherian-specialization-trait) -/
theorem exists_trait_of_strict_specializes {X : Scheme.{u}} [IsLocallyNoetherian X]
    {x y : X} (hxy : y ⤳ x) (hne : y ≠ x) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (a : Spec (.of R) ⟶ X),
      a (closedPoint R) = x ∧ a (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) = y := by
  let i := X.affineOpenCover.idx x
  let B := X.affineOpenCover.X i
  let j : Spec B ⟶ X := X.affineOpenCover.f i
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range j := X.affineOpenCover.covers x
  have hy : y ∈ Set.range j := hxy.mem_open j.isOpenEmbedding.isOpen_range ⟨x₀, hx₀⟩
  obtain ⟨y₀, hy₀⟩ := hy
  have hspec : y₀ ⤳ x₀ := j.isOpenEmbedding.isInducing.specializes_iff.mp
    (by simpa [hx₀, hy₀] using hxy)
  have hlt : y₀.asIdeal < x₀.asIdeal := lt_of_le_of_ne
    ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec)
    (fun h ↦ hne (by rw [← hy₀, ← hx₀, PrimeSpectrum.ext h]))
  have : IsLocallyNoetherian (Spec B) :=
    LocallyOfFiniteType.isLocallyNoetherian j
  have : IsNoetherianRing B := (isLocallyNoetherian_Spec (R := B)).mp inferInstance
  obtain ⟨R, hR, hdom, hdvr, φ, hker, hmax⟩ :=
    Ideal.exists_isDiscreteValuationRing_of_lt hlt
  let a : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ j
  refine ⟨R, hR, hdom, hdvr, a, ?_, ?_⟩
  · change j (PrimeSpectrum.comap φ (closedPoint R)) = x
    have h : PrimeSpectrum.comap φ (closedPoint R) = x₀ := PrimeSpectrum.ext hmax
    rw [h, hx₀]
  · change j (PrimeSpectrum.comap φ ⟨⊥, Ideal.isPrime_bot⟩) = y
    have h : PrimeSpectrum.comap φ ⟨⊥, Ideal.isPrime_bot⟩ = y₀ :=
      PrimeSpectrum.ext hker
    rw [h, hy₀]

end AlgebraicGeometry
