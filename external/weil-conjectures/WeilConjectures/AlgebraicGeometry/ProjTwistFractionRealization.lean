/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.Algebra.Module.DegreeZeroFractions

/-!
# Realization of homogeneous fractions on a Proj basic open

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous shifted fraction defines a section of the twist.
Source: Stacks Project, Definition 27.10.1, Tag 01MN.
(blueprint: lem-sc-proj-twist-fraction-realization)

Proof: choose a homogeneous numerator y and homogeneous denominator d in powers of f
of equal shifted degree from the definition of degreeZeroFractions. If the shifted degree
is negative then y is zero, and use the zero section. Otherwise d avoids every point of
D₊(f), and degreePart.mk y d defines the required section by isLocallyFraction_mk.
Its value in every prime localization is the image of the ordinary fraction, by the
formula for the localization map on fractions. This also covers nilpotent f. -/
theorem twist_fraction_realization
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A)
    (z : LocalizedModule.Away f A)
    (hz : z ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set A))
      (fun n : ℕ ↦ {y : A | if 0 ≤ k + n then y ∈ 𝒜 (k + n).toNat else y = 0})
      (Submonoid.powers f)) :
    ∃ s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f)),
      ∀ p : basicOpen 𝒜 f,
        IsLocalization.map (M := Submonoid.powers f)
          (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
          (Submonoid.powers_le.mpr p.2) z = (s.1 p).1  := by
  classical
  obtain ⟨n, y, d, hy, hd, rfl⟩ := hz
  by_cases hn : 0 ≤ k + n
  · have hy' : y ∈ 𝒜 (k + n).toNat := by simpa [hn] using hy
    have hdeg : ((k + n).toNat : ℤ) = n + k := by omega
    have hden (p : basicOpen 𝒜 f) : (d : A) ∉ p.1.asHomogeneousIdeal.toIdeal :=
      (Submonoid.powers_le.mpr p.2 : Submonoid.powers f ≤
        p.1.asHomogeneousIdeal.toIdeal.primeCompl) d.2
    refine ⟨⟨(fun p ↦ HomogeneousLocalization.degreePart.mk ⟨y, hy'⟩ ⟨d, hd⟩
      (hden p) hdeg), ProjectiveSpectrum.Twist.isLocallyFraction_mk hdeg
        ⟨y, hy'⟩ ⟨d, hd⟩ hden⟩, ?_⟩
    intro p
    change IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id A) _
      (Localization.mk y d) = Localization.mk y ⟨d, hden p⟩
    simp only [Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
  · have hy' : y = 0 := by simpa [hn] using hy
    subst y
    refine ⟨0, ?_⟩
    intro p
    change IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id A) _
      (Localization.mk 0 d) = 0
    rw [Localization.mk_zero, map_zero]

end AlgebraicGeometry.Proj
