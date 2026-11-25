/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.RingTheory.CoverModuleExact

import WeilConjectures.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives
import WeilConjectures.AlgebraicGeometry.ProjTwistLocalOverlapCompatibility

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Finite localization data of twist sections

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- A family spanning the unit ideal has a unit image in any local ring. -/
private theorem exists_unit_of_span_top
    {B R ι : Type*} [CommRing B] [CommRing R] [IsLocalRing R]
    (g : ι → B) (hspan : Ideal.span (Set.range g) = ⊤) (F : B →+* R) :
    ∃ i, IsUnit (F (g i)) := by
  classical
  by_contra hn
  have hle : Ideal.span (Set.range g) ≤ Ideal.comap F (IsLocalRing.maximalIdeal R) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change F (g i) ∈ IsLocalRing.maximalIdeal R
    exact (IsLocalRing.mem_maximalIdeal _).mpr (fun h ↦ hn ⟨i, h⟩)
  have h1 := hle (hspan.symm ▸ (show (1 : B) ∈ (⊤ : Ideal B) from trivial))
  change F 1 ∈ IsLocalRing.maximalIdeal R at h1
  exact h1 (by simp)

/-- A twist section has compatible ordinary fractions on a finite principal cover of
Spec(A_(f)), with evaluations agreeing with the original section.
Source: Stacks Project, Section 27.8, preceding Definition 27.8.3 (Tag 01M6),
and Lemma 27.8.4 (Tag 01M7).
(blueprint: lem-sc-proj-twist-finite-localization-data)

Proof: at each point use the local homogeneous-fraction witness of s. Choose a
homogeneous basic neighborhood inside its witness neighborhood and D₊(f). Multiply the
witness denominator by this neighborhood's defining element and by f, and multiply the
numerator by the same factors. The resulting homogeneous denominator h has positive
degree c and D₊(h) lies in the witness neighborhood. For u = h^b/f^c in A_(f), the affine
chart identifies D₊(h) inside D₊(f) with D(u). Quasi-compactness gives finitely many such
neighborhoods. Their chart elements u_i generate the unit ideal. In A_f localized at u_i,
h_i is invertible since h_i^b = u_i*f^c_i and f is invertible, so the witness fraction
defines t_i. On an overlap use the homogeneous element f*h_i*h_j of A. Both fractions
have the same evaluations s(p) at every point of its basic open, so homogeneous-prime
equality detection makes them equal in A localized at f*h_i*h_j. The universal properties
identify this ring localization with the iterated module localization at u_i*u_j, giving
the displayed compatibility. At a point of D(u_i), u_i maps to a unit in A_p; the ordinary
evaluation A_f → A_p therefore extends to the further localization. Its underlying
additive map sends z/1 to the ordinary evaluation of z and t_i to s(p). Every point lies
in some neighborhood. If the open is empty, f is nilpotent and both A_f and A_(f) are
zero; the empty cover has span top in this zero ring and evaluation is vacuous. -/
theorem twist_finiteLocalization_data
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤),
      let ρ := fun (a h : B) (ha : a ∣ h) ↦
        IsLocalizedModule.lift (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
          (RingTheory.localizationAway_map_units_of_dvd (M := M) a h ha)
      ∃ t : ∀ i : Fin n, LocalizedModule.Away (g i) M,
        (∀ i j : Fin n,
          ρ (g i) (g i * g j) (dvd_mul_right (g i) (g j)) (t i) =
            ρ (g j) (g i * g j) (dvd_mul_left (g j) (g i)) (t j)) ∧
        ∀ p : basicOpen 𝒜 f,
          ∃ (i : Fin n)
            (e : LocalizedModule.Away (g i) M →+
              Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
            (∀ z : M,
              e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
                IsLocalization.map (M := Submonoid.powers f)
                  (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
                  (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
                  (Submonoid.powers_le.mpr p.2) z) ∧
            e (t i) = (s.1 p).1  := by
  rcases twist_finiteLocal_representatives 𝒜 k f b hb hf s with
    ⟨n, g, hspan, t, hlocal⟩
  refine ⟨n, g, hspan, t, ?_, ?_⟩
  · exact twist_localOverlap_compatibility 𝒜 k f b hb hf s n g t hlocal
  · intro p
    let F := IsLocalization.map (M := Submonoid.powers f)
      (S := LocalizedModule.Away f A)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
    obtain ⟨i, hi⟩ := exists_unit_of_span_top g hspan
      (F.comp (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)))
    obtain ⟨e, he, _, hs⟩ := hlocal i p hi
    exact ⟨i, e, he, hs⟩

end AlgebraicGeometry.Proj
