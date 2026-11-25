/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.IntegralHenselianClosedFibreSections
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionsFieldExtension

/-! # Injectivity of integral sections over a strictly henselian base

Source: Stacks Project, Tags 09XK, 09ZH and 0A3I, as used in Tag 0EYP.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction to any closed geometric fibre of an integral scheme over a strictly
henselian local ring is injective on sections.

Source: Stacks Project, Tags 09XK, 09ZH and 0A3I, proof of Tag 0EYP.
(blueprint: lem-sbc-strict-henselian-integral-sections-injective).

Proof: An integral scheme over Spec A is affine, say Spec B, with B integral over A.
Set J to the extension of the maximal ideal of A. Tag 09XK makes (B,J) henselian.
Apply henselian degree-zero comparison to the proper identity of Spec B to see
that restriction to Spec(B/J) is injective. The map t factors through the residue
field k of A, since its image is the closed point. The ring k is separably closed.
Tag 0A3I makes further restriction from the closed fibre to its extension along
k -> Omega bijective. Forgetting modules to sets commutes with inverse images
and the units; hence these are the same restriction maps for module coefficients.
The pullback property identifies their composite, up to the canonical composition
and terminal-section isomorphisms, with the displayed map. Injectivity follows.
The zero algebra B and the empty fibre cause no exception: their section module
is zero, and the henselian comparison also holds for the zero ring. -/
theorem strictHenselianIntegralSections_injective
    (Λ : Type (u + 1)) [CommRing Λ]
    (A : Type u) [CommRing A] [IsStrictlyHenselianLocalRing A]
    {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsIntegralHom p]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of A))
    (ht : t (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A)
    (i : Z' ⟶ Z) (p' : Z' ⟶ Spec (.of Ω)) (sq : IsPullback i p' p t)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Injective (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F).hom := by
  let φ := (Spec.preimage t).hom
  have htφ : PrimeSpectrum.comap φ (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint A := by
    change Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint Ω) = _
    simpa only [φ, CommRingCat.ofHom_hom, Spec.map_preimage] using ht
  have hker : IsLocalRing.maximalIdeal A ≤ RingHom.ker φ := by
    have h := congrArg PrimeSpectrum.asIdeal htφ
    simpa only [PrimeSpectrum.comap_asIdeal, IsLocalRing.closedPoint,
      IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot] using le_of_eq h.symm
  let ψ : IsLocalRing.ResidueField A →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ hker
  let s : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let r : Spec (.of Ω) ⟶ Spec (.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom ψ)
  have hrs : r ≫ s = t := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact Spec.map_preimage t
  let Z₀ := Limits.pullback p s
  let i₀ : Z₀ ⟶ Z := Limits.pullback.fst p s
  let p₀ : Z₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)) := Limits.pullback.snd p s
  let j : Z' ⟶ Z₀ := Limits.pullback.lift i (p' ≫ r) (by rw [Category.assoc, hrs]; exact sq.w)
  have hj : j ≫ i₀ = i := by simp [j, i₀]
  have hjp : j ≫ p₀ = p' ≫ r := by simp [j, p₀]
  have sqj : IsPullback j p' p₀ r := by
    have outer : IsPullback p' (j ≫ i₀) (r ≫ s) p := by
      simpa only [hj, hrs] using sq.flip
    exact (IsPullback.of_bot outer hjp.symm (IsPullback.of_hasPullback p s).flip).flip
  have h₀ := integralHenselianClosedFibreSections_injective Λ A p i₀ p₀
    (IsPullback.of_hasPullback p s) F
  have h₁ := etaleModuleSectionsFieldExtension_injective Λ
    (IsLocalRing.ResidueField A) Ω p₀ r j p' sqj ((i₀)^*[ModuleCat.{u + 1} Λ].obj F)
  have hcomp := globalSectionsUpperStarMap_comp' (ModuleCat.{u + 1} Λ) j i₀ i hj.symm F
  intro x y hxy
  apply h₀
  apply h₁
  have he := congrArg (fun f ↦ f.hom x) hcomp
  have he' := congrArg (fun f ↦ f.hom y) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he he'
  exact he.symm.trans ((congrArg
    ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) j i₀ i hj.symm).hom.app F)).hom hxy).trans he')

end AlgebraicGeometry.Etale
