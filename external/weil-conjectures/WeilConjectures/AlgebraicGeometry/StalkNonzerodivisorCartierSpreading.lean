/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.Ideal

/-! # Spreading a stalk nonzerodivisor generator to a Cartier equation

Source: Stacks Project, divisors.tex, Tag 0AG8 (lemma-effective-Cartier-in-points),
and Algebra, Tag 061L (lemma-regular-sequence-in-neighbourhood).
(blueprint: lem-sfb-stalk-nonzerodivisor-cartier-spreading).

The two statements are the ring assertion and the scheme assertion of the node.
The ideal stalk in the latter is expressed by extending the ideal on an affine
neighbourhood along the canonical germ homomorphism. This is the stalk ideal inside
the structure-sheaf stalk, independently of the chosen affine neighbourhood.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- Clear the ideal generators and the kernel of the localization map simultaneously.
This is the finite-denominator argument of Stacks Tags 0AG8 and 061L. -/
private theorem exists_clearing_of_regular_generator
    {A S : Type u} [CommRing A] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] [CommRing S] [Algebra A S]
    [IsLocalization.AtPrime S P] (I : Ideal A) (t : S)
    (ht : I.map (algebraMap A S) = Ideal.span {t})
    (htreg : Function.Injective (fun z : S ↦ t * z)) :
    ∃ g ∉ P, ∃ π ∈ I, (∀ a ∈ I, g * a ∈ Ideal.span {π}) ∧
      (∀ b, π * b = 0 → g * b = 0) := by
  classical
  obtain ⟨⟨⟨π, hπI⟩, s⟩, hπs⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl S).mp
    (ht ▸ Ideal.mem_span_singleton_self t)
  have hsu : IsUnit (algebraMap A S s) := IsLocalization.map_units S s
  have hspan : I.map (algebraMap A S) = Ideal.span {algebraMap A S π} := by
    rw [ht, ← hπs, Ideal.span_singleton_mul_right_unit hsu]
  have hπreg : Function.Injective (fun z : S ↦ algebraMap A S π * z) := by
    intro x y hxy
    apply htreg
    apply (IsUnit.isRegular hsu).right
    simpa only [mul_assoc, mul_comm (algebraMap A S s), mul_left_comm t] using
      (show (t * algebraMap A S s) * x = (t * algebraMap A S s) * y from
        hπs.symm ▸ hxy)
  obtain ⟨F, hF⟩ := (IsNoetherian.noetherian I : I.FG)
  have h1 (a : A) (ha : a ∈ F) : ∃ u ∉ P, u * a ∈ Ideal.span {π} := by
    have : algebraMap A S a ∈ (Ideal.span {π}).map (algebraMap A S) := by
      rw [Ideal.map_span, Set.image_singleton, ← hspan]
      exact Ideal.mem_map_of_mem _ (hF ▸ Ideal.subset_span ha)
    obtain ⟨u, hu, h⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl S _ _).1 this
    exact ⟨u, hu, h⟩
  choose! u hu hu' using h1
  obtain ⟨T, hT⟩ :=
    (IsNoetherian.noetherian (RingHom.ker (algebraMap A S)) : (RingHom.ker _).FG)
  have h2 (b : A) (hb : b ∈ T) : ∃ v ∉ P, v * b = 0 := by
    have : algebraMap A S b = 0 := (hT ▸ Ideal.subset_span hb : b ∈ RingHom.ker _)
    obtain ⟨⟨v, hv⟩, h⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl S b).1 this
    exact ⟨v, hv, h⟩
  choose! v hv hv' using h2
  have hg : (∏ a ∈ F, u a) * ∏ b ∈ T, v b ∉ P :=
    P.primeCompl.mul_mem (P.primeCompl.prod_mem fun a ha => hu a ha)
      (P.primeCompl.prod_mem fun b hb => hv b hb)
  refine ⟨_, hg, π, hπI, ?_, ?_⟩
  · intro a ha
    rw [← hF] at ha
    refine Ideal.mul_mem_of_mem_span_of_forall _ _ _ (fun a ha => ?_) ha
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem u ha
    rw [hc]
    convert Ideal.mul_mem_right (c * ∏ b ∈ T, v b) _ (hu' a ha) using 1
    ring
  · intro b hb
    have hb' : algebraMap A S b = 0 := by
      have := congrArg (algebraMap A S) hb
      rw [map_mul, map_zero] at this
      exact hπreg (by simpa only [mul_zero] using this)
    have hbk : b ∈ Ideal.span (T : Set A) := by
      rw [Ideal.span, hT]
      exact hb'
    have := Ideal.mul_mem_of_mem_span_of_forall (T : Set A) ⊥ ((∏ a ∈ F, u a) * ∏ b ∈ T, v b)
      (fun t ht => by
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem v ht
        rw [hc, Ideal.mem_bot]
        calc _ = (∏ a ∈ F, u a) * c * (v t * t) := by ring
          _ = 0 := by rw [hv' t ht, mul_zero]) hbk
    exact Ideal.mem_bot.1 this


end Ideal

namespace AlgebraicGeometry

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- A closed subscheme whose ideal stalks have nonzerodivisor generators has an effective
Cartier ideal. The affine germ presentation denotes the ideal stalk, not an equation on
an open neighbourhood. The generator may be a unit at a point outside the closed subscheme.

Source: Stacks Project, divisors.tex, Tag 0AG8 (lemma-effective-Cartier-in-points), (2).
(blueprint: lem-sfb-stalk-nonzerodivisor-cartier-spreading).

Proof:
5. Fix x and an affine neighbourhood Spec B. Local Noetherianity makes B Noetherian.
   The ideal sheaf i.ker is quasi-coherent by def-sbc-closed-immersion-ideal-sheaf.
   By lem-weil-pbc-affine-open-stalk-localization its ring stalk is B_p, and by
   lem-sbc-affine-module-germ-localization the ideal stalk, with its inclusion in
   the ring stalk, is the extension I B_p. Thus the hypothesis gives the ring
   assertion above, independently of the affine chart used to express it.
6. Apply the ring assertion to obtain g outside p and a in I. The basic open D(g)
   is affine with section ring B_g by lem-weil-pbc-affine-ideals-closed-subscheme.
   By lem-weil-pbc-affine-module-basic-open-localization, its ideal sections are
   I B_g, inside the structure sheaf, so they are generated by the regular a/1.
7. The affine description of def-sbc-closed-immersion-ideal-sheaf identifies this
   with the local equation of the closed subscheme. These neighbourhoods cover X,
   giving precisely def-nagata-effective-cartier-ideal, namely i.ker.IsInvertible.
8. Outside the closed subscheme its ideal stalk is the whole ring, with generator
   1. For the empty closed subscheme this works everywhere; for empty X the cover
   condition is vacuous. The proof uses no reducedness, integrality or regularity. -/
theorem isInvertible_ker_of_stalk_nonzerodivisor
    {X H : Scheme.{u}} [IsLocallyNoetherian X]
    (i : H ⟶ X) [IsClosedImmersion i]
    (h : ∀ x : X, ∃ (U : X.affineOpens) (hx : x ∈ U.1)
      (t : X.presheaf.stalk x),
      (i.ker.ideal U).map (X.presheaf.germ U.1 x hx).hom = Ideal.span {t} ∧
        Function.Injective (fun z : X.presheaf.stalk x ↦ t * z)) :
    i.ker.IsInvertible := by
  generalize hj : i.ker = J at h ⊢
  intro x
  obtain ⟨U, hx, t, hI, ht⟩ := h x
  let p := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Algebra (X.presheaf.obj (.op U.1)) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  have : IsNoetherianRing (X.presheaf.obj (.op U.1)) :=
    IsLocallyNoetherian.component_noetherian U
  obtain ⟨g, hgp, a, haI, hgen, hkill⟩ :=
    Ideal.exists_clearing_of_regular_generator p (J.ideal U) t hI ht
  have hxg : x ∈ X.basicOpen g := by
    apply (X.mem_basicOpen g x hx).mpr
    exact IsLocalization.map_units (X.presheaf.stalk x) (⟨g, hgp⟩ : p.primeCompl)
  have := U.2.isLocalization_basicOpen g
  refine ⟨X.affineBasicOpen g, hxg, ?_⟩
  rw [← J.map_ideal (show X.affineBasicOpen g ≤ U from X.basicOpen_le g)]
  exact Ideal.isRegularPrincipal_map_away
    (A := X.presheaf.obj (.op U.1))
    (B := X.presheaf.obj (.op (X.basicOpen g))) g (J.ideal U) a haI hgen hkill

end AlgebraicGeometry
