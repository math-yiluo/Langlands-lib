/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtaleClassVanishingSpreads
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-! # GabberPrincipalClassLocallyZero

Source: Stacks Project, Tag 0GY0.
(blueprint: lem-weil-pbc-gabber-principal-class-locally-zero) -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem vanishing_of_factorization {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : a ≫ b = c)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (ξ : Sheaf.H F q) (hb : cohomologyMap b F q ξ = 0) :
    cohomologyMap c F q ξ = 0 := by
  subst c
  have he := (cohomologyPullbackFunctorial a b F q).2.1 ξ
  rw [hb, map_zero] at he
  have hi := injective_sheafHMap_of_isIso
    ((upperStarComp AddCommGrpCat.{u + 1} a b).hom.app F) q
  exact hi (he.symm.trans (map_zero _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Every positive-degree class locally vanishes on principal opens.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label lemma-gabber-criterion,
proof's local triviality paragraph; Lemma 03QO and the local-ring continuity
argument in Lemma 09AX (using Tags 03Q6, 09YQ and 03F3).
(blueprint: lem-weil-pbc-gabber-principal-class-locally-zero)

Proof: identify the stalk on D(h) at p with the prime localization R_p.
Transport strict henselianity along this isomorphism. Positive-degree etale
cohomology over its spectrum vanishes by 03QO, so the local pullback of the class
is zero. Local-ring continuity spreads this vanishing to an open neighborhood U
of p in D(h). Choose a basic open D(f) containing p inside the image of U in
Spec R and refine to D(fh). Its inclusion into D(h) factors through U, hence
pullback composition kills the class there. Membership in D(f) gives f outside p.
This works also for h = 0: there are no primes avoiding h. -/
theorem gabber_principal_class_locally_zero
    (R : Type u) [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsStrictlyHenselianLocalRing (Localization.AtPrime p))
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (hq : 0 < q)
    (h : R) (ξ : Sheaf.H
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q) :
    ∀ (p : Ideal R) [p.IsPrime], h ∉ p →
      ∃ f : R, (cohomologyMap
      (Scheme.homOfLE (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen_mul_le_right f h))
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q ξ) = 0 ∧ f ∉ p := by
  intro p hp hh
  let X := Spec (CommRingCat.of R)
  let H : X.Opens := PrimeSpectrum.basicOpen h
  let x : H.toScheme := ⟨⟨p, hp⟩, hh⟩
  let G := ((H.ι)^*[AddCommGrpCat.{u + 1}]).obj F
  let e := (H.stalkIso x) ≪≫ Spec.stalkIso (CommRingCat.of R) ⟨p, hp⟩
  let : IsStrictlyHenselianLocalRing (Localization.AtPrime p) := hR p
  let : IsStrictlyHenselianLocalRing (H.toScheme.presheaf.stalk x) :=
    IsStrictlyHenselianLocalRing.of_ringEquiv e.symm.commRingCatIsoToRingEquiv
  have hlocal : cohomologyMap (H.toScheme.fromSpecStalk x) G q ξ = 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    have hs := Scheme.subsingleton_H_of_isStrictlyHenselianLocalRing
      (H.toScheme.presheaf.stalk x)
      (((H.toScheme.fromSpecStalk x)^*[AddCommGrpCat.{u + 1}]).obj G) n
    exact hs.allEq _ _
  obtain ⟨U, hxU, hU⟩ := etale_class_vanishing_spreads G q ξ x hlocal
  have hxW : (⟨p, hp⟩ : PrimeSpectrum R) ∈ H.ι ''ᵁ U :=
    H.mem_ι_image_iff.mpr hxU
  obtain ⟨V, ⟨f, rfl⟩, hpf, hfV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hxW
  have hfH : PrimeSpectrum.basicOpen (f * h) ≤ H.ι ''ᵁ U :=
    (PrimeSpectrum.basicOpen_mul_le_left f h).trans hfV
  let g := X.homOfLE hfH ≫ (H.ι.isoImage U).inv
  have hg : g ≫ U.ι = X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right f h) := by
    apply (cancel_mono H.ι).mp
    change (X.homOfLE hfH ≫ (H.ι.isoImage U).inv) ≫ U.ι ≫ H.ι = _
    rw [Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι]
  refine ⟨f, ?_, hpf⟩
  exact vanishing_of_factorization g U.ι _ hg G q ξ hU

end AlgebraicGeometry.Etale
