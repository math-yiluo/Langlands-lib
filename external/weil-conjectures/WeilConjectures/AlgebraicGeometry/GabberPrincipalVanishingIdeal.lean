/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCohomologyJointKernel
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # GabberPrincipalVanishingIdeal

Source: Stacks Project, Tag 0GY0.
(blueprint: lem-weil-pbc-gabber-principal-vanishing-ideal) -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private theorem cohomologyMap_eq_zero_of_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) (hx : cohomologyMap b F q x = 0) :
    cohomologyMap (a ≫ b) F q x = 0 := by
  let e := (upperStarComp AddCommGrpCat.{u + 1} a b).app F
  have he := (cohomologyPullbackFunctorial a b F q).2.1 x
  rw [hx, map_zero] at he
  have he' := congrArg (Sheaf.H.map e.inv q) he
  simpa [e, ← Sheaf.H.map_comp_apply] using he'.symm

private theorem cohomologyMap_eq_zero_of_le {X : Scheme.{u}} {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W)
    (F : Sheaf W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) (hx : cohomologyMap (X.homOfLE hVW) F q x = 0) :
    cohomologyMap (X.homOfLE (hUV.trans hVW)) F q x = 0 := by
  rw [← X.homOfLE_homOfLE hUV hVW]
  exact cohomologyMap_eq_zero_of_comp _ _ F q x hx

private theorem cohomologyMap_transported_eq_zero {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ((b)^*[AddCommGrpCat.{u + 1}]).obj F ≅ G)
    (q : ℕ) (x : Sheaf.H F q) (hx : cohomologyMap (a ≫ b) F q x = 0) :
    cohomologyMap a G q (Sheaf.H.map e.hom q (cohomologyMap b F q x)) = 0 := by
  rw [cohomologyMap_map, (cohomologyPullbackFunctorial a b F q).2.1 x,
    hx, map_zero, map_zero]

private theorem cohomologyMap_eq_zero_of_transport {X Y : Scheme.{u}}
    (b : X ⟶ Y) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ((b)^*[AddCommGrpCat.{u + 1}]).obj F ≅ G)
    (q : ℕ) (x : Sheaf.H F q)
    (hx : Sheaf.H.map e.hom q (cohomologyMap b F q x) = 0) :
    cohomologyMap b F q x = 0 := by
  have h := congrArg (Sheaf.H.map e.inv q) hx
  simpa only [← Sheaf.H.map_comp_apply, Iso.hom_inv_id,
    Sheaf.H.map_id_apply, map_zero] using h

/-- The principal restrictions killing a class form an ideal in the inductive step.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label lemma-gabber-criterion,
proof's ideal and addition-closure paragraphs.
(blueprint: lem-weil-pbc-gabber-principal-vanishing-ideal)

Proof: let I consist of f such that the class restricts to zero on D(fh).
The empty open D(0) gives zero membership, and restriction functoriality gives
closure under multiplication by any r. For addition, restrict the class to
D(h(f+g)). If q = 1, apply hfg to hf and hg; its two target opens are
D(h^2 f(f+g)) and D(h^2 g(f+g)), equal to D(hf(f+g)) and D(hg(f+g)).
Functoriality and the inverse-image composition isomorphisms make both images
zero. If q > 1, these two opens cover D(h(f+g)), and their intersection is
D(hfg(f+g)). Its degree q-1 group is subsingleton by hprev. Exactness of
Mayer--Vietoris therefore makes the two restriction maps jointly injective.
The restricted class is zero, proving addition closure. Negatives follow from
multiplication by -1, so the set with these operations is an ideal. All
composition identifications are additive and preserve zero. The empty open,
f = 0, g = -f, and h = 0 require no exclusions. -/
theorem gabber_principal_vanishing_ideal
    (R : Type u) [CommRing R]
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfg : ∀ (f g : R) (x : Sheaf.H
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1),
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right f (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right g (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
        x = 0)
    (q : ℕ) (hq : 0 < q)
    (hprev : ∀ (n : ℕ), 0 < n → n < q → ∀ (a : R),
      Subsingleton (Sheaf.H
        (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
          (PrimeSpectrum.basicOpen a))^*[AddCommGrpCat.{u + 1}]).obj F) n))
    (h : R) (ξ : Sheaf.H
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q) :
    ∃ I : Ideal R, ∀ f : R, f ∈ I ↔ (cohomologyMap
      (Scheme.homOfLE (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen_mul_le_right f h))
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q ξ) = 0 := by
  let P : R → Prop := fun f ↦ cohomologyMap
    (Scheme.homOfLE (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen_mul_le_right f h))
    (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q ξ = 0
  have hzero : P 0 := by
    dsimp [P]
    let W : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen (0 * h)
    have hW : W = ⊥ := by simp [W]
    have : IsEmpty W.toScheme := by
      refine ⟨fun x ↦ ?_⟩
      have hx := x.property
      change x.val ∈ W at hx
      simp [hW] at hx
    have hz := Sheaf.subsingleton_H_of_isZero
      (Scheme.Etale.isZero_sheaf_of_isEmpty
        (((Scheme.homOfLE (X := Spec (CommRingCat.of R))
          (PrimeSpectrum.basicOpen_mul_le_right 0 h))^*[AddCommGrpCat.{u + 1}]).obj
          (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
            (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F))) q
    exact hz.elim _ _
  have hmul (r f : R) (hf : P f) : P (r * f) := by
    have hle : PrimeSpectrum.basicOpen ((r * f) * h) ≤
        PrimeSpectrum.basicOpen (f * h) := by
      simpa only [mul_assoc] using PrimeSpectrum.basicOpen_mul_le_right r (f * h)
    exact cohomologyMap_eq_zero_of_le hle
      (PrimeSpectrum.basicOpen_mul_le_right f h) _ q ξ hf
  have hadd (f g : R) (hf : P f) (hg : P g) : P (f + g) := by
    let X := Spec (CommRingCat.of R)
    let a := f * h
    let b := g * h
    let H : X.Opens := PrimeSpectrum.basicOpen h
    let A : X.Opens := PrimeSpectrum.basicOpen (a + b)
    have hAH : A ≤ H := by
      dsimp [A, H, a, b]
      rw [← add_mul]
      exact PrimeSpectrum.basicOpen_mul_le_right (f + g) h
    let j := X.homOfLE hAH
    let G := ((H.ι)^*[AddCommGrpCat.{u + 1}]).obj F
    let K := ((A.ι)^*[AddCommGrpCat.{u + 1}]).obj F
    let e : ((j)^*[AddCommGrpCat.{u + 1}]).obj G ≅ K :=
      ((upperStarComp AddCommGrpCat.{u + 1} j H.ι A.ι
        (X.homOfLE_ι hAH).symm).app F).symm
    let z := Sheaf.H.map e.hom q (cohomologyMap j G q ξ)
    have ha : cohomologyMap
        (X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right a (a + b))) K q z = 0 := by
      apply cohomologyMap_transported_eq_zero _ j G K e q ξ
      rw [X.homOfLE_homOfLE]
      apply cohomologyMap_eq_zero_of_le
        (PrimeSpectrum.basicOpen_mul_le_left a (a + b))
        (PrimeSpectrum.basicOpen_mul_le_right f h) _ q ξ hf
    have hb : cohomologyMap
        (X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right b (a + b))) K q z = 0 := by
      apply cohomologyMap_transported_eq_zero _ j G K e q ξ
      rw [X.homOfLE_homOfLE]
      apply cohomologyMap_eq_zero_of_le
        (PrimeSpectrum.basicOpen_mul_le_left b (a + b))
        (PrimeSpectrum.basicOpen_mul_le_right g h) _ q ξ hg
    have hz : z = 0 := by
      by_cases hq1 : q = 1
      · subst q
        exact hfg a b z ha hb
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
        have hnpos : 0 < n := by omega
        have hnlt : n < q := by omega
        subst q
        exact principalOpenCohomology_joint_kernel R F a b n
          (hprev n hnpos hnlt (a * b * (a + b))) z ha hb
    have hj := cohomologyMap_eq_zero_of_transport j G K e q ξ hz
    have hA' : PrimeSpectrum.basicOpen ((f + g) * h) ≤ A := by
      dsimp [A, a, b]
      rw [← add_mul]
    exact cohomologyMap_eq_zero_of_le hA' hAH G q ξ hj
  let I : Ideal R :=
    { carrier := {f | P f}
      zero_mem' := hzero
      add_mem' := by intro f g hf hg; exact hadd f g hf hg
      smul_mem' := by intro r f hf; exact hmul r f hf }
  refine ⟨I, ?_⟩
  intro f
  rfl

end AlgebraicGeometry.Etale
