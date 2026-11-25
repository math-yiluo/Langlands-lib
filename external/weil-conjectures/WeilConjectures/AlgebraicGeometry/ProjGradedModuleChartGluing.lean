/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.Algebra.Module.GradedModuleAwayRestriction
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.RingTheory.CoverModuleExact

/-!
# Finite gluing of graded-module charts

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-gluing)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-graded-module-chart-gluing) -/
local instance localizedModuleHomogeneousScalarsChartGluing (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1

/-- Finite unique gluing for a graded-module chart system, including the empty cover.
Source: Stacks Project, Constructions, Lemma 01M4 (1)(c)--(h) and the construction
before Definition 01M6; Algebra, Lemma 00EK.
(blueprint: lem-weil-pbc-proj-graded-module-chart-gluing)

Proof:
1. Use standardOpenProperties to obtain the unit-ideal generators
   u_i = g_i^deg(f)/f^deg(g_i) in R[f] for the displayed cover.
2. Apply gradedModuleAwayRestriction. Its submodule has the same carrier as Z, so
   Submodule.ext identifies them. The given rho agrees with its restriction: represent
   each element by an ordinary localized fraction and use the stated fraction formula.
   The ambient ring maps agree by the uniqueness of maps out of S_f that commute with S;
   injectivity of homogeneous-localization inclusion gives equality of rhoS.
3. Transport the principal localization comparisons to Z. The comparison to each chart
   sends t/1 to rho(t). The generator for the product chart is u_i*u_j: this follows by
   multiplying the two fractions. The comparison composition law identifies the two
   overlap maps with the canonical localization maps in coverModuleExact.
4. Transport q_i back along these comparisons. The overlap assumption is exactly the
   compatibility hypothesis of coverModuleExact. That theorem gives a unique t in Z f,
   and its localization equations give the asserted restriction equations. Conversely
   any solution localizes to this glued t and hence equals it. For n=0 the unit-ideal
   hypothesis forces R[f] to be the zero ring and Z f the zero module, so the same
   existence and uniqueness proof applies without a maximum over an empty set. -/
theorem gradedModuleChart_gluing
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (hZ : (∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)))
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (hlaws : (∀ (f g : Fidx) (i : D[g] ≤ D[f]),
        (∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) ∧
        (∀ (r : R[f]) (q : Z f), rho f g i (r • q) = rhoS f g i r • rho f g i q) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g.val.1 ^ e = a * f.val.1 →
          ∀ (m : ℕ) (y : M) (q : Z f),
            (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
            (rho f g i q : N[g]) = mk (a ^ m • y)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1))) ∧
      (∀ (f : Fidx) (i : D[f] ≤ D[f]) (q : Z f), rho f f i q = q) ∧
      (∀ (f g h : Fidx) (i : D[g] ≤ D[f]) (j : D[h] ≤ D[g]) (q : Z f),
        rho g h j (rho f g i q) = rho f h (j.trans i) q) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]), D[f] = D[g] →
        Function.Bijective (rho f g i)))
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val) :
    let fg := fun f g : Fidx ↦
      (⟨(f.val.1 * g.val.1, f.val.2 + g.val.2),
        Nat.add_pos_left f.property.1 g.val.2,
        SetLike.mul_mem_graded f.property.2 g.property.2⟩ : Fidx)
    ∀ (f : Fidx) (n : ℕ) (g : Fin n → Fidx)
      (hg : ∀ i, D[g i] ≤ D[f]),
      (⨆ i, D[g i]) = D[f] → ∀ q : ∀ i, Z (g i),
      (∀ i j,
        rho (g i) (fg (g i) (g j))
          (by simpa only [fg, basicOpen_mul] using
            (inf_le_left : D[g i] ⊓ D[g j] ≤ D[g i])) (q i) =
        rho (g j) (fg (g i) (g j))
          (by simpa only [fg, basicOpen_mul] using
            (inf_le_right : D[g i] ⊓ D[g j] ≤ D[g j])) (q j)) →
      ∃! t : Z f, ∀ i, rho f (g i) (hg i) t = q i := by
  classical
  have _ := hcanonical
  clear hcanonical
  obtain ⟨Z', hZ', lambda, lambdaS, r, rS, U, hU, hpair, hid, hmul, hcomp,
    theta, thetaS, htheta, hkappa⟩ := gradedModuleAwayRestriction 𝒜 𝓜 h𝓜 hsmul
  have hZZ : Z' = Z := by
    funext f
    apply SetLike.coe_injective
    exact (hZ' f).trans (hZ f).symm
  subst Z'
  have hr (f g : Fidx) (i : D[g] ≤ D[f])
      (p : ∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1)
      (x : Z f) : rho f g i x = r f g p x := by
    obtain ⟨e, k, a, he, ha, hp⟩ := p
    have hx : ∃ (y : M) (s : Submonoid.powers f.val.1), mk y s = (x : N[f]) := by
      exact LocalizedModule.induction_on (fun y s ↦ ⟨y, s, rfl⟩) x.val
    obtain ⟨y, s, hs⟩ := hx
    obtain ⟨m, hm⟩ := s.property
    have hs' : s = (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) :=
      Subtype.ext hm.symm
    rcases hpair f g ⟨e, k, a, he, ha, hp⟩ with
      ⟨_, _, _, _, _, hformula, _, _, hcoe, _, _, _⟩
    apply Subtype.ext
    rw [(hlaws.1 f g i).2.2 e k a he ha hp m y x (by simpa [hs'] using hs.symm)]
    rw [hcoe]
    rw [← hs, hs']
    exact (hformula e k a he ha hp y m).symm
  let fg := fun f g : Fidx ↦
    (⟨(f.val.1 * g.val.1, f.val.2 + g.val.2),
      Nat.add_pos_left f.property.1 g.val.2,
      SetLike.mul_mem_graded f.property.2 g.property.2⟩ : Fidx)
  have hprod (f g h : Fidx) : U f (fg g h) = U f g * U f h := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, hU, hU, hU, Localization.mk_mul]
    simp only [fg, mul_pow, pow_add]
    rfl
  dsimp only
  intro f n g hg hcover q hq
  let p (a b : Fidx) (i : D[b] ≤ D[a]) := (hlaws.1 a b i).1
  let u : Fin n → R[f] := fun i ↦ U f (g i)
  let E (i : Fin n) := theta f (g i) (p f (g i) (hg i))
  let s (i : Fin n) := (E i).symm (q i)
  have hu (i : Fin n) : u i =
      HomogeneousLocalization.Away.mk 𝒜 f.property.2 (g i).val.2
        ((g i).val.1 ^ f.val.2)
        (by simpa [smul_eq_mul, mul_comm] using
          SetLike.pow_mem_graded f.val.2 (g i).property.2) := by
    apply HomogeneousLocalization.val_injective
    simpa only [HomogeneousLocalization.Away.val_mk] using hU f (g i)
  have hspan : Ideal.span (Set.range u) = ⊤ := by
    have hh := (standardOpenProperties.{u, u, 0} 𝒜).2.2.2.2 f.val.1 f.val.2 f.property.1
      f.property.2 n (fun i ↦ (g i).val.1) (fun i ↦ (g i).val.2)
      (fun i ↦ (g i).property.1) (fun i ↦ (g i).property.2) |>.mp hcover.ge
    have hueq := funext hu
    rw [hueq]
    exact hh
  let loc (a : R[f]) := LocalizedModule.mkLinearMap (Submonoid.powers a) (Z f)
  let k (a b : R[f]) (hab : a ∣ b) :=
    IsLocalizedModule.lift (Submonoid.powers a) (loc a) (loc b)
      (RingTheory.localizationAway_map_units_of_dvd (M := Z f) a b hab)
  have hs : ∀ i j,
      k (u i) (u i * u j) (dvd_mul_right _ _) (s i) =
        k (u j) (u i * u j) (dvd_mul_left _ _) (s j) := by
    intro i j
    have hi : D[fg (g i) (g j)] ≤ D[g i] := by
      simpa only [fg, basicOpen_mul] using
        (inf_le_left : D[g i] ⊓ D[g j] ≤ D[g i])
    have hj : D[fg (g i) (g j)] ≤ D[g j] := by
      simpa only [fg, basicOpen_mul] using
        (inf_le_right : D[g i] ⊓ D[g j] ≤ D[g j])
    let t := p f (fg (g i) (g j)) (hi.trans (hg i))
    have hleft := hkappa f (g i) (fg (g i) (g j)) (p f (g i) (hg i))
      (p (g i) (fg (g i) (g j)) hi) t
    have hright := hkappa f (g j) (fg (g i) (g j)) (p f (g j) (hg j))
      (p (g j) (fg (g i) (g j)) hj) t
    obtain ⟨_, kl, hkl, hkluniq, hsql⟩ := hleft
    obtain ⟨_, kr, hkr, hkruniq, hsqr⟩ := hright
    -- Bind the comparison equivalence before rewriting its localization parameter.
    -- This transports the two commuting squares together with their common target.
    have hdata : ∃ (Eij : LocalizedModule.Away (U f (fg (g i) (g j))) (Z f) ≃+
        Z (fg (g i) (g j)))
        (kl : LocalizedModule.Away (u i) (Z f) →ₗ[R[f]]
          LocalizedModule.Away (U f (fg (g i) (g j))) (Z f))
        (kr : LocalizedModule.Away (u j) (Z f) →ₗ[R[f]]
          LocalizedModule.Away (U f (fg (g i) (g j))) (Z f)),
        (∀ K, (∀ x : Z f, K (mk x 1) = mk x 1) → K = kl) ∧
        (∀ K, (∀ x : Z f, K (mk x 1) = mk x 1) → K = kr) ∧
        (∀ x, r (g i) (fg (g i) (g j)) (p _ _ hi) (E i x) = Eij (kl x)) ∧
        (∀ x, r (g j) (fg (g i) (g j)) (p _ _ hj) (E j x) = Eij (kr x)) :=
      ⟨theta f (fg (g i) (g j)) t, kl, kr, hkluniq, hkruniq, hsql, hsqr⟩
    rw [hprod] at hdata
    obtain ⟨Eij, kl, kr, hkluniq, hkruniq, hsql, hsqr⟩ := hdata
    have hkl' : k (u i) (u i * u j) (dvd_mul_right _ _) = kl := by
      apply hkluniq
      intro x
      exact IsLocalizedModule.lift_apply _ _ _ _ x
    have hkr' : k (u j) (u i * u j) (dvd_mul_left _ _) = kr := by
      apply hkruniq
      intro x
      exact IsLocalizedModule.lift_apply _ _ _ _ x
    rw [hkl', hkr']
    apply Eij.injective
    rw [← hsql, ← hsqr]
    simp only [s, AddEquiv.apply_symm_apply]
    rw [← hr _ _ hi (p _ _ hi), ← hr _ _ hj (p _ _ hj)]
    exact hq i j
  obtain ⟨x, hx, huniq⟩ := (RingTheory.coverModuleExact (M := Z f) n u hspan).2 s hs
  refine ⟨x, ?_, ?_⟩
  · intro i
    rw [hr f (g i) (hg i) (p f (g i) (hg i))]
    have hh := congrArg (E i) (hx i)
    simpa only [E, LocalizedModule.mkLinearMap_apply, (htheta _ _ _).2.1,
      s, AddEquiv.apply_symm_apply] using hh
  · intro y hy
    apply huniq y
    intro i
    apply (E i).injective
    simpa only [E, LocalizedModule.mkLinearMap_apply, (htheta _ _ _).2.1,
      s, AddEquiv.apply_symm_apply, ← hr f (g i) (hg i) (p f (g i) (hg i))] using hy i

end AlgebraicGeometry.Proj
