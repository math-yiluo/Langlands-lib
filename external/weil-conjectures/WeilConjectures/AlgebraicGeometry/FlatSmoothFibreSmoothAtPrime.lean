/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionSmoothJacobian
import WeilConjectures.RingTheory.SmoothLocalCompleteIntersection
import WeilConjectures.RingTheory.SmoothFibreLocalizedPresentationJacobian
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection

/-!
# Flat with smooth fibre implies smooth at a prime

Source: Stacks Project, Algebra, Lemma 00TF (lemma-flat-fibre-smooth)
(blueprint: lem-weil-pbc-flat-smooth-fibre-smooth-at-prime).
-/

@[expose] public section

universe u v

/-- Global complete intersections are invariant under algebra equivalence. -/
private theorem globalCI_equiv {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : Algebra.IsGlobalCompleteIntersection k A) :
    Algebra.IsGlobalCompleteIntersection k B := by
  rcases h with h | ⟨n, c, f, hcn, ⟨ef⟩, hdim⟩
  · exact Or.inl (e.toEquiv.subsingleton_congr.mp h)
  · refine Or.inr ⟨n, c, f, hcn, ⟨ef.trans e⟩, ?_⟩
    rw [← (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).isHomeomorph.topologicalKrullDim_eq]
    exact hdim

/-- A smooth neighbourhood over a field can be shrunk to a global complete intersection. -/
private theorem exists_globalCI_of_smoothAt {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] (q : PrimeSpectrum A) (h : Algebra.IsSmoothAtPrime k q) :
    ∃ a : A, a ∉ q.asIdeal ∧
      Algebra.IsGlobalCompleteIntersection k (Localization.Away a) := by
  obtain ⟨g, hg, hsm⟩ := h
  have := hsm
  let B := Localization.Away g
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
    rw [PrimeSpectrum.localization_away_comap_range B g]
    exact hg
  obtain ⟨qB, hqB⟩ := hq
  obtain ⟨s, hs, hci⟩ := Algebra.isLocalCompleteIntersection_of_smooth k B
  have hcover : qB ∈ (⨆ a ∈ s, PrimeSpectrum.basicOpen a) := by rw [hs]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hcover
  obtain ⟨a, ha, hqa⟩ := hcover
  let b := (IsLocalization.Away.sec g a).1
  have hab : Associated (algebraMap A B b) a :=
    IsLocalization.Away.associated_sec_fst g a
  have hb : b ∉ q.asIdeal := by
    intro hb
    have hbB : algebraMap A B b ∈ qB.asIdeal := by
      change b ∈ qB.asIdeal.comap (algebraMap A B)
      simpa [← hqB] using hb
    exact hqa (qB.asIdeal.mem_of_dvd hab.dvd hbB)
  have : IsLocalization.Away (g * b) (Localization.Away a) :=
    IsLocalization.Away.mul_of_associated g b a hab
  refine ⟨g * b, q.asIdeal.primeCompl.mul_mem hg hb, ?_⟩
  exact globalCI_equiv
    ((IsLocalization.algEquiv (.powers (g * b)) (Localization.Away a)
      (Localization.Away (g * b))).restrictScalars k) (hci a ha)

/-- Smoothness at a prime is invariant under algebra equivalence. -/
private theorem smoothAt_equiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (q : PrimeSpectrum B)
    (h : Algebra.IsSmoothAtPrime R q) :
    Algebra.IsSmoothAtPrime R (PrimeSpectrum.comap e.toRingHom q) := by
  obtain ⟨b, hb, hsm⟩ := h
  have := hsm
  refine ⟨e.symm b, ?_, ?_⟩
  · simpa using hb
  · exact Algebra.Smooth.of_equiv
      (IsLocalization.algEquivOfAlgEquiv (M := .powers b) (T := .powers (e.symm b))
        (Localization.Away b) (Localization.Away (e.symm b)) e.symm
        (Submonoid.map_powers e.symm b))

/-- A smooth neighbourhood of a point of a principal localization descends to the ring. -/
private theorem smoothAt_of_away {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (g : A) (qB : PrimeSpectrum (Localization.Away g))
    (h : Algebra.IsSmoothAtPrime R qB) :
    Algebra.IsSmoothAtPrime R
      (PrimeSpectrum.comap (algebraMap A (Localization.Away g)) qB) := by
  let B := Localization.Away g
  obtain ⟨a, ha, hsm⟩ := h
  have := hsm
  let b := (IsLocalization.Away.sec g a).1
  have hab : Associated (algebraMap A B b) a :=
    IsLocalization.Away.associated_sec_fst g a
  have hb : b ∉ (PrimeSpectrum.comap (algebraMap A B) qB).asIdeal := by
    intro hb
    exact ha (qB.asIdeal.mem_of_dvd hab.dvd hb)
  have hg : g ∉ (PrimeSpectrum.comap (algebraMap A B) qB).asIdeal := by
    exact fun hmem ↦ qB.isPrime.ne_top
      (qB.asIdeal.eq_top_of_isUnit_mem hmem (IsLocalization.Away.algebraMap_isUnit g))
  have : IsLocalization.Away (g * b) (Localization.Away a) :=
    IsLocalization.Away.mul_of_associated g b a hab
  refine ⟨g * b, (PrimeSpectrum.comap (algebraMap A B) qB).asIdeal.primeCompl.mul_mem hg hb, ?_⟩
  exact Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (.powers (g * b)) (Localization.Away a)
      (Localization.Away (g * b))).restrictScalars R)

/-- Let `R → S` be a ring map, `q` a prime of `S` and `p = q ∩ R`. If `S_g` is a finitely
presented `R`-algebra for some `g ∉ q`, the local map `R_p → S_q` is flat, and the fibre
`κ(p) ⊗[R] S` (`p.Fiber S`) is smooth over `κ(p)` at the prime `Q` corresponding to `q`
(`PrimeSpectrum.preimageEquivFiber`, the kernel of `κ(p) ⊗[R] S → κ(q)`), then `R → S` is
smooth at `q`. Smoothness at a prime is `Algebra.IsSmoothAtPrime` (`∃ g ∉ q, S_g` smooth).
Source: Stacks Project, Algebra, Lemma 00TF (lemma-flat-fibre-smooth).
(blueprint: lem-weil-pbc-flat-smooth-fibre-smooth-at-prime)

Proof, following the node:
1. By (3) some `F_h`, `h ∉ Q`, is smooth over `κ(p)`, hence a local complete intersection;
shrinking, some `F_{h'}`, `h' ∉ Q`, is a global complete intersection over `κ(p)`.
2. With (1), (2) and step 1, the syntomic-at-a-prime lemma gives `g ∉ q` and an
`R`-isomorphism of `S_g` with a relative global complete intersection
`T = R[x_1,…,x_n]/(f_1,…,f_c)`, and the prime `q_T` corresponding to `q`.
3. The fibre `F_T = T ⊗_R κ(p)` is `κ(p)[x]/(f̄)` and is `F_{ḡ}`, matching `Q_T` with `Q`.
4. `κ(p) → F_T` is a relative global complete intersection smooth at `Q_T`.
5. The Jacobian criterion gives a maximal minor `g_I` with `ḡ_I ⊗ 1 ∉ Q_T`.
6. Hence `ḡ_I ∉ q_T` and the Jacobian criterion for `R → T` gives `t ∉ q_T` with `T_t` smooth.
7. Writing `θ⁻¹(t) = s/g^m`, `S_{gs} ≅ T_t` is smooth with `gs ∉ q`. -/
theorem flat_smooth_fibre_smooth_at_prime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ Algebra.FinitePresentation R (Localization.Away g))
    (hflat : (Localization.localRingHom (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
      q.asIdeal (algebraMap R S) rfl).Flat)
    (hsmooth : Algebra.IsSmoothAtPrime (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
      (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q) ⟨q, rfl⟩)) :
    Algebra.IsSmoothAtPrime R q := by
  have hci := exists_globalCI_of_smoothAt _ hsmooth
  obtain ⟨g, hg, n, c, f, hf, ⟨e⟩⟩ :=
    Algebra.exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime q hfp hflat hci
  have hq : q ∈ Set.range
      (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hg
  obtain ⟨qg, hqg⟩ := hq
  let qT := PrimeSpectrum.comap e.symm.toRingHom qg
  have hminor := Algebra.exists_jacobian_minor_of_smooth_fibre_localizedPresentation
    q g qg hqg n c f hf e hsmooth
  have hT : Algebra.IsSmoothAtPrime R qT :=
    (Algebra.isSmoothAtPrime_iff_exists_jacobian_minor R n c f hf qT).mpr hminor
  have hgsm : Algebra.IsSmoothAtPrime R qg := by
    have h := smoothAt_equiv e qT hT
    have heq : PrimeSpectrum.comap e.toRingHom qT = qg := by
      ext x
      change e.symm (e x) ∈ qg.asIdeal ↔ x ∈ qg.asIdeal
      rw [e.symm_apply_apply]
    rwa [heq] at h
  simpa [hqg] using smoothAt_of_away g qg hgsm
