/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Local clearing of denominators for twist sections

Source: Stacks Project, Section 27.8, construction preceding Lemma 27.8.4, Tag 01M7.
(blueprint: lem-sc-proj-twist-local-clearing)
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry.Proj

/-- A twist section has a cleared representative on a principal neighborhood of each
point of the affine chart.
Source: Stacks Project, Section 27.8, Lemma 27.8.1 and the construction preceding
Lemma 27.8.4, Tag 01M7, specialized to the shift A(k).
(blueprint: lem-sc-proj-twist-local-clearing)

Proof: transport x to D₊(f) under its canonical affine chart. The locally-fraction
predicate gives a homogeneous fraction a/d on a neighborhood V of that point. Choose
an open D₊(u) containing the point and contained in V, with u homogeneous. Multiply
both a and d by u*f, giving N=a*u*f and h=d*u*f. The degree c of h is positive since
f has degree b>0, and D₊(h) lies in V and D₊(f). In B=A_(f) put g=h^b/f^c; the chart
identifies D₊(h) with D(g), so x lies in D(g). Put z=h^(b-1)*N/f^c in A_f. At any p
where the canonical image of g is a unit, the image of h is a unit: the image of f
already is, and h^b/f^c is a unit with b>0. In the prime localization this says h
avoids the prime, hence p lies in D₊(h). The section value there is N/h, and
(h^b/f^c)*(N/h)=h^(b-1)*N/f^c, the image of z. This is the displayed identity.
The construction does not require a to be nonzero or k to be nonnegative. If the
chart is empty (including nilpotent f), there is no x and the assertion is vacuous. -/
theorem twist_local_clearing
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f)))
    (x : PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f)) :
    ∃ (g : HomogeneousLocalization.Away 𝒜 f) (z : Localization.Away f),
      x ∈ PrimeSpectrum.basicOpen g ∧
      ∀ p : basicOpen 𝒜 f,
        let F := IsLocalization.map (M := Submonoid.powers f)
          (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
          (Submonoid.powers_le.mpr p.2)
        IsUnit (F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
          (Localization.Away f) g)) →
        F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
          (Localization.Away f) g) * (s.1 p).1 = F z := by
  classical
  obtain ⟨y, rfl⟩ :=
    ProjIsoSpecTopComponent.toSpec_surjective 𝒜 hf hb x
  obtain ⟨V, hyV, jV, i, j, hij, a, d, hd, hs⟩ := s.2 y
  obtain ⟨U, ⟨u, rfl⟩, hyu, huV⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open hyV V.isOpen
  have hyproj : y.1 ∈ ⨆ l, ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 l u) := by
    rw [← ProjectiveSpectrum.basicOpen_eq_union_of_projection]
    exact hyu
  obtain ⟨l, hyl⟩ := TopologicalSpace.Opens.mem_iSup.mp hyproj
  let u' := GradedRing.proj 𝒜 l u
  have hu' : u' ∈ 𝒜 l := SetLike.coe_mem _
  have hu'V : (ProjectiveSpectrum.basicOpen 𝒜 u' : Set (ProjectiveSpectrum 𝒜)) ⊆ V.1 := by
    apply Set.Subset.trans _ huV
    change ProjectiveSpectrum.basicOpen 𝒜 u' ≤ ProjectiveSpectrum.basicOpen 𝒜 u
    rw [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 u]
    exact le_iSup (fun l => ProjectiveSpectrum.basicOpen 𝒜 (GradedRing.proj 𝒜 l u)) l
  let h : A := (d : A) * u' * f
  let c := j + l + b
  have hh : h ∈ 𝒜 c := SetLike.mul_mem_graded (SetLike.mul_mem_graded d.2 hu') hf
  let g := HomogeneousLocalization.Away.isLocalizationElem hf hh
  let N : A := (a : A) * u' * f
  let z : Localization.Away f := Localization.mk (h ^ (b - 1) * N)
    ⟨f ^ c, ⟨c, rfl⟩⟩
  refine ⟨g, z, ?_, ?_⟩
  · change g ∉ (ProjIsoSpecTopComponent.toSpec 𝒜 f y).asIdeal
    change HomogeneousLocalization.mk _ ∉ _
    apply (ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier y _).not.mpr
    change h ^ b ∉ y.1.asHomogeneousIdeal
    apply (y.1.isPrime.pow_mem_iff_mem b hb).not.mpr
    exact y.1.isPrime.mul_notMem
      (y.1.isPrime.mul_notMem (hd ⟨y.1, hyV⟩) hyl) y.2
  · intro p F hunit
    have hFg : F (algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (Localization.Away f) g) =
        Localization.mk (h ^ b)
          ⟨f ^ c, p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem p.2 c⟩ := by
      dsimp [F, g, HomogeneousLocalization.Away.isLocalizationElem]
      simp only [Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
    have hhp : h ∉ p.1.asHomogeneousIdeal := by
      rw [hFg, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hunit
      exact fun hhmem => hunit (p.1.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hhmem b hb)
    have hup : u' ∉ p.1.asHomogeneousIdeal := by
      intro humem
      exact hhp (Ideal.mul_mem_right f _
        (Ideal.mul_mem_left p.1.asHomogeneousIdeal.toIdeal (d : A) humem))
    have hpV : p.1 ∈ V := hu'V hup
    have hsp : (s.1 p).1 =
        Localization.mk (a : A) ⟨(d : A), hd ⟨p.1, hpV⟩⟩ := by
      have heq := congrArg Subtype.val (hs ⟨p.1, hpV⟩)
      exact heq
    have hFz : F z = Localization.mk (h ^ (b - 1) * N)
        ⟨f ^ c, p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem p.2 c⟩ := by
      dsimp [F, z]
      simp only [Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
    rw [hFg, hsp, hFz, Localization.mk_mul, Localization.mk_eq_mk_iff]
    apply Localization.r_iff_exists.mpr
    refine ⟨1, ?_⟩
    dsimp
    simp only [one_mul]
    have hpow : h ^ b = h ^ (b - 1) * h := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    dsimp [h, N]
    ring

end AlgebraicGeometry.Proj

