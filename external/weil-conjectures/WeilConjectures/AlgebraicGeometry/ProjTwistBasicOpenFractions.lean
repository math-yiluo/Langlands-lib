/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionRealization
import WeilConjectures.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-!
# Basic-open fractions for a single Proj twist

Source: Stacks Project, Constructions, Tags 01MN (1) and 01M7 (2),(3).
-/

@[expose] public section

universe v

open CategoryTheory Opposite LocalizedModule

namespace AlgebraicGeometry.Proj

/-- The locally-fraction construction of one twist has its usual homogeneous fraction chart.
Source: Stacks Project, Constructions, Definition 27.10.1 (1), Tag 01MN, and
Lemma 27.8.4 (2),(3), Tag 01M7.
(blueprint: lem-sc-proj-single-twist-basic-open-fractions)

Proof: map a homogeneous fraction y/f^m of degree k to the section that at a homogeneous
prime p in D₊(f) is the image of that fraction in the degree-k part of A_p. Equality in the
localization implies equality of sections. Conversely a locally-fraction section on D₊(f)
is represented on a finite basic-open cover by homogeneous fractions. Such a finite cover
exists because D₊(f) is affine for f homogeneous of positive degree. Clear denominators on
that cover and then clear the finitely many witnesses of equality on the overlaps. The usual
localization gluing argument gives a single fraction with denominator a power of f; its
numerator has degree k+m*b. Injectivity follows by the same finite covering and denominator
clearing argument applied to a section equal to zero. Thus the inverse chart embeds sections
in the ordinary localized module and has the displayed range. Degrees below zero have zero
numerator by the convention A_n=0 for n<0. Multiplication of pointwise fractions identifies
the scalar action with the homogeneous-localization algebra map. If g^e=h*f, the canonical
localization map sends y/f^m to h^m*y/g^(e*m), and both sections have identical values at
every prime in D₊(g), proving restriction compatibility. If f is nilpotent D₊(f) is empty
and the localization is zero, so all assertions hold. -/
theorem single_twist_basicOpen_fractions
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    ∃ beta : ∀ (k : ℤ) (f : A) (b : ℕ), 0 < b → f ∈ 𝒜 b →
      (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f A,
    (∀ (k : ℤ) (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b),
      Function.Injective (beta k f b hb hf) ∧
      Set.range (beta k f b hb hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set A))
        (fun n : ℕ ↦ {y : A | if 0 ≤ k + n then y ∈ 𝒜 (k + n).toNat else y = 0})
        (Submonoid.powers f)) ∧
    (∀ (k : ℤ) (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b)
      (q : HomogeneousLocalization.Away 𝒜 f)
      (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))),
      beta k f b hb hf (awayToSection 𝒜 f q • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) q •
          beta k f b hb hf s) ∧
    (∀ (k : ℤ) (f g : A) (b c : ℕ) (hb : 0 < b) (hc : 0 < c)
      (hf : f ∈ 𝒜 b) (hg : g ∈ 𝒜 c) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e t : ℕ) (h : A), 0 < e → h ∈ 𝒜 t → g ^ e = h * f →
      ∀ (m : ℕ) (y : A) (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))),
        beta k f b hb hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
        beta k g c hc hg ((twist 𝒜 k).val.map (homOfLE inc).op s) =
          mk (h ^ m • y)
            (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by
  classical
  let ev (f : A) (p : basicOpen 𝒜 f) :
      Localization.Away f →+* Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal :=
    IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
  let B (k : ℤ) (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b)
      (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :=
    (twist_fraction_descent 𝒜 k f b hb hf s).choose
  have spec (k : ℤ) (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b)
      (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :=
    (twist_fraction_descent 𝒜 k f b hb hf s).choose_spec
  let beta (k : ℤ) (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b) :
      (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f A :=
    { toFun := B k f b hb hf
      map_zero' := by
        apply basicOpen_localization_detection 𝒜 f b hb hf
        intro p
        exact (spec k f b hb hf 0).2 p |>.trans (map_zero (ev f p)).symm
      map_add' := by
        intro s t
        apply basicOpen_localization_detection 𝒜 f b hb hf
        intro p
        rw [map_add]
        exact ((spec k f b hb hf (s + t)).2 p).trans
          (congrArg₂ (· + ·) ((spec k f b hb hf s).2 p)
            ((spec k f b hb hf t).2 p)).symm }
  have val (k : ℤ) (f : A) (b : ℕ) (hb : 0 < b) (hf : f ∈ 𝒜 b)
      (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) (p : basicOpen 𝒜 f) :
      ev f p (beta k f b hb hf s) = (s.1 p).1 := (spec k f b hb hf s).2 p
  refine ⟨beta, ?_, ?_, ?_⟩
  · intro k f b hb hf
    refine ⟨?_, ?_⟩
    · intro s t h
      apply Subtype.ext
      funext p
      apply Subtype.ext
      exact (val k f b hb hf s p).symm.trans
        ((congrArg (ev f p) h).trans (val k f b hb hf t p))
    · ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact (spec k f b hb hf s).1
      · intro hz
        obtain ⟨s, hs⟩ := twist_fraction_realization 𝒜 k f z hz
        refine ⟨s, ?_⟩
        apply basicOpen_localization_detection 𝒜 f b hb hf
        intro p
        exact (val k f b hb hf s p).trans (hs p).symm
  · intro k f b hb hf q s
    apply basicOpen_localization_detection 𝒜 f b hb hf
    intro p
    rw [val k f b hb hf]
    change ((awayToSection 𝒜 f q).1 p).val * (s.1 p).1 = _
    rw [show algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) q =
      q.val from rfl]
    rw [smul_eq_mul, map_mul, val k f b hb hf]
    congr 1
    exact ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f q p
  · intro k f g b c hb hc hf hg inc e t h he ht heq m y s hs
    apply basicOpen_localization_detection 𝒜 g c hc hg
    intro p
    rw [val k g c hc hg]
    change (s.1 ⟨p.1, inc p.2⟩).1 = _
    rw [← val k f b hb hf s ⟨p.1, inc p.2⟩, hs]
    change ev f ⟨p.1, inc p.2⟩ (Localization.mk y _) =
      ev g p (Localization.mk (h ^ m * y) _)
    simp only [ev, Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply]
    apply IsLocalization.mk'_eq_of_eq
    change f ^ m * (h ^ m * y) = g ^ (e * m) * y
    rw [pow_mul, heq, mul_pow]
    ring


end AlgebraicGeometry.Proj
