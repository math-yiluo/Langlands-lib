import Langlands.Geometry.FormalGroup.PiDivisible

/-! # Finite-kernel composition and pointwise rank: the remaining proof target -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw.Hom

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

/-- The actual composite kernel has a finite projective representation, with
pointwise rank the product of the ranks of the two actual kernel models.
Only the first arrow is required to have affine fppf local lifting. -/
def FiniteKernelCompositionStatement
    (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) (P : ModuleLaw O R υ) : Prop :=
  ∀ (f : Hom M N) (g : Hom N P), f.IsFppfLocallySurjective →
    ∀ (K : FiniteKernelModel f) (L : FiniteKernelModel g),
      ∃ H : FiniteKernelModel (g.comp f),
        ∀ p : PrimeSpectrum R, H.rank p = K.rank p * L.rank p

/-- This exact proof target is sufficient for the missing isogeny-composition law. -/
theorem IsIsogeny.comp_of_finiteKernelComposition
    (h : FiniteKernelCompositionStatement M N P)
    {f : Hom M N} {g : Hom N P} (hg : g.IsIsogeny) (hf : f.IsIsogeny) :
    (g.comp f).IsIsogeny := by
  obtain ⟨K⟩ := hf.2
  obtain ⟨L⟩ := hg.2
  obtain ⟨H, -⟩ := h f g hf.1 K L
  exact ⟨hg.1.comp hf.1, ⟨H⟩⟩

/-- Pointwise rank multiplicativity implies the constant-rank composition law. -/
theorem HasKernelRank.comp_of_finiteKernelComposition
    (h : FiniteKernelCompositionStatement M N P)
    {f : Hom M N} {g : Hom N P} (hf : f.IsFppfLocallySurjective) {m n : ℕ}
    (hfr : f.HasKernelRank m) (hgr : g.HasKernelRank n) :
    (g.comp f).HasKernelRank (m * n) := by
  obtain ⟨K, hK⟩ := hfr
  obtain ⟨L, hL⟩ := hgr
  obtain ⟨H, hH⟩ := h f g hf K L
  exact ⟨H, fun p => (hH p).trans (by rw [hK p, hL p])⟩

/-- The same proof target suffices for additive kernel-rank heights. -/
theorem HasHeight.comp_of_finiteKernelComposition
    (h : FiniteKernelCompositionStatement M N P)
    {f : Hom M N} {g : Hom N P} {q i j : ℕ}
    (hg : g.HasHeight q j) (hf : f.HasHeight q i) :
    (g.comp f).HasHeight q (i + j) := by
  refine ⟨hg.1.comp_of_finiteKernelComposition h hf.1, ?_⟩
  rw [pow_add]
  exact hf.2.comp_of_finiteKernelComposition h hf.1.1 hg.2

end Langlands.FormalGroup.ModuleLaw.Hom
