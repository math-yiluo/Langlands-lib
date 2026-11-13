import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof

/-!
# The Gelfand–Kazhdan contragredient over every nonarchimedean local field

The published proofs of `GeneralLinearConjugationDistributionTransposeStatement` and
`GelfandKazhdanContragredientStatement` are stated for `PadicField` only, but use the
p-adic structure only to obtain topological properties of the field and of `GL_n`.
This module repeats their last specializations over an arbitrary nonarchimedean local
field `F` (any characteristic), with the topological certificates of
`Langlands.Group.GL.LocalFieldTopology` in place of the p-adic ones. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.LocalField

open HarmonicAnalysis HarmonicAnalysis.Distribution MeasureTheory MeasureTheory.Measure

universe uF uV

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.totallyDisconnectedSpace
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  LocalFieldTopology.generalLinear_sigmaCompactSpace
  LocalFieldTopology.generalLinear_nonarchimedean
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Bernstein–Zelevinsky (1976), §7.3, over every nonarchimedean local field: a
conjugation-invariant distribution on `GL_(n+1)(F)` is invariant under transposition. -/
theorem generalLinearConjugationDistributionTranspose (n : ℕ)
    (D : Distribution (Matrix.GeneralLinearGroup (Fin (n + 1)) F))
    (hD : IsConjugationInvariant D) : IsTransposeInvariant (n + 1) F D := by
  classical
  set τ := transposeHomeomorph (n + 1) F with hτ
  set q := charpolyCoeffs (K := F) (n + 1) with hq
  have hqconj : ∀ a g, q (a * g * a⁻¹) = q g := charpolyCoeffs_conj
  have hqτ : ∀ g, q (τ g) = q g := charpolyCoeffs_transpose
  -- Transposition preserves every conjugacy class.
  have hτconj : ∀ z : Matrix.GeneralLinearGroup (Fin (n + 1)) F,
      ∃ a, a * z * a⁻¹ = τ z := by
    intro z
    obtain ⟨a, ha⟩ := matrixTransposeConjugate F (n + 1) z
    exact ⟨a, Units.ext (by simpa only [Units.val_mul, hτ, transposeHomeomorph_coe] using ha)⟩
  have hτsymm : ∀ z, τ.symm z = τ z := fun z =>
    τ.symm_apply_eq.mpr (transposeHomeomorph_involutive (n + 1) F z).symm
  -- The difference is conjugation invariant and transpose anti-invariant.
  let D' := D - pushforward τ D
  have hDτ : IsConjugationInvariant (pushforward τ D) :=
    IsConjugationInvariant.pushforward_transpose (n + 1) F hD
  have hD'conj : IsConjugationInvariant D' := fun a => by
    simp only [D', map_sub, hD a, hDτ a]
  have hD'τ : pushforward τ D' = -D' := by
    simp only [D', map_sub, hτ, pushforward_transpose_involutive, neg_sub]
  -- Localization along the characteristic polynomial.
  let ι := Matrix.GeneralLinearGroup (Fin (n + 1)) F ⊕ Unit
  let h : ι → Matrix.GeneralLinearGroup (Fin (n + 1)) F ≃ₜ
      Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
    Sum.elim conjugationHomeomorph fun _ => τ
  let χ : ι → ℂ := Sum.elim (fun _ => 1) fun _ => -1
  have hfib : ∀ i x, q (h i x) = q x := by
    rintro (a | u) x
    · exact hqconj a x
    · exact hqτ x
  have hloc : ∀ (y : Fin (n + 1) → F)
      (T : Distribution (Matrix.GeneralLinearGroup (Fin (n + 1)) F)),
      (∀ f : SchwartzBruhat (Matrix.GeneralLinearGroup (Fin (n + 1)) F),
        (∀ x, q x = y → f x = 0) → T f = 0) →
      (∀ i, pushforward (h i) T = χ i • T) → T = 0 := by
    intro y T hT hTi
    have hTconj : IsConjugationInvariant T := fun a => by
      simpa [h, χ] using hTi (Sum.inl a)
    have hTτ : pushforward τ T = -T := by
      simpa [h, χ] using hTi (Sum.inr ())
    -- The fibre is a closed finite union of conjugacy classes.
    obtain ⟨s, hs⟩ : ∃ s : Finset (Matrix.GeneralLinearGroup (Fin (n + 1)) F),
        q ⁻¹' {y} = ⋃ x ∈ s, {g | ∃ a, a * x * a⁻¹ = g} := by
      by_cases hne : ∃ g₀, q g₀ = y
      · obtain ⟨g₀, hg₀⟩ := hne
        obtain ⟨s₀, hs₀⟩ := matrixCharpolyFiniteConjugacy F (n + 1)
          (g₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F).charpoly
        refine ⟨(s₀.preimage (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
          (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) Units.val_injective.injOn).filter
            (fun g => q g = y), ?_⟩
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
          Finset.mem_filter, exists_prop]
        constructor
        · intro hg
          have hc : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F).charpoly =
              (g₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) F).charpoly :=
            charpoly_eq_of_coeff_eq _ _ fun i => by
              have := congrFun (hg.trans hg₀.symm) i
              simpa only [hq, charpolyCoeffs] using this
          obtain ⟨y', hy's, k, hk⟩ := hs₀ _ hc
          refine ⟨k * g * k⁻¹, ⟨?_, ?_⟩, k⁻¹, ?_⟩
          · rw [Finset.mem_preimage, Units.val_mul, Units.val_mul, hk]
            exact hy's
          · rw [hqconj, hg]
          · group
        · rintro ⟨x, ⟨-, hx⟩, a, rfl⟩
          rw [hqconj, hx]
      · refine ⟨∅, ?_⟩
        ext g
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.notMem_empty,
          Set.iUnion_of_empty, Set.iUnion_empty, Set.mem_empty_iff_false, iff_false]
        exact fun hg => hne ⟨g, hg⟩
    refine conjugationInvariant_finiteOrbit_vanishing finiteOrbitAntiInvariantVanishing τ
      (q ⁻¹' {y}) s ((isClosed_singleton).preimage (continuous_charpolyCoeffs (n + 1))) hs
      (fun z _ => ⟨hτconj z, by rw [hτsymm]; exact hτconj z⟩) T
      (fun f hf => hT f fun x hx => hf x hx) hTconj hTτ
  have hD'i : ∀ i, pushforward (h i) D' = χ i • D' := by
    rintro (a | u)
    · simpa [h, χ] using hD'conj a
    · simpa [h, χ] using hD'τ
  have hD'0 : D' = 0 :=
    equivariantLocalization (Matrix.GeneralLinearGroup (Fin (n + 1)) F) (Fin (n + 1) → F) q
      (continuous_charpolyCoeffs (n + 1)) ι h χ hfib hloc D' hD'i
  have : D - pushforward τ D = 0 := hD'0
  exact (sub_eq_zero.mp this).symm

/-- Bernstein–Zelevinsky (1976), Theorem 7.3, over every nonarchimedean local field: an
irreducible admissible representation of `GL_(n+1)(F)`, composed with inverse transpose,
is equivalent to its smooth dual. -/
theorem gelfandKazhdanContragredient (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F) V)
    (hρ : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) :
    ∃ E : V ≃ₗ[ℂ] SmoothDual ρ, ∀ g v,
      E (ρ (GeneralLinear.inverseTranspose (n + 1) F g) v) =
        smoothContragredient ρ g (E v) := by
  let G := Matrix.GeneralLinearGroup (Fin (n + 1)) F
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ := RankinSelberg.generalLinearHaar F n
  obtain ⟨hinv, he, _, hconj⟩ := RankinSelberg.generalLinearHaarSymmetries F n
  let : IsInvInvariant μ := hinv
  let e := GeneralLinear.inverseTransposeContinuous (n + 1) F
  obtain ⟨hdual, hdualChar⟩ := characterTransport.1 G μ V ρ hρ
  obtain ⟨hpull, hpullChar⟩ := characterTransport.2 G μ e he V ρ hρ
  have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hLc, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hLc, hLK⟩
  have hdualIrr : Representation.IsIrreducible (smoothContragredient ρ) :=
    (isIrreducible_smoothContragredient_iff_of_bidual
      (fun W _ _ σ hσ => smoothBidual_injective_of_compact_cofinal hcofinal σ hσ)
      ρ hρ.1 ⟨smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ.1,
        smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ⟩).mpr hirr
  have hpullIrr : Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
    (isIrreducible_comp_continuousMulEquiv_iff ρ e).mpr hirr
  have hDconj : Distribution.IsConjugationInvariant (Character.distribution μ ρ hρ) :=
    Character.distribution_isConjugationInvariant_of_measurePreserving μ ρ hρ hconj
  have hDtrans := generalLinearConjugationDistributionTranspose F n
    (Character.distribution μ ρ hρ) hDconj
  have hchars : Character.distribution μ (ρ.comp e.toMonoidHom) hpull =
      Character.distribution μ (smoothContragredient ρ) hdual := by
    ext f
    rw [hpullChar, hdualChar]
    have htest : Hecke.TestFunction.pullback e.symm.toHomeomorph f =
        Hecke.TestFunction.pullback (Distribution.transposeHomeomorph (n + 1) F)
          (Hecke.TestFunction.inversion f) := by
      ext g
      change f (GeneralLinear.inverseTranspose (n + 1) F g) =
        f ((GeneralLinear.inverseTranspose (n + 1) F g⁻¹)⁻¹)
      rw [map_inv, inv_inv]
    rw [htest]
    exact (Distribution.isTransposeInvariant_iff _ _ _).mp hDtrans _
  exact (characterSeparation G μ V (SmoothDual ρ) (ρ.comp e.toMonoidHom)
    (smoothContragredient ρ) hpull hdual hpullIrr hdualIrr).mp hchars

end Langlands.LocalField
