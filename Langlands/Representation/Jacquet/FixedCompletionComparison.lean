import Langlands.Representation.Jacquet.CompletionCharacterization
import Langlands.Representation.Smooth.CompactCompletionMaps

/-!
# Fixed completion and Jacquet completion

The opposite contraction basis supplies both cofinality inputs. Stationarity
identifies the fixed completion with stable families, giving the actual Jacquet
completion equivalence, its component formula, and naturality.
-/

noncomputable section

namespace Langlands.Jacquet

open Langlands.HarishChandraSchwartz Langlands.CompactCompletion

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (N M Nbar : Subgroup G) (g : G)

omit [IsTopologicalGroup G] in
/-- An opposite contraction basis is cofinal for ambient completion. -/
theorem oppositeCompressionIndices_cofinal
    (hBasis : HasOppositeIwahoriContractionBasis N M Nbar g) :
    CompactCompletion.IsCofinal (oppositeCompressionIndices N M Nbar g) := by
  intro J
  obtain ⟨K, hK, hKJ, h, hopp⟩ := hBasis J.1 J.1.isOpen J.1.one_mem
  exact ⟨⟨K, hK⟩, ⟨h, hopp⟩, hKJ⟩

omit [IsTopologicalGroup G] in
/-- The same basis is cofinal after intersecting with the closed Levi. -/
theorem oppositeCompressionIndices_levi_cofinal
    (hM : IsClosed (M : Set G))
    (hBasis : HasOppositeIwahoriContractionBasis N M Nbar g) :
    CompactCompletion.IsCofinal
      (leviCompactIndex M hM '' oppositeCompressionIndices N M Nbar g) := by
  apply leviCompactIndex_cofinal
  intro O hO h1
  obtain ⟨K, hK, hKO, h, hopp⟩ := hBasis O hO h1
  exact ⟨⟨K, hK⟩, ⟨h, hopp⟩, hKO⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (hMN : M ≤ Subgroup.normalizer N)
variable (hMNbar : M ≤ Subgroup.normalizer Nbar)
variable (hcentral : ∀ m ∈ M, m * g = g * m)
variable (hM : IsClosed (M : Set G)) (hNbar : IsClosed (Nbar : Set G))
variable (hBasis : HasOppositeIwahoriContractionBasis N M Nbar g)
variable (hcover : ∀ h ∈ Nbar, ∃ C : Subgroup G,
  IsCompact (C : Set G) ∧ C ≤ Nbar ∧ h ∈ C)
variable (hstationary : ∀ K ∈ oppositeCompressionIndices N M Nbar g,
  ∃ b : ℕ, stableImage ρ hρ K.1 K.2 g =
    LinearMap.range (compressedAction ρ hρ K.1 K.2 g ^ b))

/-- Identify lower-fixed and stable completion families without changing their
components. The structural and stationary-image assumptions are explicit. -/
def fixedCompletionStableEquiv :
    completionFixed ρ hρ Nbar ≃ₗ[ℂ] stableImageCompletion ρ hρ N M Nbar g where
  toFun v := ⟨v.val, by
    rw [stableImageCompletion_eq_completionFixed ρ hρ N M Nbar g hNbar hMNbar
      hcentral hBasis hcover hstationary]
    exact v.property⟩
  invFun v := ⟨v.val, by
    rw [← stableImageCompletion_eq_completionFixed ρ hρ N M Nbar g hNbar hMNbar
      hcentral hBasis hcover hstationary]
    exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hbij : ∀ K : oppositeCompressionIndices N M Nbar g,
  Function.Bijective (stableImageJacquetMap ρ hρ K.1.1 K.1.2 g N M hMN))

/-- The fixed-completion Jacquet equivalence under explicit basis, compact
covering, stationarity, and pointwise stable Jacquet bijectivity inputs. -/
def fixedCompletionJacquetEquiv :
    completionFixed ρ hρ Nbar ≃ₗ[ℂ]
      completion (action ρ N M hMN) (isSmooth_action ρ N M hMN hρ) :=
  (fixedCompletionStableEquiv N M Nbar g ρ hρ hMNbar hcentral hNbar hBasis
      hcover hstationary).trans
    (stableCompletionJacquetEquiv ρ hρ N M Nbar g hMN hMNbar hcentral hM
      (oppositeCompressionIndices_cofinal N M Nbar g hBasis)
      (oppositeCompressionIndices_levi_cofinal N M Nbar g hM hBasis) hbij)

/-- A good smaller ambient index computes each Levi component. -/
theorem fixedCompletionJacquetEquiv_apply
    (v : completionFixed ρ hρ Nbar) (J : CompactOpenSubgroup M)
    (K : oppositeCompressionIndices N M Nbar g)
    (hKJ : (leviCompactIndex M hM K.val).1 ≤ J.1) :
    (fixedCompletionJacquetEquiv N M Nbar g ρ hρ hMN hMNbar hcentral hM hNbar
      hBasis hcover hstationary hbij v).val J =
      Compact.averageMap (action ρ N M hMN) (isSmooth_action ρ N M hMN hρ)
        J.1 J.2 (mk ρ N (v.val.val K.val)) := by
  exact stableCompletionJacquetMap_apply ρ hρ N M Nbar g hMN hcentral hM
    (oppositeCompressionIndices_cofinal N M Nbar g hBasis)
    (oppositeCompressionIndices_levi_cofinal N M Nbar g hM hBasis) _ J K hKJ

/-- The quotient-component characterization at every Iwahori factorization. -/
theorem fixedCompletionJacquetEquiv_apply_of_factor
    (v : completionFixed ρ hρ Nbar) (K : CompactOpenSubgroup G)
    (hfactor : ∀ k ∈ K.1, ∃ l ∈ K.1.toSubgroup ⊓ Nbar,
      ∃ m ∈ K.1.toSubgroup ⊓ M, ∃ u ∈ K.1.toSubgroup ⊓ N, k = l * m * u) :
    (fixedCompletionJacquetEquiv N M Nbar g ρ hρ hMN hMNbar hcentral hM hNbar
      hBasis hcover hstationary hbij v).val (leviCompactIndex M hM K) =
        mk ρ N (v.val.val K) := by
  exact stableCompletionJacquetMap_apply_of_factor ρ hρ N M Nbar g hMN hMNbar
    hcentral hM hNbar (oppositeCompressionIndices_cofinal N M Nbar g hBasis)
    (oppositeCompressionIndices_levi_cofinal N M Nbar g hM hBasis)
    (fixedCompletionStableEquiv N M Nbar g ρ hρ hMNbar hcentral hNbar hBasis
      hcover hstationary v) K hfactor

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (σ : Representation ℂ G W) (hσ : IsSmooth σ)
variable (hstationaryσ : ∀ K ∈ oppositeCompressionIndices N M Nbar g,
  ∃ b : ℕ, stableImage σ hσ K.1 K.2 g =
    LinearMap.range (compressedAction σ hσ K.1 K.2 g ^ b))
variable (hbijσ : ∀ K : oppositeCompressionIndices N M Nbar g,
  Function.Bijective (stableImageJacquetMap σ hσ K.1.1 K.1.2 g N M hMN))

/-- Componentwise related fixed families have componentwise related Jacquet
completions, for the actual quotient map induced by the intertwiner. -/
theorem fixedCompletionJacquetEquiv_natural
    (f : ρ.IntertwiningMap σ) (v : completionFixed ρ hρ Nbar)
    (w : completionFixed σ hσ Nbar)
    (hvw : ∀ K : CompactOpenSubgroup G, w.val.val K = f (v.val.val K))
    (J : CompactOpenSubgroup M) :
    (fixedCompletionJacquetEquiv N M Nbar g σ hσ hMN hMNbar hcentral hM hNbar
      hBasis hcover hstationaryσ hbijσ w).val J =
      map N M hMN f
        ((fixedCompletionJacquetEquiv N M Nbar g ρ hρ hMN hMNbar hcentral hM hNbar
          hBasis hcover hstationary hbij v).val J) := by
  obtain ⟨_, ⟨K, hKS, rfl⟩, hKJ⟩ :=
    oppositeCompressionIndices_levi_cofinal N M Nbar g hM hBasis J
  rw [fixedCompletionJacquetEquiv_apply N M Nbar g σ hσ hMN hMNbar hcentral hM
      hNbar hBasis hcover hstationaryσ hbijσ w J ⟨K, hKS⟩ hKJ,
    fixedCompletionJacquetEquiv_apply N M Nbar g ρ hρ hMN hMNbar hcentral hM
      hNbar hBasis hcover hstationary hbij v J ⟨K, hKS⟩ hKJ,
    hvw, ← map_mk N M hMN f]
  exact (LinearMap.congr_fun
    (Compact.averageMap_commute (action ρ N M hMN) (action σ N M hMN)
      (isSmooth_action ρ N M hMN hρ) (isSmooth_action σ N M hMN hσ)
      J.1 J.2 (map N M hMN f)) (mk ρ N (v.val.val K))).symm

end Langlands.Jacquet
