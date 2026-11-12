import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionRegularityProof

/-! # Algebra laws for compact distribution convolution -/

noncomputable section

open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution

universe uX uY uG

section Tensor

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] in
/-- The reverse order of the two actual algebraic partial evaluations. -/
theorem tensor_fubini (T : Distribution X) (S : Distribution Y)
    (f : SchwartzBruhat (X × Y)) : tensor T S f = S (partialApplyFst T f) := by
  classical
  obtain ⟨n, a, b, hf⟩ := SchwartzBruhat.exists_tensor_expansion f
  have he : f = ∑ i, SchwartzBruhat.tensor (a i) (b i) := by
    ext ⟨x, y⟩
    simpa using hf x y
  rw [he]
  simp only [map_sum, tensor_apply_tensor, partialApplyFst_tensor, map_smul,
    smul_eq_mul]

/-- Only support containment is needed for the compact tensor comparison. -/
theorem support_tensor_subset (T : Distribution X) (S : Distribution Y) :
    support (tensor T S) ⊆ support T ×ˢ support S := by
  apply support_subset_of_mem_supportedOn ((isClosed_support T).prod (isClosed_support S))
  intro f hf
  apply mem_supportedOn_support T
  intro x hx
  apply mem_supportedOn_support S
  intro y hy
  exact hf (x, y) ⟨hx, hy⟩

def compactTensor (T : compactlySupported (X := X)) (S : compactlySupported (X := Y)) :
    compactlySupported (X := X × Y) :=
  ⟨tensor (T : Distribution X) (S : Distribution Y),
    (T.property.prod S.property).of_isClosed_subset (isClosed_support _)
      (support_tensor_subset _ _)⟩

theorem compactPairing_partial_eq (T : compactlySupported (X := X))
    (S : compactlySupported (X := Y)) (h : LocallyConstant (X × Y) ℂ)
    (f : SchwartzBruhat (X × Y))
    (hf : ∀ x ∈ support (T : Distribution X), ∀ y ∈ support (S : Distribution Y),
      f (x, y) = h (x, y)) :
    compactSupportPairing T (compactPartial S h) =
      tensor (T : Distribution X) (S : Distribution Y) f := by
  apply compactSupportPairing_eq_of_agrees
  intro x hx
  change _ = compactSupportPairing S _
  symm
  apply compactSupportPairing_eq_of_agrees
  intro y hy
  exact hf x hx y hy

theorem compactPairing_partial_congr (T : compactlySupported (X := X))
    (S : compactlySupported (X := Y)) {h k : LocallyConstant (X × Y) ℂ}
    (he : ∀ x ∈ support (T : Distribution X), ∀ y ∈ support (S : Distribution Y),
      h (x, y) = k (x, y)) :
    compactSupportPairing T (compactPartial S h) =
      compactSupportPairing T (compactPartial S k) := by
  apply compactSupportPairing_congr
  intro x hx
  apply compactSupportPairing_congr
  exact he x hx

theorem compactPairing_tensor (T : compactlySupported (X := X))
    (S : compactlySupported (X := Y)) (h : LocallyConstant (X × Y) ℂ) :
    compactSupportPairing (compactTensor T S) h =
      compactSupportPairing T (compactPartial S h) := by
  obtain ⟨f, hf⟩ := exists_testFunction_agrees_on_compact (T.property.prod S.property) h
  rw [compactSupportPairing_eq_of_agrees (compactTensor T S) h f
    (fun p hp => hf p (support_tensor_subset _ _ hp))]
  exact (compactPairing_partial_eq T S h f (fun x hx y hy => hf (x, y) ⟨hx, hy⟩)).symm

/-- Fubini for extended evaluation, on arbitrary locally constant kernels. -/
theorem compactPairing_swap (T : compactlySupported (X := X))
    (S : compactlySupported (X := Y)) (h : LocallyConstant (X × Y) ℂ) :
    compactSupportPairing T (compactPartial S h) =
      compactSupportPairing S (compactPartial T
        ⟨fun p : Y × X => h (p.2, p.1),
          h.isLocallyConstant.comp_continuous continuous_swap⟩) := by
  obtain ⟨f, hf⟩ := exists_testFunction_agrees_on_compact (T.property.prod S.property) h
  rw [compactPairing_partial_eq T S h f (fun x hx y hy => hf (x, y) ⟨hx, hy⟩),
    tensor_fubini]
  symm
  apply compactSupportPairing_eq_of_agrees
  intro y hy
  symm
  apply compactSupportPairing_eq_of_agrees
  intro x hx
  exact hf (x, y) ⟨hx, hy⟩

end Tensor

section Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Pullback by group multiplication on all locally constant functions. -/
def mulFunction (f : LocallyConstant G ℂ) : LocallyConstant (G × G) ℂ :=
  ⟨fun p => f (p.1 * p.2),
    f.isLocallyConstant.comp_continuous (continuous_fst.mul continuous_snd)⟩

/-- The support-based definition agrees with iterated extended evaluation. -/
theorem convolution_eq_pairing (T S : compactlySupported (X := G))
    (f : SchwartzBruhat G) :
    (convolution T S : Distribution G) f =
      compactSupportPairing T (compactPartial S
        (mulFunction ⟨(f : G → ℂ), f.locallyConstant⟩)) := by
  rw [convolution_apply, compactSupportPairing_apply]
  change onSupport T _ = onSupport T _
  congr 1

/-- The convolution evaluation formula also holds on all smooth functions. -/
theorem compactSupportPairing_convolution (T S : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) :
    compactSupportPairing (convolution T S) f =
      compactSupportPairing T (compactPartial S (mulFunction f)) := by
  obtain ⟨g, hg⟩ := exists_testFunction_agrees_on_compact (T.property.mul S.property) f
  rw [compactSupportPairing_eq_of_agrees (convolution T S) f g
    (fun x hx => hg x (support_convolutionDistribution_subset T S hx)),
    convolution_eq_pairing]
  apply compactPairing_partial_congr
  intro x hx y hy
  exact hg (x * y) ⟨x, hx, y, hy, rfl⟩

theorem convolution_associative (T S R : compactlySupported (X := G)) :
    convolution (convolution T S) R = convolution T (convolution S R) := by
  apply Subtype.ext
  ext f
  rw [convolution_eq_pairing, convolution_eq_pairing, compactSupportPairing_convolution]
  apply compactSupportPairing_congr
  intro x _
  change compactSupportPairing S _ = compactSupportPairing (convolution S R) _
  rw [compactSupportPairing_convolution]
  apply compactSupportPairing_congr
  intro y _
  apply compactSupportPairing_congr
  intro z _
  exact congrArg f (mul_assoc x y z)

end Group

namespace RenardConvolution

theorem ambientTensor : AmbientTensorStatement.{uG} := by
  intro G _ _ _ _ _ _ T S
  refine ⟨(compactTensor T S).property, ?_⟩
  intro f
  rw [convolution_eq_pairing]
  exact (compactPairing_tensor T S _).symm

theorem associativity : AssociativityStatement.{uG} := by
  intro G _ _ _ _ _ _ T S R
  exact convolution_associative T S R

end RenardConvolution
end Langlands.HarmonicAnalysis.Distribution
