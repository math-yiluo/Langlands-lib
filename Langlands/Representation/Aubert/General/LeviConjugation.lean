import Langlands.Representation.Aubert.General.GroupTransport

/-! # Conjugating normalized functors between actual ambient Levi subgroups -/

noncomputable section

open CategoryTheory Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uG uV

namespace LeviConjugation

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {M Q L N M' Q' L' N' : Subgroup G}

section Functors

variable (hM : IsClosed (M : Set G)) (hM' : IsClosed (M' : Set G))
  (hLM : L ≤ M) (hL'M' : L' ≤ M')
  (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
  (h' : IsSemidirectDecomposition (Q'.subgroupOf M') (L'.subgroupOf M') (N'.subgroupOf M'))
  (hN : IsClosed (N : Set G)) (hN' : IsClosed (N' : Set G))
  (g : G)
  (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
  (hLL' : ∀ x : G, x ∈ L' ↔ g⁻¹ * x * g ∈ L)
  (hQQ' : ∀ x : M', (x : G) ∈ Q' ↔ g⁻¹ * (x : G) * g ∈ Q)
  (hNN' : ∀ x : M', (x : G) ∈ N' ↔ g⁻¹ * (x : G) * g ∈ N)

/-- Compare actual Levi-in-Levi induction, retaining the ambient subgroup
models on both sides. Only the parabolics restricted to the ambient Levis
are required to correspond. -/
def inductionIso :
    leviNormalizedInductionFunctor.{uG, uV} hM hLM h hN ⋙
        conjugationFunctor g hMM' ≅
      conjugationFunctor g hLL' ⋙
        leviNormalizedInductionFunctor hM' hL'M' h' hN' := by
  letI := hM.locallyCompactSpace
  letI := hM'.locallyCompactSpace
  exact Functor.isoWhiskerLeft
    (SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM))
    (GroupTransport.inductionIso h h' (conjugationEquiv g hMM')
      hQQ' (fun x => hLL' x) hNN'
      (hN.preimage continuous_subtype_val) (hN'.preimage continuous_subtype_val))

omit hQQ' in
/-- Compare actual Levi-in-Levi Jacquet restriction, with the actual
descendant Levis as codomains. -/
def jacquetIso :
    leviNormalizedJacquetFunctor.{uG, uV} hM hLM h hN ⋙
        conjugationFunctor g hLL' ≅
      conjugationFunctor g hMM' ⋙
        leviNormalizedJacquetFunctor hM' hL'M' h' hN' := by
  letI := hM.locallyCompactSpace
  letI := hM'.locallyCompactSpace
  exact Functor.isoWhiskerRight
    (GroupTransport.jacquetIso h h' (conjugationEquiv g hMM')
      (fun x => hLL' x) hNN'
      (hN.preimage continuous_subtype_val) (hN'.preimage continuous_subtype_val))
    (SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hL'M').symm)

end Functors

section Maps

variable (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
  (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
  (hN : IsClosed (N : Set G))
  (hfl : letI := hM.locallyCompactSpace
    ParabolicFiniteLength.{uG, max uG uV} h (hN.preimage continuous_subtype_val))

/-- Normalized induction from the actual ambient descendant subgroup, on
exact finite-length K0. The finite-length data concern the literal restricted
decomposition. -/
def inductionMap :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ L →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ M :=
  letI := hM.locallyCompactSpace
  (inductionK0 h (hN.preimage continuous_subtype_val) hfl.1 hfl.2.1).comp
    (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM))

/-- Normalized Jacquet restriction to the actual ambient descendant subgroup,
on exact finite-length K0. -/
def jacquetMap :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ M →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ L :=
  letI := hM.locallyCompactSpace
  (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM).symm).comp
    (jacquetK0 h (hN.preimage continuous_subtype_val) hfl.2.2.1 hfl.2.2.2)

/-- The induction adapter is the exact-K0 map of the actual
`leviNormalizedInductionFunctor`. -/
theorem inductionMap_eq_map :
    letI := hM.locallyCompactSpace
    inductionMap.{uG, uV} hM hLM h hN hfl =
      FiniteLengthGrothendieckGroup.map
        (leviNormalizedInductionFunctor hM hLM h hN)
        ((SmoothRep.pullbackFunctor_preservesFiniteLength
          (subgroupOfContinuousEquiv hLM)).comp hfl.1)
        (PreservesFiniteLengthShortExact.comp
          (SmoothRep.pullbackFunctor_preservesFiniteLength
            (subgroupOfContinuousEquiv hLM))
          (SmoothRep.pullbackFunctor_preservesShortExact
            (subgroupOfContinuousEquiv hLM)) hfl.2.1) := by
  let _ := hM.locallyCompactSpace
  exact (FiniteLengthGrothendieckGroup.map_comp _ _
    (SmoothRep.pullbackFunctor_preservesFiniteLength _)
    (SmoothRep.pullbackFunctor_preservesShortExact _) hfl.1 hfl.2.1 _ _).symm

/-- The Jacquet adapter is the exact-K0 map of the actual
`leviNormalizedJacquetFunctor`. -/
theorem jacquetMap_eq_map :
    letI := hM.locallyCompactSpace
    jacquetMap.{uG, uV} hM hLM h hN hfl =
      FiniteLengthGrothendieckGroup.map
        (leviNormalizedJacquetFunctor hM hLM h hN)
        (hfl.2.2.1.comp (SmoothRep.pullbackFunctor_preservesFiniteLength
          (subgroupOfContinuousEquiv hLM).symm))
        (PreservesFiniteLengthShortExact.comp hfl.2.2.1 hfl.2.2.2
          (SmoothRep.pullbackFunctor_preservesShortExact
            (subgroupOfContinuousEquiv hLM).symm)) := by
  let _ := hM.locallyCompactSpace
  exact (FiniteLengthGrothendieckGroup.map_comp _ _ hfl.2.2.1 hfl.2.2.2
    (SmoothRep.pullbackFunctor_preservesFiniteLength _)
    (SmoothRep.pullbackFunctor_preservesShortExact _) _ _).symm

/-- The two canonical subgroup-copy transports cancel. Hence induction after
Jacquet restriction is exactly the original restricted term. -/
theorem inductionMap_comp_jacquetMap :
    letI := hM.locallyCompactSpace
    (inductionMap.{uG, uV} hM hLM h hN hfl).comp
        (jacquetMap hM hLM h hN hfl) =
      (inductionK0 h (hN.preimage continuous_subtype_val) hfl.1 hfl.2.1).comp
        (jacquetK0 h (hN.preimage continuous_subtype_val) hfl.2.2.1 hfl.2.2.2) := by
  let _ := hM.locallyCompactSpace
  have hinv :
      (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM)).comp
          (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM).symm) =
        LinearMap.id :=
    FiniteLengthGrothendieckGroup.pullback_symm_comp
      (subgroupOfContinuousEquiv hLM).symm
  calc
    _ = (inductionK0 h (hN.preimage continuous_subtype_val) hfl.1 hfl.2.1).comp
        (((FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM)).comp
          (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM).symm)).comp
            (jacquetK0 h (hN.preimage continuous_subtype_val) hfl.2.2.1 hfl.2.2.2)) := by
      rfl
    _ = _ := by rw [hinv, LinearMap.id_comp]

end Maps

section TransportMaps

variable (hM : IsClosed (M : Set G)) (hM' : IsClosed (M' : Set G))
  (hLM : L ≤ M) (hL'M' : L' ≤ M')
  (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
  (h' : IsSemidirectDecomposition (Q'.subgroupOf M') (L'.subgroupOf M') (N'.subgroupOf M'))
  (hN : IsClosed (N : Set G)) (hN' : IsClosed (N' : Set G))
  (g : G)
  (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
  (hLL' : ∀ x : G, x ∈ L' ↔ g⁻¹ * x * g ∈ L)
  (hQQ' : ∀ x : M', (x : G) ∈ Q' ↔ g⁻¹ * (x : G) * g ∈ Q)
  (hNN' : ∀ x : M', (x : G) ∈ N' ↔ g⁻¹ * (x : G) * g ∈ N)
  (hfl : letI := hM.locallyCompactSpace
    ParabolicFiniteLength.{uG, max uG uV} h (hN.preimage continuous_subtype_val))
  (hfl' : letI := hM'.locallyCompactSpace
    ParabolicFiniteLength.{uG, max uG uV} h' (hN'.preimage continuous_subtype_val))

include hQQ' hNN' in
/-- The exact-K0 induction square in the ambient subgroup models. -/
theorem inductionMap_transport :
    (conjugationK0.{uG, max uG uV} g hMM').comp
        (inductionMap hM hLM h hN hfl) =
      (inductionMap hM' hL'M' h' hN' hfl').comp (conjugationK0 g hLL') := by
  let _ := hM.locallyCompactSpace
  let _ := hM'.locallyCompactSpace
  have hcopy :
      (FiniteLengthGrothendieckGroup.pullback
        (GroupTransport.subgroupEquiv (conjugationEquiv g hMM') (fun x => hLL' x))).comp
          (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM)) =
        (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hL'M')).comp
          (conjugationK0.{uG, max uG uV} g hLL') := by
    rw [conjugationK0, ← FiniteLengthGrothendieckGroup.pullback_trans,
      ← FiniteLengthGrothendieckGroup.pullback_trans]
    congr 1
  unfold inductionMap conjugationK0
  rw [← LinearMap.comp_assoc,
    GroupTransport.inductionK0_transport h h' (conjugationEquiv g hMM')
      hQQ' (fun x => hLL' x) hNN'
      (hN.preimage continuous_subtype_val) (hN'.preimage continuous_subtype_val)
      hfl.1 hfl.2.1 hfl'.1 hfl'.2.1,
    LinearMap.comp_assoc, hcopy, ← LinearMap.comp_assoc]
  rfl

include hNN' in
/-- The exact-K0 Jacquet square in the ambient subgroup models. -/
theorem jacquetMap_transport :
    (conjugationK0.{uG, max uG uV} g hLL').comp
        (jacquetMap hM hLM h hN hfl) =
      (jacquetMap hM' hL'M' h' hN' hfl').comp (conjugationK0 g hMM') := by
  let _ := hM.locallyCompactSpace
  let _ := hM'.locallyCompactSpace
  have hcopy :
      (conjugationK0.{uG, max uG uV} g hLL').comp
          (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hLM).symm) =
        (FiniteLengthGrothendieckGroup.pullback (subgroupOfContinuousEquiv hL'M').symm).comp
          (FiniteLengthGrothendieckGroup.pullback
            (GroupTransport.subgroupEquiv (conjugationEquiv g hMM')
              (P := L.subgroupOf M) (Q := L'.subgroupOf M')
              (fun x => hLL' x))) := by
    rw [conjugationK0, ← FiniteLengthGrothendieckGroup.pullback_trans,
      ← FiniteLengthGrothendieckGroup.pullback_trans]
    congr 1
  unfold jacquetMap
  rw [← LinearMap.comp_assoc, hcopy, LinearMap.comp_assoc,
    GroupTransport.jacquetK0_transport h h' (conjugationEquiv g hMM')
      (fun x => hLL' x) hNN'
      (hN.preimage continuous_subtype_val) (hN'.preimage continuous_subtype_val)
      hfl.2.2.1 hfl.2.2.2 hfl'.2.2.1 hfl'.2.2.2,
    ← LinearMap.comp_assoc]
  rfl

include hLL' hQQ' hNN' in
/-- The exact-K0 induction-after-Jacquet square, expressed entirely in the
actual ambient subgroup models. -/
theorem inductionJacquetMap_transport :
    (conjugationK0.{uG, max uG uV} g hMM').comp
        ((inductionMap hM hLM h hN hfl).comp (jacquetMap hM hLM h hN hfl)) =
      ((inductionMap hM' hL'M' h' hN' hfl').comp
        (jacquetMap hM' hL'M' h' hN' hfl')).comp (conjugationK0 g hMM') := by
  calc
    _ = ((conjugationK0 g hMM').comp (inductionMap hM hLM h hN hfl)).comp
        (jacquetMap hM hLM h hN hfl) := rfl
    _ = ((inductionMap hM' hL'M' h' hN' hfl').comp
        (conjugationK0 g hLL')).comp (jacquetMap hM hLM h hN hfl) := by
      rw [inductionMap_transport hM hM' hLM hL'M' h h' hN hN'
        g hMM' hLL' hQQ' hNN' hfl hfl']
    _ = (inductionMap hM' hL'M' h' hN' hfl').comp
        ((conjugationK0 g hLL').comp (jacquetMap hM hLM h hN hfl)) := rfl
    _ = (inductionMap hM' hL'M' h' hN' hfl').comp
        ((jacquetMap hM' hL'M' h' hN' hfl').comp (conjugationK0 g hMM')) := by
      rw [jacquetMap_transport hM hM' hLM hL'M' h h' hN hN'
        g hMM' hLL' hNN' hfl hfl']
    _ = _ := rfl

end TransportMaps

end LeviConjugation
end Langlands.Aubert.General
