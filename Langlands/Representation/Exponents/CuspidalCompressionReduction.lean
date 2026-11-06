import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingStatement
import Langlands.Representation.Jacquet.CompressionFiniteSupport
import Langlands.Representation.Jacquet.CompressionUniformity
import Langlands.Representation.Category.UniverseLift

/-! # Compression reduction through actual finite induced-cuspidal embeddings

Embedding an object and then its cokernel in finite induced-cuspidal sums
gives a left exact row. Eventual compression stability of cuspidal inductions
therefore implies pointwise stability and a representation-uniform threshold.
-/

noncomputable section

open CategoryTheory
open Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.Jacquet

universe uG uA uB uC

/-- Two eventually stable objects in a left exact row give eventual
stability of its kernel object, using a common larger stationary threshold. -/
theorem compressedAction_eventuallyStable_of_leftExact
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type uA} {B : Type uB} {C : Type uC}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C]
    {ρ : Representation ℂ G A} {σ : Representation ℂ G B}
    {τ : Representation ℂ G C}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (f : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hinj : Function.Injective f)
    (hexact : LinearMap.range f.toLinearMap = LinearMap.ker q.toLinearMap)
    (hB : EventuallyStable (compressedAction σ hσ K hK g))
    (hC : EventuallyStable (compressedAction τ hτ K hK g)) :
    EventuallyStable (compressedAction ρ hρ K hK g) := by
  obtain ⟨b, hb⟩ := (compactCompression_eventuallyStable_iff_exists_stationaryFrom
    σ hσ K hK g).mp hB
  obtain ⟨c, hc⟩ := (compactCompression_eventuallyStable_iff_exists_stationaryFrom
    τ hτ K hK g).mp hC
  let n := max 1 (max b c)
  refine ⟨n, by dsimp [n]; omega, ?_⟩
  exact compressedAction_stablePower_of_leftExact hρ hσ hτ K hK g f q hinj hexact n
    (compactCompressionStablePower_of_stationaryFrom σ hσ K hK g
      (hb.mono (by dsimp [n]; omega)))
    (compactCompressionStablePower_of_stationaryFrom τ hτ K hK g
      (hc.mono (by dsimp [n]; omega)))

end Langlands.Jacquet

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {κ : Type uG} [Fintype κ]
  (P M U : Finset κ → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset κ) (J : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I J)).subgroupOf (M I))
      ((M (leviIndex I J)).subgroupOf (M I)) ((U (leviIndex I J)).subgroupOf (M I)))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)

/-- Eventual compression stability on every actual normalized induction of
an arbitrary cuspidal object from one standard Levi. -/
def CuspidalInductionCompressionEventuallyStable : Prop :=
  ∀ (I : Finset κ) (A : SmoothRep.{0, uG, max uG uV} ℂ (M I)),
    IsLeviCuspidal P M U hU I (hM I) (hL I) A →
      EventuallyStable (Jacquet.compressedAction
        ((normalizedInductionFunctor (h I) (hU I)).obj A).representation
        ((normalizedInductionFunctor (h I) (hU I)).obj A).isSmooth K hK g)

private theorem finite_cuspidalInduced_sum_eventuallyStable
    (hstable : CuspidalInductionCompressionEventuallyStable.{uG, uV}
      P M U h hU hM hL K hK g)
    (A : ∀ I : Finset κ, SmoothRep.{0, uG, max uG uV} ℂ (M I))
    (hA : ∀ I, IsLeviCuspidal P M U hU I (hM I) (hL I) (A I)) :
    letI := Classical.decEq (Finset κ)
    let B := SmoothRep.directSum.{uG, uG, uV}
      (fun I => (normalizedInductionFunctor (h I) (hU I)).obj (A I))
    EventuallyStable (Jacquet.compressedAction B.representation B.isSmooth K hK g) := by
  classical
  exact Jacquet.compressedAction_eventuallyStable_directSum_of_finite_support
    (fun I => ((normalizedInductionFunctor (h I) (hU I)).obj (A I)).representation)
    (fun I => ((normalizedInductionFunctor (h I) (hU I)).obj (A I)).isSmooth)
    (SmoothRep.directSum.{uG, uG, uV}
      (fun I => (normalizedInductionFunctor (h I) (hU I)).obj (A I))).isSmooth
    K hK g (Set.toFinite _) (fun I => hstable I (A I) (hA I))

/-- The finite embedding theorem, used twice, reduces pointwise compression
stability to actual normalized induction of arbitrary cuspidal objects. -/
theorem pointwiseCompressionEventuallyStable_of_cuspidalInduced
    (hembed : FiniteCuspidalInducedEmbeddingTarget.{uG, uG, max uG uV}
      (P := P) (M := M) (U := U) (h := h) (hU := hU) (hM := hM) (hL := hL))
    (hstable : CuspidalInductionCompressionEventuallyStable.{uG, uV}
      P M U h hU hM hL K hK g) :
    Jacquet.PointwiseCompressionEventuallyStable.{uG, uV} K hK g := by
  classical
  have hsaturated : Jacquet.PointwiseCompressionEventuallyStable.{uG, max uG uV}
      K hK g := by
    intro E
    obtain ⟨A, hA, f, hf⟩ := hembed E
    let B := SmoothRep.directSum.{uG, uG, uV}
      (fun I => (normalizedInductionFunctor (h I) (hU I)).obj (A I))
    let Q := SmoothRep.quotient B f.range
    let q := SmoothRep.hom (SmoothRep.mkQ B f.range)
    obtain ⟨D, hD, j, hj⟩ := hembed Q
    let C := SmoothRep.directSum.{uG, uG, uV}
      (fun I => (normalizedInductionFunctor (h I) (hU I)).obj (D I))
    let r : B.representation.IntertwiningMap C.representation := j.comp q
    have hexact : LinearMap.range f.toLinearMap = LinearMap.ker r.toLinearMap := by
      ext b
      change b ∈ f.range.toSubmodule ↔ j (q b) = 0
      have hquot : q b = 0 ↔ b ∈ f.range.toSubmodule :=
        Submodule.Quotient.mk_eq_zero _
      exact hquot.symm.trans ⟨fun hz => by rw [hz, map_zero],
        fun hz => hj (hz.trans j.map_zero.symm)⟩
    exact Jacquet.compressedAction_eventuallyStable_of_leftExact
      E.isSmooth B.isSmooth C.isSmooth K hK g f r hf hexact
      (finite_cuspidalInduced_sum_eventuallyStable P M U h hU hM hL K hK g hstable A hA)
      (finite_cuspidalInduced_sum_eventuallyStable P M U h hU hM hL K hK g hstable D hD)
  intro E
  let E' := SmoothRep.universeLift.{uG} E
  obtain ⟨b, hb, hpower⟩ := hsaturated E'
  refine ⟨b, hb, ?_⟩
  exact Jacquet.compactCompressionStablePower_of_retract
    E.representation E'.representation E.isSmooth E'.isSmooth K hK g
    (SmoothRep.universeLiftEquiv.{uG} E).toIntertwiningMap
    (SmoothRep.universeLiftEquiv.{uG} E).symm.toIntertwiningMap
    (by ext x; rfl) b hpower

/-- The countable-sum diagonal argument supplies one stationary threshold
before every representation in the original independent carrier universe. -/
theorem uniformCompressionStationary_of_cuspidalInduced
    (hembed : FiniteCuspidalInducedEmbeddingTarget.{uG, uG, max uG uV}
      (P := P) (M := M) (U := U) (h := h) (hU := hU) (hM := hM) (hL := hL))
    (hstable : CuspidalInductionCompressionEventuallyStable.{uG, uV}
      P M U h hU hM hL K hK g) :
    Jacquet.UniformCompressionStationary.{uG, uV} K hK g :=
  Jacquet.uniformCompressionStationary_of_pointwise K hK g
    (pointwiseCompressionEventuallyStable_of_cuspidalInduced
      P M U h hU hM hL K hK g hembed hstable)

end Langlands.Aubert.General
