import Langlands.BaseChange.TwistedCharacter.Devissage
import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Smooth.FixedVectors.JacquetDetectionProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # Restriction of compactly dominated forms along smooth induction -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis Induction MeasureTheory

universe uG uM uX

section FixedVectors

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [T2Space M] [LocallyCompactSpace M] [TotallyDisconnectedSpace M]

/-- A uniform inducing-group level suffices for detecting ambient fixed vectors. -/
def SmoothInducedFixedVanishingStatement (P : Subgroup G) (p : P →* M)
    (K : OpenSubgroup G) : Prop :=
  ∃ J : OpenSubgroup M, IsCompact (J : Set M) ∧
    ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ M X),
      fixedVectors Ξ J.toSubgroup = ⊥ →
      fixedVectors (smoothInduced P (Ξ.comp p)) K.toSubgroup = ⊥

/-- Intersect the images of the stabilizers of a finite double-coset cover. -/
theorem smoothInducedFixedVanishing (P : Subgroup G) [CompactSpace (LeftQuotient P)]
    (p : P →* M) (hp : IsOpenMap p) (K : OpenSubgroup G) :
    SmoothInducedFixedVanishingStatement.{uG,uM,uX} P p K := by
  classical
  obtain ⟨t, ht⟩ := exists_finset_doubleCoset_cover P K
  let H (i : t) := conjOpenSubgroup P K i
  let L (i : t) : OpenSubgroup M := ⟨(H i).toSubgroup.map p, hp _ (H i).isOpen⟩
  obtain ⟨J, hJle, hJ, _⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance M ∅ (Finset.univ.inf L)
  refine ⟨J, hJ, ?_⟩
  intro X _ _ Ξ hbot
  let ρ := Ξ.comp p
  have hzero (i : t) : fixedVectors ρ (H i).toSubgroup = ⊥ := by
    rw [fixedVectors_comp_eq_map]
    have hJi : J ≤ L i := hJle.trans (Finset.inf_le (Finset.mem_univ i))
    exact le_bot_iff.mp ((fixedVectors_antitone Ξ hJi).trans_eq hbot)
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have h : fixedEvaluation P ρ K t ⟨v, hv⟩ = 0 := by
    funext i
    apply Subtype.ext
    have hi := (fixedEvaluation P ρ K t ⟨v, hv⟩ i).property
    change eval P ρ v i ∈ fixedVectors ρ (H i).toSubgroup at hi
    exact (Submodule.eq_bot_iff _).mp (hzero i) _ hi
  rw [← map_zero (fixedEvaluation P ρ K t)] at h
  exact congrArg Subtype.val (fixedEvaluation_injective P ρ K t ht h)

end FixedVectors

section Functional

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : MulAut G)

/-- The domination level for irreducible distributions also annihilates the trace
of a finite-length pair invisible at that level. -/
theorem compactDomination_apply_of_finiteLength
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (Φ : Module.Dual ℂ (Distribution G))
    (hΦ : ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G X)
      (hπ : IsAdmissible π), π.IsIrreducible → fixedVectors π K.toSubgroup = ⊥ →
        ∀ A : π.Equiv (π.comp θ.toMonoidHom), Φ (twistedDistribution μ π hπ A.toLinearMap) = 0)
    (B : SmoothRep.{0,uG,uX} ℂ G) (hB : B.IsAdmissible) (hFin : B.HasFiniteLength)
    (hBot : fixedVectors B.representation K.toSubgroup = ⊥)
    (A : B.representation.Equiv (B.representation.comp θ.toMonoidHom)) :
    Φ (twistedDistribution μ B.representation hB A.toLinearMap) = 0 := by
  apply LinearMap.mem_ker.mp
  apply twistedDistribution_mem_of_finiteLength μ θ Φ.ker B hB hFin A
  intro D hD hI hSub C
  apply LinearMap.mem_ker.mpr
  apply hΦ D D.representation hD hI _ C
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  by_contra hv₀
  obtain ⟨w, hw, hw₀⟩ := SmoothRep.exists_nonzero_fixedVector_of_isSubquotient K hK hSub
    ⟨v, hv, hv₀⟩
  exact hw₀ ((Submodule.eq_bot_iff _).mp hBot w hw)

variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [T2Space M] [LocallyCompactSpace M] [TotallyDisconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (ν : Measure M) [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant]
  (θM : MulAut M)

/-- A trace transfer for finite-length inductions pulls compactly dominated functionals
back to compactly dominated functionals. -/
theorem compactlyDominatedFunctional_comp_induction
    (hθ : Continuous θ) (hθ' : Continuous θ.symm)
    (P : Subgroup G) [CompactSpace (LeftQuotient P)] (hP : ∀ g, θ g ∈ P ↔ g ∈ P)
    (p : P →* M) (hpo : IsOpenMap p)
    (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x))
    (T : Distribution M →ₗ[ℂ] Distribution G)
    (hT : ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X]
      (Ξ : Representation ℂ M X) (hΞ : IsAdmissible Ξ), Ξ.IsIrreducible →
      ∀ B : Ξ.Equiv (Ξ.comp θM.toMonoidHom),
        ∃ hI : IsAdmissible (smoothInduced P (Ξ.comp p)),
          (SmoothRep.of _ hI.1).HasFiniteLength ∧
            T (twistedDistribution ν Ξ hΞ B.toLinearMap) =
              twistedDistribution μ _ hI
                (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B).toLinearMap)
    (Φ : Module.Dual ℂ (Distribution G))
    (hΦ : IsCompactlyDominatedFunctional.{uG,max uG uX} θ μ Φ) :
    IsCompactlyDominatedFunctional.{uM,uX} θM ν (Φ.comp T) := by
  obtain ⟨K, hK, hVan⟩ := hΦ
  obtain ⟨J, hJ, hFixed⟩ := smoothInducedFixedVanishing.{uG,uM,uX} P p hpo K
  refine ⟨J, hJ, ?_⟩
  intro X _ _ Ξ hΞ hIrr hBot B
  obtain ⟨hI, hFin, he⟩ := hT X Ξ hΞ hIrr B
  change Φ (T (twistedDistribution ν Ξ hΞ B.toLinearMap)) = 0
  rw [he]
  exact compactDomination_apply_of_finiteLength μ θ K hK Φ hVan
    (SmoothRep.of _ hI.1) hI hFin (hFixed X Ξ hBot) _

end Functional

end Langlands.BaseChange
