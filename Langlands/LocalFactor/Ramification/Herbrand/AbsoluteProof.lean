import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteStatement
import Langlands.LocalFactor.Ramification.Herbrand.TowerProof
import Langlands.LocalFactor.Ramification.InertiaPresentation

/-!
# Absolute upper ramification: endpoint, left continuity and finite images

Finite upper groups are locally constant from the left, which gives left
continuity of the absolute filtration. Herbrand's theorem for an inclusion of
actual finite Galois subfields, together with compactness of the absolute
Galois group, shows that the absolute upper group maps onto every finite upper
group. Since finite Galois groups are discrete, the image of a Krull closure is
the image of the subgroup, which gives the closed right limit images.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open Topology
open _root_.Langlands.Ramification.Padic

universe u uK uL

section Finite

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
  [IsScalarTower (Padic p) K F.Carrier]

/-- A finite upper group equals the upper groups at all indices slightly to its left. -/
theorem exists_lt_upperRamificationGroup_eq {v : ℝ} (hv : -1 < v) :
    ∃ w : ℝ, -1 < w ∧ w < v ∧
      Padic.upperRamificationGroup T K w = Padic.upperRamificationGroup T K v := by
  have hn : ((⌈herbrandPsi T K v⌉ : ℤ) : ℝ) - 1 < herbrandPsi T K v := by
    linarith [Int.ceil_lt_add_one (herbrandPsi T K v)]
  have h1 : ∀ᶠ w in 𝓝[<] v, ((⌈herbrandPsi T K v⌉ : ℤ) : ℝ) - 1 < herbrandPsi T K w :=
    mem_nhdsWithin_of_mem_nhds (((herbrandPsi_continuous T K).tendsto v).eventually
      (lt_mem_nhds hn))
  have h2 : ∀ᶠ w in 𝓝[<] v, -1 < w := mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hv)
  have h3 : ∀ᶠ w in 𝓝[<] v, w < v := self_mem_nhdsWithin
  obtain ⟨w, hw1, hw2, hw3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨w, hw2, hw3, ?_⟩
  rw [upperRamificationGroup_eq_lower, upperRamificationGroup_eq_lower, Int.ceil_eq_iff.mpr
    ⟨hw1, (herbrandPsi_strictMono T K hw3).le.trans (Int.le_ceil _)⟩]

end Finite

section Absolute

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The absolute filtration is the whole group at the left endpoint. -/
theorem absoluteUpperEndpoint : AbsoluteUpperEndpoint F :=
  absoluteUpperRamificationGroup_neg_one F

/-- Left continuity of the absolute filtration inside Serre's domain. -/
theorem absoluteUpperLeftContinuity : AbsoluteUpperLeftContinuity F := by
  intro v hv
  apply le_antisymm
  · exact le_iInf₂ fun w hw => absoluteUpperRamificationGroup_antitone F hw.2.le
  · intro σ hσ
    rw [mem_absoluteUpperRamificationGroup_iff]
    intro L
    obtain ⟨w, hw, hwv, heq⟩ := exists_lt_upperRamificationGroup_eq
      (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier hv
    have h := (mem_absoluteUpperRamificationGroup_iff F w σ).mp
      (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hσ w) ⟨hw.le, hwv⟩) L
    rw [canonicalUpperRamificationGroup, ← heq]
    exact h

/-- Restriction from the absolute Galois group to an actual finite Galois subfield
is surjective. -/
theorem absoluteFiniteRestriction_surjective
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    Function.Surjective (absoluteFiniteRestriction F L) := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  exact AlgEquiv.restrictNormalHom_surjective (F := F.Carrier)
    (E := AlgebraicClosure F.Carrier) (K₁ := L)

variable {F}

/-- Restriction to a smaller finite Galois subfield factors absolute restriction. -/
theorem finiteGaloisRestriction_absoluteFiniteRestriction
    {L M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}
    (h : L ≤ M) (σ : Field.absoluteGaloisGroup F.Carrier) :
    finiteGaloisRestriction F h (absoluteFiniteRestriction F M σ) =
      absoluteFiniteRestriction F L σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [finiteGaloisRestriction_apply]
  exact (σ.restrictNormal_commutes M (IntermediateField.inclusion h x)).trans
    (σ.restrictNormal_commutes L x).symm

/-- Herbrand's theorem for an inclusion of actual finite Galois subfields. -/
theorem map_finiteGaloisRestriction_upper
    {L M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}
    (h : L ≤ M) {v : ℝ} (hv : -1 ≤ v) :
    (canonicalUpperRamificationGroup (absoluteFiniteExtension F M) F.Carrier v).map
        (finiteGaloisRestriction F h).toMonoidHom =
      canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v := by
  let : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower F.Carrier L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois L M := IsGalois.tower_top_of_isGalois F.Carrier L M
  exact upperRestrictionCompatibility F (absoluteFiniteExtension F M)
    (absoluteFiniteExtension F L) (absoluteFiniteExtension F M).canonicalTopologicalData
    (absoluteFiniteExtension F L).canonicalTopologicalData v hv

variable (F)

/-- The absolute Galois elements that restrict to `τ` on `L` and whose restriction to `M`
lies in the canonical upper group of index `v`. -/
def upperLiftSet (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (τ : Gal(L/F.Carrier)) (v : ℝ)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :
    Set (Field.absoluteGaloisGroup F.Carrier) :=
  {σ | absoluteFiniteRestriction F L σ = τ ∧ absoluteFiniteRestriction F M σ ∈
    canonicalUpperRamificationGroup (absoluteFiniteExtension F M) F.Carrier v}

/-- The absolute upper group maps onto every finite upper group. -/
theorem absoluteUpperFiniteImage : AbsoluteUpperFiniteImage F := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  intro L v hv
  apply le_antisymm (absoluteUpperRamificationGroup_map_restriction_le F v L)
  intro τ hτ
  let t := upperLiftSet F L τ v
  have hcl : ∀ M, IsClosed (t M) := fun M =>
    ((isClosed_discrete {τ}).preimage (absoluteFiniteRestriction F L).continuous).inter
      ((isClosed_discrete _).preimage (absoluteFiniteRestriction F M).continuous)
  have hmono : ∀ {M N : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)},
      M ≤ N → t N ⊆ t M := by
    intro M N h σ hσ
    refine ⟨hσ.1, ?_⟩
    rw [← finiteGaloisRestriction_absoluteFiniteRestriction h σ,
      ← map_finiteGaloisRestriction_upper h hv]
    exact Subgroup.mem_map_of_mem _ hσ.2
  have hne : ∀ M, (t M).Nonempty := by
    intro M
    rw [← map_finiteGaloisRestriction_upper (le_sup_right : L ≤ M ⊔ L) hv] at hτ
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hτ
    obtain ⟨σ, rfl⟩ := absoluteFiniteRestriction_surjective F (M ⊔ L) τ'
    exact ⟨σ, hmono le_sup_left
      ⟨(finiteGaloisRestriction_absoluteFiniteRestriction (le_sup_right : L ≤ M ⊔ L) σ).symm,
        hτ'⟩⟩
  have hdir : Directed (· ⊇ ·) t := fun M N =>
    ⟨M ⊔ N, hmono le_sup_left, hmono le_sup_right⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
    hne (fun M => (hcl M).isCompact) hcl
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, ?_, (hσ L).1⟩
  exact (mem_absoluteUpperRamificationGroup_iff F v σ).mpr fun M => (hσ M).2

/-- An image in an actual finite Galois group does not see the Krull closure. -/
theorem map_topologicalClosure_absoluteFiniteRestriction
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (H : Subgroup (Field.absoluteGaloisGroup F.Carrier)) :
    H.topologicalClosure.map (absoluteFiniteRestriction F L).toMonoidHom =
      H.map (absoluteFiniteRestriction F L).toMonoidHom := by
  apply le_antisymm _ (Subgroup.map_mono H.le_topologicalClosure)
  rw [Subgroup.map_le_iff_le_comap]
  have hc := (isClosed_discrete
    ((H.map (absoluteFiniteRestriction F L).toMonoidHom : Subgroup _) : Set _)).preimage
      (absoluteFiniteRestriction F L).continuous
  exact H.topologicalClosure_minimal (Subgroup.le_comap_map _ H) hc

/-- The closed right limit of the absolute filtration has the finite right limit
as its image. -/
theorem absoluteUpperClosedRightImage : AbsoluteUpperClosedRightImage F := by
  intro L v hv
  rw [map_topologicalClosure_absoluteFiniteRestriction, Subgroup.map_iSup]
  refine iSup_congr fun w => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hw => absoluteUpperFiniteImage F L w (hv.trans hw.le)

end Absolute

end Langlands.Ramification.HerbrandBridge
