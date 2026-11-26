import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.Representation.Category.CentralCharacterRegularity
import Langlands.Representation.Hecke.RenardTestDecompositionProof

/-! # Regularity of a twisted trace on unramified twists of a fixed representation -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

universe uG uV

section CharacterOperations

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction along a continuous group homomorphism preserves unramifiedness. -/
theorem IsUnramifiedCharacter.comp_of_continuous {ψ : H →* ℂˣ} (hψ : IsUnramifiedCharacter ψ)
    (f : G →* H) (hf : Continuous f) : IsUnramifiedCharacter (ψ.comp f) := by
  intro K hK k hk
  apply hψ (K.map f)
  · rw [Subgroup.coe_map]
    exact hK.image hf
  · exact ⟨k, hk, rfl⟩

/-- Products of unramified characters are unramified. -/
theorem IsUnramifiedCharacter.mul {ψ η : G →* ℂˣ}
    (hψ : IsUnramifiedCharacter ψ) (hη : IsUnramifiedCharacter η) :
    IsUnramifiedCharacter (ψ * η) := by
  intro K hK k hk
  change ψ k * η k = 1
  rw [hψ K hK k hk, hη K hK k hk, mul_one]

/-- The inverse of an unramified character is unramified. -/
theorem IsUnramifiedCharacter.inv {ψ : G →* ℂˣ} (hψ : IsUnramifiedCharacter ψ) :
    IsUnramifiedCharacter ψ⁻¹ := by
  intro K hK k hk
  change (ψ k)⁻¹ = 1
  rw [hψ K hK k hk, inv_one]

end CharacterOperations

section TestFunctions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Pointwise multiplication of tests by an open-kernel character. -/
def characterMultiplyTest (ψ : G →* ℂˣ) (hψ : IsOpen (ψ.ker : Set G)) :
    Module.End ℂ (SchwartzBruhat G) :=
  Distribution.multiplyTest ⟨fun g => ψ g, (isLocallyConstant_of_isOpen_character_ker ψ hψ).comp
    (fun z : ℂˣ => (z : ℂ))⟩

@[simp]
theorem characterMultiplyTest_apply (ψ : G →* ℂˣ) (hψ : IsOpen (ψ.ker : Set G))
    (φ : SchwartzBruhat G) (g : G) :
    characterMultiplyTest ψ hψ φ g = (ψ g : ℂ) * φ g := rfl

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- On a totally disconnected locally compact group, an unramified character has open kernel. -/
theorem IsUnramifiedCharacter.isOpen_ker {ψ : G →* ℂˣ} (hψ : IsUnramifiedCharacter ψ) :
    IsOpen (ψ.ker : Set G) := by
  obtain ⟨K, _, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ ⊤
  exact Subgroup.isOpen_mono (show K.toSubgroup ≤ ψ.ker by exact hψ _ hK) K.isOpen

/-- Pull a distribution back along multiplication of test functions by a smooth character. -/
def characterTwistDistribution (ψ : G →* ℂˣ) (hψ : IsOpen (ψ.ker : Set G)) :
    Module.End ℂ (Distribution G) where
  toFun d := d.comp (characterMultiplyTest ψ hψ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem characterTwistDistribution_apply (ψ : G →* ℂˣ) (hψ : IsOpen (ψ.ker : Set G))
    (d : Distribution G) (f : SchwartzBruhat G) :
    characterTwistDistribution ψ hψ d f = d (characterMultiplyTest ψ hψ f) := rfl

end TestFunctions

section Trace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  [μ.IsMulLeftInvariant] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The twisted distribution of `ρ ⊗ ψ` is the pullback of that of `ρ` by multiplication
of tests by `ψ`. The twisting endomorphism is the same linear map on both carriers. -/
theorem twistedDistribution_twist_eq_comp (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) (ψ : G →* ℂˣ) (hψ : IsOpen (ψ.ker : Set G))
    (h : IsAdmissible (twist ψ ρ)) :
    twistedDistribution μ (twist ψ ρ) h A =
      (twistedDistribution μ ρ hρ A).comp (characterMultiplyTest ψ hψ) := by
  ext φ
  rw [LinearMap.comp_apply, twistedDistribution_apply, twistedDistribution_apply]
  congr 1
  apply Subtype.ext
  ext v
  change Hecke.integratedAction μ (twist ψ ρ) h.1 φ (A v) =
    Hecke.integratedAction μ ρ hρ.1 (characterMultiplyTest ψ hψ φ) (A v)
  rw [Hecke.integratedAction_apply, Hecke.integratedAction_apply]
  congr 1
  ext g
  change φ g • ((ψ g : ℂ) • ρ g (A v)) = ((ψ g : ℂ) * φ g) • ρ g (A v)
  rw [smul_smul, mul_comm (φ g)]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Evaluation of any fixed distribution on the character multiples of one test function
is a finite linear combination of evaluations of the unramified character. -/
theorem exists_regular_characterTwistDistribution (d : Distribution G) (φ : SchwartzBruhat G) :
    ∃ (s : Finset G) (c : G → ℂ), ∀ (ψ : G →* ℂˣ) (hψ : IsUnramifiedCharacter ψ),
      characterTwistDistribution ψ hψ.isOpen_ker d φ = ∑ g ∈ s, c g * (ψ g : ℂ) := by
  classical
  obtain ⟨K, hK, n, g, a, hdis, hφ⟩ := Hecke.RenardTestDecomposition.doubleCosetExpansion G φ
  let F (i : Fin n) := Hecke.TestFunction.doubleCosetIndicator K hK (g i)
  let b (i : Fin n) := a i * d (F i)
  have hg : Function.Injective g := by
    intro i j h
    by_contra hne
    have hmem : g i ∈ Hecke.TestFunction.doubleCosetSet K (g i) :=
      DoubleCoset.mem_doubleCoset_self K.toSubgroup K.toSubgroup (g i)
    exact Set.disjoint_left.mp (hdis hne) hmem (by simpa only [← h] using hmem)
  let c (x : G) := ∑ i, if g i = x then b i else 0
  have hc (i : Fin n) : c (g i) = b i := by
    simp [c, hg.eq_iff]
  refine ⟨Finset.univ.image g, c, fun ψ hψ => ?_⟩
  have hmul (i : Fin n) : characterMultiplyTest ψ hψ.isOpen_ker (F i) = (ψ (g i) : ℂ) • F i := by
    apply Hecke.TestFunction.ext
    intro x
    change (ψ x : ℂ) * F i x = (ψ (g i) : ℂ) * F i x
    by_cases hx : x ∈ Hecke.TestFunction.doubleCosetSet K (g i)
    · obtain ⟨k, hk, k', hk', hx⟩ := (Hecke.TestFunction.mem_doubleCosetSet K (g i) x).mp hx
      have hval : ψ x = ψ (g i) := by
        rw [hx, map_mul, map_mul, hψ K.toSubgroup hK k hk, hψ K.toSubgroup hK k' hk',
          one_mul, mul_one]
      rw [hval]
    · have hzero : F i x = 0 := by
        change Hecke.TestFunction.doubleCosetIndicator K hK (g i) x = 0
        rw [Hecke.TestFunction.doubleCosetIndicator_apply, Set.indicator_of_notMem hx]
      rw [hzero, mul_zero, mul_zero]
  rw [characterTwistDistribution_apply, Finset.sum_image hg.injOn]
  rw [show φ = ∑ i, a i • F i from hφ]
  simp only [map_sum, map_smul, hmul, hc, smul_eq_mul, b]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The twisted trace of a fixed test function is regular on unramified twists of a fixed
admissible representation. -/
theorem exists_regular_twistedDistribution_twist (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (A : Module.End ℂ V) (φ : SchwartzBruhat G) :
    ∃ (s : Finset G) (c : G → ℂ), ∀ (ψ : G →* ℂˣ), IsUnramifiedCharacter ψ →
      ∀ h : IsAdmissible (twist ψ ρ),
        twistedDistribution μ (twist ψ ρ) h A φ = ∑ g ∈ s, c g * (ψ g : ℂ) := by
  obtain ⟨s, c, hc⟩ := exists_regular_characterTwistDistribution (twistedDistribution μ ρ hρ A) φ
  refine ⟨s, c, fun ψ hψ h => ?_⟩
  rw [twistedDistribution_twist_eq_comp μ ρ hρ A ψ hψ.isOpen_ker h]
  exact hc ψ hψ

end Trace

end Langlands.BaseChange
