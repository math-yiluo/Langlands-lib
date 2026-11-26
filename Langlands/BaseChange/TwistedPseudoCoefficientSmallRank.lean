import Langlands.BaseChange.TwistedPseudoCoefficientExistenceStatement
import Langlands.Representation.Character.SeparationProof
import Langlands.Representation.Hecke.ActionProjection

/-! # Twisted pseudo-coefficients when the group equals its centre -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uG uV uR

section CentralAction

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

private def centralCharacterModel (hG : ∀ g : G, g ∈ Subgroup.center G)
    (χ : Subgroup.center G →* ℂˣ) : Representation ℂ G ℂ :=
  twist (χ.comp ((MonoidHom.id G).codRestrict (Subgroup.center G) hG))
    (Representation.trivial ℂ G ℂ)

/-- If the entire group is central, an irreducible representation with central character `χ`
is equivalent to the one-dimensional scalar action of `χ`. -/
private def equivCentralCharacterModel (hG : ∀ g : G, g ∈ Subgroup.center G)
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) (χ : Subgroup.center G →* ℂˣ)
    (hχ : HasCentralCharacterRep ρ χ) : (centralCharacterModel hG χ).Equiv ρ := by
  have := hρ
  have := CharacterSeparation.nontrivial_of_isIrreducible hρ
  let v : V := (exists_ne (0 : V)).choose
  have hv : v ≠ 0 := (exists_ne (0 : V)).choose_spec
  let f : (centralCharacterModel hG χ).IntertwiningMap ρ :=
    ⟨LinearMap.toSpanSingleton ℂ V v, by
      intro g
      apply LinearMap.ext
      intro c
      change ((χ ⟨g, hG g⟩ : ℂ) • c) • v = ρ g (c • v)
      have hh := hχ ⟨g, hG g⟩ (c • v)
      change ρ g (c • v) = _ at hh
      rw [hh, smul_smul, smul_eq_mul]⟩
  refine f.ofBijective ⟨smul_left_injective ℂ hv, ?_⟩
  refine (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right (fun hf => hv ?_)
  have h := congrArg (fun T : (centralCharacterModel hG χ).IntertwiningMap ρ => T 1) hf
  simpa [f, LinearMap.toSpanSingleton_apply] using h

end CentralAction

section AbelianCase

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- If every element of `G` is central, the normalized indicator of a compact open subgroup
acting trivially on `ρ`, rescaled by the inverse trace of `A`, is a twisted pseudo-coefficient.
There is no continuity or finite-order hypothesis on the automorphism. -/
theorem exists_isTwistedPseudoCoefficient_of_center_eq_top
    (hG : ∀ g : G, g ∈ Subgroup.center G) (θ : G ≃* G)
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (χ : Subgroup.center G →* ℂˣ) (hχ : HasCentralCharacterRep ρ χ)
    (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    ∃ φ : SchwartzBruhat G, IsTwistedPseudoCoefficient μ θ χ ρ hρ A φ := by
  let e := equivCentralCharacterModel hG ρ hirr χ hχ
  let E := e.toLinearEquiv
  have hE : ∀ c : ℂ, E c = c • E 1 := fun c => by
    rw [← E.map_smul c (1 : ℂ), smul_eq_mul, mul_one]
  obtain ⟨U, hU⟩ := hρ.1 (E 1)
  obtain ⟨K, hKU, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
  let f := Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
  have hact : Hecke.integratedAction μ ρ hρ.1 f = LinearMap.id := by
    ext w : 1
    obtain ⟨c, rfl⟩ := E.surjective w
    apply Hecke.heckeAction_normalizedIndicator_of_fixed μ ρ hρ.1 K hK
    intro k
    change ρ k (E c) = E c
    have hk := hU ⟨k, hKU k.property⟩
    change ρ k (E 1) = E 1 at hk
    rw [hE, map_smul, hk]
  let T : Module.End ℂ ℂ := E.symm.toLinearMap ∘ₗ A.toLinearMap ∘ₗ E.toLinearMap
  let a := T 1
  have ha : a ≠ 0 := by
    change E.symm (A (E 1)) ≠ 0
    exact (E.symm.map_ne_zero_iff).2 (A.toLinearEquiv.map_ne_zero_iff.2
      (E.map_ne_zero_iff.2 one_ne_zero))
  have hT : T = a • LinearMap.id := by
    apply LinearMap.ext
    intro c
    change T c = a • c
    calc
      T c = T (c • (1 : ℂ)) := by simp
      _ = c • a := T.map_smul _ _
      _ = a • c := mul_comm _ _
  let : FiniteDimensional ℂ V := E.finiteDimensional
  have htrace : twistedDistribution μ ρ hρ A.toLinearMap f = a := by
    rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_ambient]
    change LinearMap.trace ℂ V (Hecke.integratedAction μ ρ hρ.1 f ∘ₗ A.toLinearMap) = a
    rw [hact, LinearMap.id_comp]
    calc
      _ = LinearMap.trace ℂ ℂ T := by
        change LinearMap.trace ℂ V A.toLinearMap = LinearMap.trace ℂ ℂ (E.symm.conj A.toLinearMap)
        exact (LinearMap.trace_conj' _ _).symm
      _ = a := by rw [hT, map_smul, LinearMap.trace_id, Module.finrank_self]; simp
  refine ⟨a⁻¹ • f, hχ, ?_, ?_⟩
  · rw [map_smul, htrace, smul_eq_mul, inv_mul_cancel₀ ha]
  · intro W _ _ ρ' _ hirr' _ hχ' hne _
    exact (hne.false ((equivCentralCharacterModel hG ρ' hirr' χ hχ').symm.trans e)).elim

end AbelianCase

/-- In rank zero or one, every element of the general linear group is central. -/
theorem generalLinear_mem_center_of_rank_le_one {R : Type uR} [CommRing R]
    {n : ℕ} (hn : n ≤ 1) (g : GeneralLinear n R) : g ∈ Subgroup.center (GeneralLinear n R) := by
  rw [Subgroup.mem_center_iff]
  intro h
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · ext i
    exact Fin.elim0 i
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]

/-- Twisted pseudo-coefficient existence for the ranks selected by `ranks`. -/
def TwistedPseudoCoefficientExistenceInRanks.{u, v, z} (ranks : ℕ → Prop) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → ranks n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      IsSigmaDiscreteSeries σ n τ →
      ∀ χ : Subgroup.center (GeneralLinear n E) →* ℂˣ, HasCentralCharacterRep τ χ →
        ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
          ∃ φ : SchwartzBruhat (GeneralLinear n E),
            IsTwistedPseudoCoefficient μ (entrywiseAut σ n) χ τ hτ A φ

/-- The twisted pseudo-coefficient existence assertion holds in ranks zero and one. -/
theorem twistedPseudoCoefficientExistenceInSmallRanks.{u, v, z} :
    TwistedPseudoCoefficientExistenceInRanks.{u, v, z} (fun n => n ≤ 1) := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro W _ _ τ hτ hdisc χ hχ A μ _
  exact exists_isTwistedPseudoCoefficient_of_center_eq_top μ
    (generalLinear_mem_center_of_rank_le_one hn) (entrywiseAut σ n) τ hτ hdisc.2.1 χ hχ A

/-- The full existence assertion follows from its restriction to ranks at least two. -/
def TwistedPseudoCoefficientRankReductionStatement.{u, v, z} : Prop :=
  TwistedPseudoCoefficientExistenceInRanks.{u, v, z} (fun n => 2 ≤ n) →
    TwistedPseudoCoefficientExistenceStatement.{u, v, z}

/-- Assemble the low-rank proof with existence in ranks at least two. -/
theorem twistedPseudoCoefficientExistence_of_higherRanks.{u, v, z} :
    TwistedPseudoCoefficientRankReductionStatement.{u, v, z} := by
  intro h F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  by_cases hn : n ≤ 1
  · exact twistedPseudoCoefficientExistenceInSmallRanks.{u, v, z} F E σ l n hE hn
  · exact h F E σ l n hE (by omega)

end Langlands.BaseChange
