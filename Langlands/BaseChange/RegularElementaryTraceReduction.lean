import Langlands.BaseChange.RegularElementaryCosetDecomposition
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Character.ModularContragredientProof

/-! # The fixed level and double-coset trace of a regular elementary test -/

noncomputable section

namespace Langlands.BaseChange

open Conductor HarmonicAnalysis Hecke.TestFunction MeasureTheory Unramified
open GeneralLinear.Iwasawa (torus)

universe u v w

section Trace

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)

/-- Twisted conjugation preserves the distribution trace when the right
translation in the conjugation is unimodular. -/
theorem twistedDistribution_twistedTranslate (α : MulAut G)
    (A : ρ.Equiv (ρ.comp α.toMonoidHom)) (g : G)
    (hmod : Distribution.renardModular (α g) = 1) (f : SchwartzBruhat G) :
    twistedDistribution μ ρ hρ A.toLinearMap
      (leftTranslate g (rightTranslate (α g) f)) =
      twistedDistribution μ ρ hρ A.toLinearMap f := by
  let T : finiteRankEnd V :=
    ⟨(Character.finiteRankIntegratedAction μ ρ hρ f).val.comp A.toLinearMap,
      (Character.finiteRankIntegratedAction μ ρ hρ f).property.comp_right _⟩
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  rw [twistedDistribution_apply, twistedDistribution_apply]
  change _ = FiniteRankEnd.trace T
  rw [← FiniteRankEnd.trace_conjugate e T]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  ext x
  change Hecke.integratedAction μ ρ hρ.1
      (leftTranslate g (rightTranslate (α g) f)) (A x) =
    ρ g (Hecke.integratedAction μ ρ hρ.1 f (A (ρ g⁻¹ x)))
  have hinter := LinearMap.congr_fun (A.isIntertwining' g⁻¹) x
  change A (ρ g⁻¹ x) = ρ (α g⁻¹) (A x) at hinter
  rw [map_inv α] at hinter
  have hright := Character.integratedAction_right_input_modular μ ρ hρ.1
    (α g)⁻¹ f (A x)
  rw [inv_inv, hmod] at hright
  simp only [NNReal.coe_one, Complex.ofReal_one, one_smul] at hright
  rw [Hecke.integratedAction_leftTranslate, hinter, hright]

end Trace

section Padic

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (E : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n E.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n

private local instance {p : ℕ} [Fact p.Prime] (E : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n E.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{u} p) {r : ℕ}
  (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)
  (π : E.Carrierˣ) (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
  (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν)

local notation "G" => GeneralLinear (r + 1) E.Carrier
local notation "K" => sphericalOpenSubgroup E r
local notation "I" => regularElementaryCompactOpenSubgroup E r
local notation "J" => principalLevelSubgroup E.Carrier r 1
local notation "B" => GeneralLinear.BlockShape.singletons (r + 1)
local notation "α" => entrywiseAut τ (r + 1)

private theorem entrywiseAut_mem_spherical_for_elementary {g : G} (hg : g ∈ K) : α g ∈ K := by
  have h := entrywiseAut_mem_principalLevel_iff E τ E.canonicalTopologicalData.uniformizerUnit
    (uniformizerUnit_isUniformizingElement E) 0 g
  rw [principalLevelSubgroup_zero] at h
  exact h.mpr hg

/-- All strict weights give bi-invariance by the same first congruence subgroup. -/
theorem regularElementaryTest_mem_firstCongruence_biInvariant :
    regularElementaryTest E τ π hπ ν hν ∈ biInvariant J J := by
  rw [regularElementaryTest_eq_sum_cosets]
  apply Submodule.sum_mem
  intro q _
  let k : K := q.out
  let d := regularElementaryDoubleCosetTest E π ν
  have hI : J ≤ (I).toSubgroup := (B).principalLevel_le_leviCongruenceSubgroup E.Carrier
  have hN : (K).toSubgroup ≤ Subgroup.normalizer (J : Set G) := by
    have h := GeneralLinear.BlockShape.integral_le_normalizer_principalLevel
      (r := r) E.Carrier 1
    rw [principalLevelSubgroup_zero] at h
    exact h
  have hd : d ∈ biInvariant (I).toSubgroup (I).toSubgroup :=
    doubleCosetIndicator_mem I (regularElementaryCompactOpenSubgroup_isCompact E) (torus π ν)
  have hσk : α (k : G) ∈ K := entrywiseAut_mem_spherical_for_elementary E τ k.property
  constructor
  · intro j x
    let j' : I := ⟨(k : G)⁻¹ * (j : G) * k,
      hI ((Subgroup.mem_normalizer_iff''.mp (hN k.property) j).mp j.property)⟩
    change d ((k : G)⁻¹ * ((j : G) * x) * α k) = d ((k : G)⁻¹ * x * α k)
    calc
      _ = d ((j' : G) * ((k : G)⁻¹ * x * α k)) := congrArg (fun z : G => d z) (by
        change _ = ((k : G)⁻¹ * (j : G) * k) * ((k : G)⁻¹ * x * α k)
        group)
      _ = _ := hd.1 j' _
  · intro j x
    let j' : I := ⟨(α (k : G))⁻¹ * (j : G) * α k,
      hI ((Subgroup.mem_normalizer_iff''.mp (hN hσk) j).mp j.property)⟩
    change d ((k : G)⁻¹ * (x * (j : G)) * α k) = d ((k : G)⁻¹ * x * α k)
    calc
      _ = d (((k : G)⁻¹ * x * α k) * (j' : G)) := congrArg (fun z : G => d z) (by
        change _ = ((k : G)⁻¹ * x * α k) * ((α (k : G))⁻¹ * (j : G) * α k)
        group)
      _ = _ := hd.2 j' _

/-- On a regular elementary test the trace is the index of the diagonal-reduction
subgroup in the spherical subgroup times the trace on the smaller double coset. -/
theorem twistedDistribution_regularElementaryTest (μ : Measure G) [μ.IsHaarMeasure]
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : IsAdmissible ρ) (A : SigmaIntertwiner τ (r + 1) ρ) :
    twistedDistribution μ ρ hρ A.toLinearMap (regularElementaryTest E τ π hπ ν hν) =
      (Fintype.card (RegularElementaryCosets E r) : ℂ) *
        twistedDistribution μ ρ hρ A.toLinearMap (regularElementaryDoubleCosetTest E π ν) := by
  rw [regularElementaryTest_eq_sum_cosets, map_sum]
  calc
    _ = ∑ _ : RegularElementaryCosets E r,
        twistedDistribution μ ρ hρ A.toLinearMap (regularElementaryDoubleCosetTest E π ν) := by
      apply Finset.sum_congr rfl
      intro q _
      let k : K := q.out
      have hk : α (k : G) ∈ K := entrywiseAut_mem_spherical_for_elementary E τ k.property
      have hmod : Distribution.renardModular (α (k : G)) = 1 :=
        (Distribution.RenardModular.regularity G).2.2.2 (K).toSubgroup
          (sphericalOpenSubgroup_isCompact E r) _ hk
      exact twistedDistribution_twistedTranslate μ ρ hρ α A (k : G) hmod _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Uniform congruence level and the double-coset reduction of the regular
    elementary trace, over any p-adic field and with any Haar normalization. -/
def RegularElementaryTraceReductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) (r : ℕ)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ)
    (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν),
    let J₁ := principalLevelSubgroup E.Carrier r 1
    regularElementaryTest E τ π hπ ν hν ∈ biInvariant J₁ J₁ ∧
    ∀ (μ : Measure (GeneralLinear (r + 1) E.Carrier)) [μ.IsHaarMeasure]
      (V : Type v) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V) (hρ : IsAdmissible ρ)
      (A : SigmaIntertwiner τ (r + 1) ρ),
      twistedDistribution μ ρ hρ A.toLinearMap (regularElementaryTest E τ π hπ ν hν) =
        (Fintype.card (RegularElementaryCosets E r) : ℂ) *
          twistedDistribution μ ρ hρ A.toLinearMap (regularElementaryDoubleCosetTest E π ν)

theorem regularElementaryTraceReduction : RegularElementaryTraceReductionStatement.{u, v} := by
  intro p _ E r τ π hπ ν hν
  exact ⟨regularElementaryTest_mem_firstCongruence_biInvariant E τ π hπ ν hν,
    fun μ _ _ _ _ ρ hρ A => twistedDistribution_regularElementaryTest E τ π hπ ν hν μ ρ hρ A⟩

/-- Both tests of the regular base-change pair are bi-invariant by the first
principal congruence subgroups, independently of the diagonal weight. -/
theorem regularElementaryBaseChangeTests_mem_firstCongruence_biInvariant
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{w} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) (hσ : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    let tests := regularElementaryBaseChangeTests F E σ l hσ he ν hν
    let JE := principalLevelSubgroup E.Carrier r 1
    let JF := principalLevelSubgroup F.Carrier r 1
    tests.1 ∈ biInvariant JE JE ∧ tests.2 ∈ biInvariant JF JF := by
  dsimp only [regularElementaryBaseChangeTests]
  exact ⟨regularElementaryTest_mem_firstCongruence_biInvariant E _ _ _ _ _,
    regularElementaryTest_mem_firstCongruence_biInvariant F _ _ _ _ _⟩

end Padic

end Langlands.BaseChange
