import Langlands.BaseChange.RegularElementaryDoubleCoset
import Langlands.BaseChange.TwistedJacquet
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof

/-!
# The regular elementary Jacquet trace formula

Henniart–Lemaire (2011), I.5.3, Proposition, printed pp. 31–32, specialized
to strict weights and the unnormalized Borel Jacquet action.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.Unramified GeneralLinear.BlockShape
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val torus)
open ClassFieldTheory.Local
open scoped BigOperators

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{u} p) {r : ℕ}

private local instance (n : ℕ) : LocallyCompactSpace (GeneralLinear n E.Carrier) :=
  E.canonicalGeneralLinearLocallyCompactSpace n

private local instance (n : ℕ) : TotallyDisconnectedSpace (GeneralLinear n E.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n

local notation "B" => singletons (r + 1)
local notation "D" => E.canonicalTopologicalData

/-- The integral diagonal subgroup in the singleton-block product Levi. -/
def integralDiagonalLevi (r : ℕ) : OpenSubgroup ((singletons (r + 1)).Levi E.Carrier) :=
  (sphericalOpenSubgroup E r).comap
    ((singletons (r + 1)).leviEmbedding E.Carrier)
    ((D).blockLeviEmbedding (singletons (r + 1))).continuous

/-- The singleton Levi coordinate embedding is the ambient diagonal matrix. -/
theorem leviEmbedding_singletonLevi_eq_diagonalUnits (a : Fin (r + 1) → E.Carrierˣ) :
    (B).leviEmbedding E.Carrier (singletonLevi E.Carrier a) = diagonalUnits a := by
  apply Units.ext
  rw [leviEmbedding_singletonLevi_val, diagonalUnits_val]

theorem mem_integralDiagonalLevi_iff (m : (B).Levi E.Carrier) :
    m ∈ integralDiagonalLevi E r ↔
      ∃ a : Fin (r + 1) → E.Carrierˣ, (∀ i, a i ∈ (D).unitSubgroup) ∧
        m = singletonLevi E.Carrier a := by
  change (B).leviEmbedding E.Carrier m ∈ sphericalOpenSubgroup E r ↔ _
  constructor
  · intro hm
    obtain ⟨a, ha⟩ := (mem_singletonLevi_iff_diagonalUnits E _).mp ⟨m, rfl⟩
    refine ⟨a, ?_, (B).leviEmbedding_injective E.Carrier
      (ha.trans (leviEmbedding_singletonLevi_eq_diagonalUnits E a).symm)⟩
    rw [ha, diagonalUnits_mem_sphericalOpenSubgroup_iff E] at hm
    exact fun i => (mem_unitSubgroup_iff_ord_eq_zero E D (a i)).mpr (hm i)
  · rintro ⟨a, ha, rfl⟩
    rw [leviEmbedding_singletonLevi_eq_diagonalUnits, diagonalUnits_mem_sphericalOpenSubgroup_iff E]
    exact fun i => (mem_unitSubgroup_iff_ord_eq_zero E D (a i)).mp (ha i)

private theorem leviAut_mem_integralDiagonalLevi (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)
    {m : (B).Levi E.Carrier} (hm : m ∈ integralDiagonalLevi E r) :
    leviAut τ B m ∈ integralDiagonalLevi E r := by
  obtain ⟨a, ha, rfl⟩ := (mem_integralDiagonalLevi_iff E m).mp hm
  change (B).leviEmbedding E.Carrier (leviAut τ B (singletonLevi E.Carrier a)) ∈
    sphericalOpenSubgroup E r
  rw [← entrywiseAut_leviEmbedding, leviEmbedding_singletonLevi_eq_diagonalUnits,
    entrywiseAut_diagonalUnits, diagonalUnits_mem_sphericalOpenSubgroup_iff E]
  intro i
  change (D).ord (τ (a i : E.Carrier)) = 0
  rw [LocalClassField.UniverseZero.ord_eq_of_algEquiv τ D D]
  exact (mem_unitSubgroup_iff_ord_eq_zero E D (a i)).mp (ha i)

section JacquetFixed

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V)

set_option quotPrecheck false in
local notation "J" => Parabolic.leviCoinvariants B (ρ.comp ((B).parabolic E.Carrier).subtype)

/-- The integral diagonal fixed submodule of the unnormalized Borel Jacquet quotient. -/
abbrev borelJacquetFixed : Submodule ℂ ((B).JacquetModule ρ) :=
  fixedVectors J (integralDiagonalLevi E r).toSubgroup

theorem mem_borelJacquetFixed_iff (w : (B).JacquetModule ρ) :
    w ∈ borelJacquetFixed E ρ ↔
      ∀ a : Fin (r + 1) → E.Carrierˣ, (∀ i, a i ∈ (D).unitSubgroup) →
        J (singletonLevi E.Carrier a) w = w := by
  constructor
  · intro hw a ha
    exact hw ⟨_, (mem_integralDiagonalLevi_iff E _).mpr ⟨a, ha, rfl⟩⟩
  · intro hw m
    obtain ⟨a, ha, he⟩ := (mem_integralDiagonalLevi_iff E _).mp m.property
    change J (m : (B).Levi E.Carrier) w = w
    rw [he]
    exact hw a ha

theorem finiteDimensional_borelJacquetFixed (hρ : IsAdmissible ρ) :
    FiniteDimensional ℂ (borelJacquetFixed E ρ) :=
  (Parabolic.isAdmissible_leviCoinvariants E D B V ρ hρ).2 (integralDiagonalLevi E r)

/-- The unnormalized action of a diagonal element on the integral fixed vectors. -/
def borelJacquetDiagonalAction (a : Fin (r + 1) → E.Carrierˣ) :
    Module.End ℂ (borelJacquetFixed E ρ) := by
  refine (J (singletonLevi E.Carrier a)).restrict ?_
  intro w hw m
  obtain ⟨b, _, hb⟩ := (mem_integralDiagonalLevi_iff E _).mp m.property
  have hcomm : (m : (B).Levi E.Carrier) * singletonLevi E.Carrier a =
      singletonLevi E.Carrier a * (m : (B).Levi E.Carrier) := by
    rw [hb, ← map_mul, ← map_mul, mul_comm]
  have hfixed : J (m : (B).Levi E.Carrier) w = w := hw m
  change J (m : (B).Levi E.Carrier) (J (singletonLevi E.Carrier a) w) =
    J (singletonLevi E.Carrier a) w
  rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hfixed]

/-- The descended intertwiner `[w] ↦ [A w]` on the integral fixed vectors. -/
def borelJacquetFixedTwist (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)
    (A : SigmaIntertwiner τ (r + 1) ρ) : Module.End ℂ (borelJacquetFixed E ρ) := by
  let Aₙ := jacquetSigmaIntertwiner τ B A
  refine Aₙ.toLinearMap.restrict ?_
  intro w hw m
  let m' := (leviAut τ B).symm (m : (B).Levi E.Carrier)
  have hm' : m' ∈ integralDiagonalLevi E r :=
    leviAut_mem_integralDiagonalLevi E τ.symm m.property
  have hfixed : J m' w = w := hw ⟨m', hm'⟩
  have h := LinearMap.congr_fun (Aₙ.isIntertwining' m') w
  change Aₙ (J m' w) = J (leviAut τ B m') (Aₙ w) at h
  change J (m : (B).Levi E.Carrier) (Aₙ w) = Aₙ w
  simpa only [show leviAut τ B m' = (m : (B).Levi E.Carrier)
    from (leviAut τ B).apply_symm_apply m, hfixed] using h.symm

end JacquetFixed

/-- The sum of the positive-root pairings of a diagonal weight. -/
def regularElementaryRho (ν : Fin (r + 1) → ℤ) : ℤ :=
  ∑ i : Fin (r + 1), ∑ j ∈ Finset.univ.filter (fun j => i < j), (ν i - ν j)

/-- Henniart–Lemaire I.5.3 for the regular elementary test and the unnormalized
Borel Jacquet quotient. -/
def RegularElementaryJacquetTraceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) (r : ℕ)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (ϖ : E.Carrierˣ)
    (hϖ : E.canonicalTopologicalData.ord (ϖ : E.Carrier) = 1),
    τ (ϖ : E.Carrier) = (ϖ : E.Carrier) →
    ∀ (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν)
      (V : Type v) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V) (hρ : IsAdmissible ρ),
      ρ.IsIrreducible →
      ∀ A : SigmaIntertwiner τ (r + 1) ρ,
        twistedDistribution (sphericalHaar E r) ρ hρ A.toLinearMap
          (regularElementaryTest E τ ϖ hϖ ν hν) =
        (E.canonicalTopologicalData.residueCardinality : ℂ) ^ regularElementaryRho ν *
          LinearMap.trace ℂ (borelJacquetFixed E ρ)
            (borelJacquetDiagonalAction E ρ (fun i => ϖ ^ ν i) ∘ₗ
              borelJacquetFixedTwist E ρ τ A)

section IdentityTwist

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V)

private def identitySigmaIntertwiner : SigmaIntertwiner
    (1 : E.Carrier ≃ₐ[Padic p] E.Carrier) (r + 1) ρ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
    ext w
    simp [entrywiseAut_one_apply]

/-- The identity twist specializes the formula to the ordinary character distribution. -/
theorem regularElementaryJacquetTrace_of_identity
    (hTrace : RegularElementaryJacquetTraceStatement.{u, v}) (hρ : IsAdmissible ρ)
    (hIrr : ρ.IsIrreducible) (ϖ : E.Carrierˣ)
    (hϖ : (D).ord (ϖ : E.Carrier) = 1) (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν) :
    Character.distribution (sphericalHaar E r) ρ hρ
      (regularElementaryTest E 1 ϖ hϖ ν hν) =
    ((D).residueCardinality : ℂ) ^ regularElementaryRho ν *
      LinearMap.trace ℂ (borelJacquetFixed E ρ)
        (borelJacquetDiagonalAction E ρ (fun i => ϖ ^ ν i)) := by
  have h := hTrace p E r 1 ϖ hϖ rfl ν hν V ρ hρ hIrr (identitySigmaIntertwiner E ρ)
  have hId : borelJacquetFixedTwist E ρ 1 (identitySigmaIntertwiner E ρ) = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change jacquetSigmaIntertwiner (1 : E.Carrier ≃ₐ[Padic p] E.Carrier) B
      (identitySigmaIntertwiner E ρ) (w : (B).JacquetModule ρ) = (w : (B).JacquetModule ρ)
    obtain ⟨x, hx⟩ := (B).jacquetMk_surjective ρ (w : (B).JacquetModule ρ)
    rw [← hx, jacquetSigmaIntertwiner_mk]
    rfl
  simpa only [show (identitySigmaIntertwiner E ρ).toLinearMap = 1 from rfl,
    twistedDistribution_one, hId, LinearMap.comp_id] using h

end IdentityTwist

end Langlands.BaseChange
