import Langlands.BaseChange.RegularElementaryIwahoriContraction
import Langlands.Representation.Jacquet.IwahoriContractionTrace
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof

/-!
# Proof of the regular elementary Jacquet trace formula

`regularElementaryJacquetTrace` proves `RegularElementaryJacquetTraceStatement`
(Henniart–Lemaire 2011, I.5.3) through compression by the torus element on the
fixed vectors of the subgroup with diagonal reduction.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.Unramified GeneralLinear.BlockShape HarmonicAnalysis
open Hecke.TestFunction
open GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val torus)
open ClassFieldTheory.Local

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
local notation "G" => GeneralLinear (r + 1) E.Carrier
set_option quotPrecheck false in
local notation "M" => (B).leviSubgroup E.Carrier
set_option quotPrecheck false in
local notation "N" => (B).unipotentSubgroup E.Carrier
local notation "I" => regularElementaryCompactOpenSubgroup E r
set_option quotPrecheck false in
local notation "hMN" => (B).leviSubgroup_le_normalizer_unipotentSubgroup E.Carrier

section Twist

variable (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)

/-- A field automorphism fixing `ϖ` fixes the torus element of any weight. -/
theorem entrywiseAut_torus_of_fixed (ϖ : E.Carrierˣ) (hτ : τ (ϖ : E.Carrier) = ϖ)
    (ν : Fin (r + 1) → ℤ) : entrywiseAut τ (r + 1) (torus ϖ ν) = torus ϖ ν := by
  have hϖ : Units.map τ.toMonoidHom ϖ = ϖ := Units.ext (by simpa using hτ)
  rw [torus, entrywiseAut_diagonalUnits]
  congr 1
  funext i
  rw [map_zpow, hϖ]

/-- The field automorphism preserves the subgroup with diagonal reduction. -/
theorem entrywiseAut_mem_regularElementary_iff (g : G) :
    entrywiseAut τ (r + 1) g ∈ I ↔ g ∈ I := by
  have hp := uniformizerUnit_isUniformizingElement E
  refine ⟨fun hg => ?_, entrywiseAut_mem_regularElementaryCompactOpenSubgroup E τ _ hp g⟩
  have h := entrywiseAut_mem_regularElementaryCompactOpenSubgroup E τ.symm _ hp _ hg
  exact ((entrywiseAut τ (r + 1)).symm_apply_apply g) ▸ h

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V} (A : SigmaIntertwiner τ (r + 1) ρ)

private theorem sigmaIntertwiner_apply (g : G) (w : V) :
    A (ρ g w) = ρ (entrywiseAut τ (r + 1) g) (A w) :=
  Representation.IntertwiningMap.isIntertwining _ _ A.toIntertwiningMap g w

/-- A σ-intertwiner preserves the vectors fixed by the subgroup with diagonal
reduction. -/
theorem sigmaIntertwiner_mem_fixedVectors {w : V} (hw : w ∈ fixedVectors ρ (I).toSubgroup) :
    A w ∈ fixedVectors ρ (I).toSubgroup := by
  intro k
  let k' := (entrywiseAut τ (r + 1)).symm (k : G)
  have hk' : k' ∈ I := (entrywiseAut_mem_regularElementary_iff E τ k').mp (by
    simp [k'])
  have h := sigmaIntertwiner_apply E τ A k' w
  rw [show entrywiseAut τ (r + 1) k' = k from (entrywiseAut τ (r + 1)).apply_symm_apply _,
    show ρ k' w = w from hw ⟨k', hk'⟩] at h
  exact h.symm

/-- A σ-intertwiner commutes with averaging over the subgroup with diagonal reduction. -/
theorem averageMap_sigmaIntertwiner (hρ : IsSmooth ρ) (x : V) :
    Compact.averageMap ρ hρ I (regularElementaryCompactOpenSubgroup_isCompact E) (A x) =
      A (Compact.averageMap ρ hρ I (regularElementaryCompactOpenSubgroup_isCompact E) x) := by
  have hI := regularElementaryCompactOpenSubgroup_isCompact E (r := r)
  have hmem := sigmaIntertwiner_mem_fixedVectors E τ A
    (Compact.averageMap_mem_fixedVectors ρ hρ I hI x)
  rw [← Compact.averageMap_id ρ hρ I hI _ hmem]
  symm
  apply Jacquet.map_averageMap_of_forall_eq ρ hρ I hI
    ((Compact.averageMap ρ hρ I hI).comp A.toLinearMap)
  intro k
  change Compact.averageMap ρ hρ I hI (A (ρ k.val x)) = _
  rw [sigmaIntertwiner_apply E τ A]
  exact Jacquet.averageMap_apply_of_mem ρ hρ I hI
    ((entrywiseAut_mem_regularElementary_iff E τ k.val).mpr k.property) _

end Twist

section JacquetFixed

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (r + 1) E.Carrier) V)

set_option quotPrecheck false in
local notation "J" => Parabolic.leviCoinvariants B (ρ.comp ((B).parabolic E.Carrier).subtype)

private theorem leviEmbedding_mem_of_mem_integralDiagonalLevi {m : (B).Levi E.Carrier}
    (hm : m ∈ integralDiagonalLevi E r) : (B).leviEmbedding E.Carrier m ∈ I := by
  obtain ⟨a, ha, rfl⟩ := (mem_integralDiagonalLevi_iff E m).mp hm
  rw [leviEmbedding_singletonLevi_eq_diagonalUnits]
  apply diagonalUnits_mem_regularElementaryCompactOpenSubgroup
  rw [← leviEmbedding_singletonLevi_eq_diagonalUnits]
  exact hm

/-- The ambient quotient comparison restricts to the integral diagonal fixed vectors. -/
theorem map_borelJacquetFixed :
    (borelJacquetFixed E ρ).map ((B).jacquetModuleEquiv ρ : (B).JacquetModule ρ →ₗ[ℂ] _) =
      fixedVectors (Jacquet.action ρ N M hMN) ((I).toSubgroup.comap (M).subtype) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro m'
    let m := ((B).leviEquiv E.Carrier).symm m'.val
    have hm : m ∈ integralDiagonalLevi E r := by
      change (B).leviEmbedding E.Carrier m ∈ sphericalOpenSubgroup E r
      have he : (B).leviEmbedding E.Carrier m = ((m'.val : M) : G) := by
        change (((B).leviEquiv E.Carrier m : M) : G) = _
        rw [MulEquiv.apply_symm_apply]
      rw [he]
      exact regularElementaryCompactOpenSubgroup_le_spherical E m'.property
    have h := Parabolic.jacquetModuleEquiv_leviCoinvariants E (B) V ρ m x
    rw [show ((B).leviEquiv E.Carrier m) = m'.val from MulEquiv.apply_symm_apply _ _] at h
    change Jacquet.action ρ N M hMN m'.val ((B).jacquetModuleEquiv ρ x) = _
    rw [← h, show J m x = x from hx ⟨m, hm⟩]
    rfl
  · intro hy
    refine ⟨((B).jacquetModuleEquiv ρ).symm y, ?_, ((B).jacquetModuleEquiv ρ).apply_symm_apply y⟩
    intro m
    apply ((B).jacquetModuleEquiv ρ).injective
    change (B).jacquetModuleEquiv ρ (J m.val (((B).jacquetModuleEquiv ρ).symm y)) = _
    rw [Parabolic.jacquetModuleEquiv_leviCoinvariants E (B) V ρ,
      LinearEquiv.apply_symm_apply]
    have hm : ((B).leviEquiv E.Carrier m.val : G) ∈ I :=
      leviEmbedding_mem_of_mem_integralDiagonalLevi E m.property
    exact hy ⟨(B).leviEquiv E.Carrier m.val, hm⟩

/-- The integral diagonal fixed vectors of the Borel Jacquet module are identified
with the fixed vectors of the embedded integral diagonal on the ambient coinvariants. -/
def borelJacquetFixedEquiv :
    borelJacquetFixed E ρ ≃ₗ[ℂ]
      fixedVectors (Jacquet.action ρ N M hMN) ((I).toSubgroup.comap (M).subtype) :=
  ((B).jacquetModuleEquiv ρ).ofSubmodules _ _ (map_borelJacquetFixed E ρ)

@[simp]
theorem borelJacquetFixedEquiv_apply (w : borelJacquetFixed E ρ) :
    (borelJacquetFixedEquiv E ρ w : Jacquet.Coinvariants ρ N) =
      (B).jacquetModuleEquiv ρ (w : (B).JacquetModule ρ) :=
  LinearEquiv.ofSubmodules_apply _ _ _

end JacquetFixed

section Trace

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
/-- The regular elementary trace formula for one field, rank, twist and representation. -/
theorem twistedDistribution_regularElementaryTest_eq_jacquetTrace
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (ϖ : E.Carrierˣ)
    (hϖ : E.canonicalTopologicalData.ord (ϖ : E.Carrier) = 1)
    (hτϖ : τ (ϖ : E.Carrier) = ϖ) (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν)
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (A : SigmaIntertwiner τ (r + 1) ρ) :
    twistedDistribution (sphericalHaar E r) ρ hρ A.toLinearMap
        (regularElementaryTest E τ ϖ hϖ ν hν) =
      (E.canonicalTopologicalData.residueCardinality : ℂ) ^ regularElementaryRho ν *
        LinearMap.trace ℂ (borelJacquetFixed E ρ)
          (borelJacquetDiagonalAction E ρ (fun i => ϖ ^ ν i) ∘ₗ
            borelJacquetFixedTwist E ρ τ A) := by
  have hI := regularElementaryCompactOpenSubgroup_isCompact E (r := r)
  let t := torus ϖ ν
  let : Fintype (I ⧸ conjIntersectionSubgroup I t) :=
    @Fintype.ofFinite _ (finite_quotient_conjIntersectionSubgroup I hI t)
  have hcontr := regularElementary_isIwahoriContraction E ϖ hϖ ν hν
  have hA : ∀ w ∈ fixedVectors ρ (I).toSubgroup, A.toLinearMap w ∈ fixedVectors ρ (I).toSubgroup :=
    fun w hw => sigmaIntertwiner_mem_fixedVectors E τ A hw
  let C := Jacquet.compressedAction ρ hρ.1 I hI t
  let A' := A.toLinearMap.restrict hA
  -- The twist commutes with compression by the torus element.
  have hcomm : Commute C A' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change Compact.averageMap ρ hρ.1 I hI (ρ t (A w)) =
      A (Compact.averageMap ρ hρ.1 I hI (ρ t (w : V)))
    rw [← averageMap_sigmaIntertwiner E τ A hρ.1, sigmaIntertwiner_apply E τ A,
      entrywiseAut_torus_of_fixed E τ ϖ hτϖ ν]
  -- Reduction to the compressed trace on the fixed vectors.
  rw [twistedDistribution_regularElementaryTest E τ ϖ hϖ ν hν (sphericalHaar E r) ρ hρ A]
  change _ * twistedDistribution (sphericalHaar E r) ρ hρ A.toLinearMap
    (doubleCosetIndicator I hI t) = _
  rw [twistedDistribution_doubleCosetIndicator (sphericalHaar E r) ρ hρ I hI t A.toLinearMap hA]
  have hcard : (Fintype.card (I ⧸ conjIntersectionSubgroup I t) : ℂ) =
      (E.canonicalTopologicalData.residueCardinality : ℂ) ^ regularElementaryRho ν := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_quotient_regularElementaryConjIntersection E ϖ hϖ ν hν
  have hscal : ∀ a b c T : ℂ, a * b = 1 → a * (b * c * T) = c * T := by
    intro a b c T h
    rw [← mul_assoc, ← mul_assoc, h, one_mul]
  have hm := card_regularElementaryCosets_mul_measure E (r := r)
  rewrite [hcard, hscal _ _ _ _ hm]
  refine congrArg (fun z => (E.canonicalTopologicalData.residueCardinality : ℂ) ^
    regularElementaryRho ν * z) ?_
  -- The compressed trace is the trace on the Jacquet fixed space.
  let Ψ := borelJacquetFixedEquiv E ρ
  let target := borelJacquetDiagonalAction E ρ (fun i => ϖ ^ ν i) ∘ₗ
    borelJacquetFixedTwist E ρ τ A
  have hZ : ∀ x, Jacquet.fixedJacquetMap ρ N M hMN (I).toSubgroup (C (A' x)) =
      Ψ.conj target (Jacquet.fixedJacquetMap ρ N M hMN (I).toSubgroup x) := by
    intro x
    have hx : (B).jacquetMk ρ (x : V) ∈ borelJacquetFixed E ρ := by
      intro m
      change (B).jacquetMk ρ (ρ ((B).leviEmbedding E.Carrier m.val) x) = (B).jacquetMk ρ x
      rw [show ρ ((B).leviEmbedding E.Carrier m.val) x = x from
        x.property ⟨_, leviEmbedding_mem_of_mem_integralDiagonalLevi E m.property⟩]
    have hsymm : Ψ.symm (Jacquet.fixedJacquetMap ρ N M hMN (I).toSubgroup x) =
        ⟨(B).jacquetMk ρ (x : V), hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [LinearEquiv.conj_apply_apply, hsymm]
    apply Subtype.ext
    rw [Jacquet.fixedJacquetMap_apply, borelJacquetFixedEquiv_apply]
    change Jacquet.mk ρ N (C (A' x) : V) =
      Jacquet.mk ρ N (ρ ((B).leviEmbedding E.Carrier (singletonLevi E.Carrier
        (fun i => ϖ ^ ν i))) (A x))
    rw [Jacquet.mk_compressedAction_of_iwahoriContraction ρ hρ.1 hI hcontr hMN,
      Jacquet.action_mk, leviEmbedding_singletonLevi_eq_diagonalUnits]
    rfl
  rw [LinearMap.trace_mul_comm,
    Jacquet.trace_compressedAction_mul_of_iwahoriContraction ρ hρ.1 hI hcontr hMN (hρ.2 I)
      A' hcomm (Ψ.conj target) hZ, LinearMap.trace_conj']

end Trace

/-- Henniart–Lemaire I.5.3 for the regular elementary test and the unnormalized
Borel Jacquet quotient, with independent field and representation universes. -/
theorem regularElementaryJacquetTrace : RegularElementaryJacquetTraceStatement.{u, v} := by
  intro p _ E r τ ϖ hϖ hτϖ ν hν V _ _ ρ hρ _ A
  exact twistedDistribution_regularElementaryTest_eq_jacquetTrace E τ ϖ hϖ hτϖ ν hν ρ hρ A

end Langlands.BaseChange
