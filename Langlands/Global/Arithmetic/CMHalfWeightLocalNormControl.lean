import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.AdelicFunctoriality.FinitePlaceDegreeTransfer
import Langlands.ClassField.Global.IdeleGaloisDescentProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Finite local norm control in CM extensions -/

noncomputable section

open Algebra NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.ClassField.Global Langlands.Global.AdelicFunctoriality

namespace Langlands.Global.CMHalfWeight

universe u v

section Local

variable {F : Type u} {E : Type v} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] (p : FinitePlace F) (q : FinitePlace E)
  [q.asIdeal.LiesOver p.asIdeal]

/-- The completion embedding on the actual unit groups. -/
def completionUnitInclusion : (FiniteCompletion F p)ˣ →ₜ* (FiniteCompletion E q)ˣ where
  toMonoidHom := Units.map (FiniteExtension.completionMap p q).toMonoidHom
  continuous_toFun := (FiniteExtension.continuous_completionMap p q).units_map _

/-- The completed field embedding preserves the given topology as a subspace. -/
theorem isEmbedding_completionMap : IsEmbedding (FiniteExtension.completionMap p q) := by
  let : NontriviallyNormedField (FiniteCompletion F p) :=
    Valued.toNontriviallyNormedField (FiniteCompletion F p) (WithZero (Multiplicative ℤ))
  exact (LinearMap.isClosedEmbedding_of_injective
    (f := Algebra.linearMap (FiniteCompletion F p) (FiniteCompletion E q))
    (LinearMap.ker_eq_bot.mpr (FiniteExtension.completionMap p q).injective)).isEmbedding

/-- The same subspace property holds for the groups of nonzero elements. -/
theorem isEmbedding_completionUnitInclusion :
    IsEmbedding (completionUnitInclusion p q) := by
  apply IsEmbedding.of_comp (completionUnitInclusion p q).continuous Units.continuous_val
  exact (isEmbedding_completionMap p q).comp Units.isEmbedding_val₀

/-- A small open subgroup in the extension completion meets the embedded base
only in local norms. -/
theorem exists_openSubgroup_norm_control :
    ∃ W : OpenSubgroup (FiniteCompletion E q)ˣ,
      ∀ a : (FiniteCompletion F p)ˣ, completionUnitInclusion p q a ∈ W →
        a ∈ (Units.map (FiniteExtension.localNorm p q)).range := by
  classical
  have hN := range_finiteLocalNorm_mem_nhds p q
  rw [(isEmbedding_completionUnitInclusion p q).isInducing.nhds_eq_comap 1] at hN
  simp only [map_one] at hN
  obtain ⟨U, hU, hpre⟩ := hN
  let : ValuativeRel (FiniteCompletion E q) :=
    (CompletionPadic.topologicalData q).valuativeRel
  let : IsNonarchimedeanLocalField (FiniteCompletion E q) :=
    (CompletionPadic.topologicalData q).localField
  let : TotallyDisconnectedSpace (FiniteCompletion E q) := inferInstance
  let : TotallyDisconnectedSpace (FiniteCompletion E q)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  obtain ⟨W, _, hW⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
  exact ⟨W, fun a ha => hpre (hW ha)⟩

/-- The unit-valued finite coordinate of an included idele. -/
theorem ideleCoordinate_ideleInclusion (r : Ideles F) :
    ideleCoordinate q (ideleInclusion (L := E) r) =
      completionUnitInclusion p q (ideleCoordinate p r) := by
  apply Units.ext
  exact IdeleGaloisDescentProof.finiteAdeleInclusion_apply_of_liesOver r.val.2 p q

end Local

section Quadratic

variable {F : Type u} {E : Type v} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsQuadraticExtension F E]

/-- In a quadratic extension, a completion of degree two is the only completion
above its base place. -/
theorem subsingleton_finitePlacesAbove_of_degree_two (p : FinitePlace F)
    (q : FinitePlacesAbove E p)
    (hq : Module.finrank (FiniteCompletion F p) (FiniteCompletion E q.1) = 2) :
    Subsingleton (FinitePlacesAbove E p) := by
  classical
  have hsum := finiteLocalDegree_sum (L := E) p
  rw [IsQuadraticExtension.finrank_eq_two] at hsum
  have hpos (r : FinitePlacesAbove E p) :
      0 < Module.finrank (FiniteCompletion F p) (FiniteCompletion E r.1) :=
    Module.finrank_pos
  have hall : ∀ r : FinitePlacesAbove E p, r = q := by
    intro r
    by_contra hr
    have hle := Finset.sum_le_sum_of_subset (f := fun r : FinitePlacesAbove E p =>
      Module.finrank (FiniteCompletion F p) (FiniteCompletion E r.1))
      (Finset.subset_univ ({q, r} : Finset (FinitePlacesAbove E p)))
    rw [Finset.sum_pair (Ne.symm hr), hsum, hq] at hle
    have := hpos r
    omega
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

/-- The finite coordinate of an idele norm is a norm from any selected completion
above that place, in a quadratic extension. -/
theorem ideleCoordinate_ideleNorm_mem_localNorm (p : FinitePlace F)
    (q : FinitePlacesAbove E p) (y : Ideles E) :
    ideleCoordinate p (ideleNorm (K := F) y) ∈
      (Units.map (FiniteExtension.localNorm p q.1)).range := by
  classical
  have hd := localDegree_dvd p q.1
  have hFE : Module.finrank F E = 2 := IsQuadraticExtension.finrank_eq_two F E
  rw [hFE] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd | hd
  · refine ⟨completionUnitInclusion p q.1
      (ideleCoordinate p (ideleNorm (K := F) y)), ?_⟩
    apply Units.ext
    change FiniteExtension.localNorm p q.1
      (FiniteExtension.completionMap p q.1 _) = _
    rw [FiniteExtension.localNorm_algebraMap, hd, pow_one]
  · let : Subsingleton (FinitePlacesAbove E p) :=
      subsingleton_finitePlacesAbove_of_degree_two p q hd
    refine ⟨ideleCoordinate q.1 y, ?_⟩
    apply Units.ext
    change FiniteExtension.localNorm p q.1 (y.val.2 q.1) =
      finiteAdeleNorm (K := F) y.val.2 p
    rw [finiteAdeleNorm_apply, Fintype.prod_subsingleton _ q]

end Quadratic

section CM

variable {K : Type u} [Field K] [NumberField K] [IsCMField K]

local notation "F" => maximalRealSubfield K

/-- Each place of the real subfield has a place above it outside a set disjoint
from its CM conjugate. -/
theorem exists_placeAbove_not_mem (S : Finset (FinitePlace K))
    (hS : Disjoint S (S.map
      (finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv).toEmbedding))
    (p : FinitePlace F) :
    ∃ q : FinitePlacesAbove K p, q.1 ∉ S := by
  classical
  let q := placeAbove K p
  by_cases hq : q.1 ∈ S
  · let r := finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv q.1
    have hr := IdeleGaloisDescentProof.liesOver_finitePlaceEquiv
      (IsCMField.complexConj K) p q.1
    refine ⟨⟨r, hr⟩, ?_⟩
    intro hrS
    exact Finset.disjoint_left.mp hS hrS (Finset.mem_map.mpr ⟨q.1, hq, rfl⟩)
  · exact ⟨q, hq⟩

/-- An open integral-idele subgroup containing infinity controls every finite
local norm of a base idele modulo an idele supported in `S`. -/
theorem exists_open_integral_subgroup_localNorm_control
    (S : Finset (FinitePlace K))
    (hS : Disjoint S (S.map
      (finitePlaceEquiv (IsCMField.complexConj K).toRingEquiv).toEmbedding)) :
    ∃ H : OpenSubgroup (Ideles K),
      H.toSubgroup ≤ integralIdeles K ∧
      (∀ x : (InfiniteAdeles K)ˣ, infiniteIdelesInclusion K x ∈ H) ∧
      ∀ (r : Ideles F) (s : Ideles K),
        (∀ w ∉ S, ideleCoordinate w s = 1) →
        ideleInclusion r * s ∈ H →
        ∀ p : FinitePlace F, ∃ q : FinitePlacesAbove K p,
          ideleCoordinate p r ∈ (Units.map (FiniteExtension.localNorm p q.1)).range := by
  classical
  choose q hq using exists_placeAbove_not_mem S hS
  choose W hW using fun p => exists_openSubgroup_norm_control p (q p).1
  let A : Finset (FinitePlace F) :=
    (Filter.eventually_cofinite.1 (eventually_ramificationIdx_eq_one F K)).toFinset
  let T (p : FinitePlace F) : OpenSubgroup (Ideles K) :=
    (W p).comap (ideleCoordinate (q p).1)
      ((continuous_finiteProjection K (q p).1).units_map _)
  let H : OpenSubgroup (Ideles K) :=
    ⟨integralIdeles K, CMUnramifiedInfinity.isOpen_integralIdeles⟩ ⊓ A.inf T
  have hmem (x : Ideles K) : x ∈ A.inf T ↔ ∀ p ∈ A, x ∈ T p := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert p B hp ih => simp only [Finset.inf_insert, OpenSubgroup.mem_inf, ih,
        Finset.mem_insert, forall_eq_or_imp]
  refine ⟨H, fun _ hx => hx.1, ?_, ?_⟩
  · intro x
    constructor
    · exact CMUnramifiedInfinity.infiniteIdelesInclusion_mem x
    · apply (hmem _).2
      intro p _
      change ideleCoordinate (q p).1 (infiniteIdelesInclusion K x) ∈ W p
      have hi : ideleCoordinate (q p).1 (infiniteIdelesInclusion K x) = 1 :=
        Units.ext rfl
      rw [hi]
      exact (W p).one_mem
  · intro r s hs hx p
    refine ⟨q p, ?_⟩
    have he : ideleCoordinate (q p).1 (ideleInclusion r * s) =
        completionUnitInclusion p (q p).1 (ideleCoordinate p r) := by
      rw [map_mul, show ideleCoordinate (q p).1 s = 1 from hs _ (hq p), mul_one,
        ideleCoordinate_ideleInclusion p (q p).1 r]
    by_cases hp : p ∈ A
    · apply hW p
      rw [← he]
      exact (hmem _).1 hx.2 p hp
    · have hunram : (q p).1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
        have hp' : ∀ t : FinitePlace K, t.asIdeal.LiesOver p.asIdeal →
            t.asIdeal.ramificationIdx (𝓞 F) = 1 := by
          simpa only [A, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hp
        exact hp' (q p).1 (q p).2
      have hu : Valued.v (ideleCoordinate p r : FiniteCompletion F p) = 1 := by
        have hv := hx.1 (q p).1
        change Valued.v (ideleCoordinate (q p).1 (ideleInclusion r * s) :
          FiniteCompletion K (q p).1) = 1 at hv
        rw [he] at hv
        change Valued.v (FiniteExtension.completionMap p (q p).1
          (ideleCoordinate p r : FiniteCompletion F p)) = 1 at hv
        rwa [FiniteExtension.valuation_completionMap, hunram, pow_one] at hv
      obtain ⟨b, _, hb⟩ := FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one
        p (q p).1 hunram (ideleCoordinate p r) hu
      exact ⟨b, Units.ext hb⟩

end CM

end Langlands.Global.CMHalfWeight
