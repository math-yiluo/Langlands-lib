import Langlands.BaseChange.CyclicNormPullbackArtinReduction
import Langlands.BaseChange.CyclicArtinTowerInvariants
import Langlands.BaseChange.CyclicArtinCharacterNormalization
import Langlands.BaseChange.CyclicArtinCharacterStage
import Langlands.BaseChange.FiniteArtinConductorForExtension

/-! # The finite Artin presentation of a norm pullback over p-adic fields -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField LocalClassField.FiniteArtinSystemExistence
open scoped IsMulCommutative

universe u

section GroupTransport

open Ramification

variable {p : ℕ} [Fact p.Prime] (F E M : PadicField.{u} p)
  [Algebra F.Carrier E.Carrier] [Algebra F.Carrier M.Carrier] [Algebra E.Carrier M.Carrier]
  [IsScalarTower F.Carrier E.Carrier M.Carrier]
  [IsScalarTower (Padic p) F.Carrier M.Carrier] [IsScalarTower (Padic p) E.Carrier M.Carrier]
  (S : M.TopologicalData)

local notation "relativeRestriction" =>
  AlgEquiv.restrictScalarsHom (S := E.Carrier) (A := M.Carrier) F.Carrier

private theorem lowerGroup_relative_card (i : ℕ) :
    letI := Padic.integerAction S F.Carrier
    Nat.card (lowerGroup S.Integers (relativeRestriction).range i) =
      Padic.lowerGroupOrder S E.Carrier i := by
  let := Padic.integerAction S F.Carrier
  let e := MonoidHom.ofInjective (f := relativeRestriction)
    (AlgEquiv.restrictScalarsHom_injective F.Carrier)
  let ei : Padic.lowerRamificationGroup S E.Carrier i ≃
      lowerGroup S.Integers (relativeRestriction).range i := e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
  exact Nat.card_congr ei.symm

private theorem artinConductor_relative_character [Module.Finite F.Carrier M.Carrier]
    (χ : (M.Carrier ≃ₐ[F.Carrier] M.Carrier) →* ℂˣ) :
    letI := Padic.integerAction S F.Carrier
    letI := HerbrandBridge.integerAction_faithful S F.Carrier
    letI := Padic.integers_isNoetherianRing S
    artinConductor S.Integers (relativeRestriction).range
      (characterRepresentation (χ.comp (relativeRestriction).range.subtype)) =
        Padic.artinConductor S E.Carrier (characterRepresentation (χ.comp relativeRestriction)) := by
  let := Padic.integerAction S F.Carrier
  let := HerbrandBridge.integerAction_faithful S F.Carrier
  let := Padic.integers_isNoetherianRing S
  let e := MonoidHom.ofInjective (f := relativeRestriction)
    (AlgEquiv.restrictScalarsHom_injective F.Carrier)
  let ρ := characterRepresentation (χ.comp (relativeRestriction).range.subtype)
  let ρ' := characterRepresentation (χ.comp relativeRestriction)
  obtain ⟨b, hb⟩ := Padic.exists_lowerRamificationGroup_eq_bot S F.Carrier
  have hb' : ∀ i ≥ b, Padic.lowerRamificationGroup S E.Carrier i = ⊥ := by
    intro i hi
    rw [← Padic.lowerRamificationGroup_comap S F.Carrier E.Carrier, hb i hi, MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (AlgEquiv.restrictScalarsHom_injective F.Carrier)
  have hbH : ∀ i ≥ b, lowerGroup S.Integers (relativeRestriction).range i = ⊥ := by
    intro i hi
    ext τ
    change τ.val ∈ Padic.lowerRamificationGroup S F.Carrier i ↔ _
    rw [hb i hi, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg Subtype.val h
  change artinConductor S.Integers (relativeRestriction).range ρ = Padic.artinConductor S E.Carrier ρ'
  rw [artinConductor_eq_sum_range _ _ _ b hbH, Padic.artinConductor_eq_sum_range_lower _ _ _ b hb']
  apply Finset.sum_congr rfl
  intro i _
  have hfix : fixedVectors ρ (lowerGroup S.Integers (relativeRestriction).range i) =
      fixedVectors ρ' (Padic.lowerRamificationGroup S E.Carrier i) := by
    let ei : Padic.lowerRamificationGroup S E.Carrier i ≃
        lowerGroup S.Integers (relativeRestriction).range i :=
      e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
    ext x
    change (∀ g : lowerGroup S.Integers (relativeRestriction).range i, ρ g.val x = x) ↔
      ∀ τ : Padic.lowerRamificationGroup S E.Carrier i, ρ' τ.val x = x
    constructor
    · intro h τ
      exact h (ei τ)
    · intro h g
      obtain ⟨τ, rfl⟩ := ei.surjective g
      exact h τ
  simp only [conductorTerm, fixedCodimension, lowerGroup_relative_card F E M S,
    Padic.lowerGroupOrder]
  have hdim := congrArg (fun V : Submodule ℂ ℂ => Module.finrank ℂ V) hfix
  rw [hdim]

end GroupTransport

section Indices

variable {A G : Type u} [Group A] [CommGroup G] [Finite G]
    {r : A →* G} (hr : Function.Surjective r) (H : Subgroup G)

local notation "DualSubgroup" => CommGroup.subgroupOrderIsoSubgroupMonoidHom G ℂ H

/-- Indexing by characters killing a preimage agrees with indexing by the
characters of the quotient. -/
private def quotientCharacterIndices (X : Finset (A →* ℂˣ))
    (hX : ∀ κ, κ ∈ X ↔ H.comap r ≤ κ.ker) : X ≃ (DualSubgroup).ofDual := by
  let φ (κ : X) : {χ : A →* ℂˣ // r.ker ≤ χ.ker} :=
    ⟨κ.val, fun a ha => (hX κ.val).mp κ.property (show r a ∈ H from
      (MonoidHom.mem_ker.mp ha).symm ▸ H.one_mem)⟩
  let forward (κ : X) : (DualSubgroup).ofDual := ⟨r.liftOfSurjective hr (φ κ), by
    apply (CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff ℂ H _).mpr
    intro g hg
    obtain ⟨a, rfl⟩ := hr g
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact (hX κ.val).mp κ.property hg⟩
  let reverse (θ : (DualSubgroup).ofDual) : X := ⟨θ.val.comp r, (hX _).mpr fun a ha =>
    (CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_iff ℂ H _).mp θ.property _ ha⟩
  refine ⟨forward, reverse, ?_, ?_⟩
  · intro κ
    apply Subtype.ext
    apply MonoidHom.ext
    intro a
    exact r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hr) (φ κ) a
  · intro θ
    apply Subtype.ext
    apply MonoidHom.ext
    intro g
    obtain ⟨a, rfl⟩ := hr g
    exact r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hr) (φ (reverse θ)) a

private theorem quotientCharacterIndices_apply (X : Finset (A →* ℂˣ))
    (hX : ∀ κ, κ ∈ X ↔ H.comap r ≤ κ.ker) (κ : X) (a : A) :
    ((quotientCharacterIndices hr H X hX κ).val) (r a) = κ.val a := by
  unfold quotientCharacterIndices
  exact r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hr) _ a

end Indices

/-- A finite abelian extension of p-adic fields has the common Artin data
needed for the cyclic norm conductor comparison. -/
def PadicNormPullbackArtinDataStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := S.topology
    letI := S.valuativeRel
    letI := S.localField
    ∀ (χ : Quasicharacter F.Carrier) (f d : ℕ),
      IsResidueDegree F.Carrier E.Carrier f → IsDifferentExponent F.Carrier E.Carrier d →
      ∀ X : Finset (F.Carrierˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E.Carrier κ) →
        Nonempty (CyclicNormPullbackArtinData χ (χ.comp (localNorm T S)) f d X)

set_option maxHeartbeats 400000 in
/-- Finite-order normalization, the norm-subgroup existence theorem, and
finite conductor transport furnish a common finite Artin presentation. -/
theorem padicNormPullbackArtinData : PadicNormPullbackArtinDataStatement.{u} := by
  classical
  intro p _ F E _ _ _ T S
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  intro χ f d hf hd X hX
  let : FiniteDimensional F.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier E.Carrier
  obtain ⟨χ₀, ⟨m, hm, hχm⟩, htwist, hnorm⟩ :=
    T.exists_finiteOrder_preserving_twist_and_norm_conductors S χ
  obtain ⟨D, hD, ⟨j⟩, hkill⟩ :=
    exists_finiteAbelianStage_of_finiteOrder F E.Carrier T χ₀ hm hχm
  let : FiniteDimensional (Padic p) D.field := FiniteDimensional.trans (Padic p) F.Carrier D.field
  let M : PadicField.{u} p := PadicField.ofField D.field
  let SM := M.canonicalTopologicalData
  let : Algebra F.Carrier M.Carrier :=
    (inferInstance : Algebra F.Carrier D.field)
  let : FiniteDimensional (Padic p) M.Carrier := M.finiteDimensional
  let : FiniteDimensional F.Carrier M.Carrier := D.2
  let : IsAbelianGalois F.Carrier M.Carrier := hD
  let : IsScalarTower (Padic p) F.Carrier M.Carrier :=
    (inferInstance : IsScalarTower (Padic p) F.Carrier D.field)
  let : Algebra E.Carrier M.Carrier := j.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier E.Carrier M.Carrier :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : IsScalarTower (Padic p) E.Carrier M.Carrier := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier,
      ← IsScalarTower.algebraMap_apply F.Carrier E.Carrier M.Carrier,
      IsScalarTower.algebraMap_apply (Padic p) F.Carrier M.Carrier]
  let : IsAbelianGalois E.Carrier M.Carrier := IsAbelianGalois.tower_top F.Carrier E.Carrier M.Carrier
  let : FiniteDimensional E.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) E.Carrier M.Carrier
  let G := M.Carrier ≃ₐ[F.Carrier] M.Carrier
  let : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm' }
  let : Finite G := inferInstanceAs (Finite (M.Carrier ≃ₐ[F.Carrier] M.Carrier))
  let φ := AlgEquiv.restrictScalarsHom (S := E.Carrier) (A := M.Carrier) F.Carrier
  let H : Subgroup G := φ.range
  let r : F.Carrierˣ →* G := geometricSymbol F M.Carrier
  have hr : Function.Surjective r := geometricSymbol_surjective F M.Carrier
  have hker : r.ker = normSubgroup F.Carrier M.Carrier := ker_geometricSymbol F M.Carrier
  have hχker : r.ker ≤ χ₀.toMonoidHom.ker := hker.symm ▸ hkill
  let ψ := r.liftOfSurjective hr ⟨χ₀.toMonoidHom, hχker⟩
  have hψ (a : F.Carrierˣ) : ψ (r a) = χ₀ a :=
    r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hr) _ a
  have hpreimage : H.comap r = normSubgroup F.Carrier E.Carrier :=
    comap_relativeGaloisGroup_geometricSymbol F E M.Carrier
  have hindices (κ : F.Carrierˣ →* ℂˣ) : κ ∈ X ↔ H.comap r ≤ κ.ker := by
    rw [hX, hpreimage]
    constructor
    · intro h a ha
      obtain ⟨x, hx⟩ := ha
      exact hx ▸ h x
    · intro h x
      exact h ⟨x, rfl⟩
  let indices := quotientCharacterIndices hr H X hindices
  let κF (κ : X) := geometricArtinCharacter F M T SM (indices κ).val
  have hκ (κ : X) (a : F.Carrierˣ) : κF κ a = κ.val a := by
    change (indices κ).val (r a) = κ.val a
    exact quotientCharacterIndices_apply hr H X hindices κ a
  let R := SM.Integers
  let := Ramification.Padic.integerAction SM F.Carrier
  let := Ramification.HerbrandBridge.integerAction_faithful SM F.Carrier
  let := Ramification.Padic.integers_isNoetherianRing SM
  obtain ⟨b, hb⟩ := Ramification.Padic.exists_lowerRamificationGroup_eq_bot SM F.Carrier
  refine ⟨{
    G := G
    R := R
    H := H
    character := ψ
    indices := indices
    twists := fun κ => κF κ * χ
    twistCharacter := fun κ => MonoidHom.ext fun a => ?_
    twistConductor := ?_
    restrictionConductor := ?_
    residueDegree := ?_
    cutoff := b
    cutoff_spec := hb
    differentOrderSum := ?_ }⟩
  · change κF κ a * χ a = κ.val a * χ a
    rw [hκ]
  · intro κ
    have heq : κF κ * χ₀ = geometricArtinCharacter F M T SM (ψ * (indices κ).val) := by
      apply ContinuousMonoidHom.ext
      intro a
      change κF κ a * χ₀ a = ψ (r a) * (indices κ).val (r a)
      rw [hψ, mul_comm]
      rfl
    rw [htwist, heq]
    exact geometricArtin_multiplicativeConductor F M T SM _
  · have heq : χ₀.comp (localNorm T S) = geometricArtinCharacter E M S SM (ψ.comp φ) := by
      apply ContinuousMonoidHom.ext
      intro a
      change χ₀ (normUnits F.Carrier E.Carrier a) =
        ψ ((geometricSymbol E M.Carrier a).restrictScalars F.Carrier)
      rw [← geometricSymbol_norm F E M.Carrier a]
      exact (hψ _).symm
    refine (congrArg (fun n : ℕ => (n : ℚ)) hnorm).trans ?_
    refine (congrArg (fun ω : Quasicharacter E.Carrier => (S.multiplicativeConductor ω : ℚ))
      heq).trans ?_
    exact (geometricArtin_multiplicativeConductor E M S SM _).trans
      (artinConductor_relative_character F E M SM ψ).symm
  · rw [lowerGroup_relative_card F E M SM]
    exact residueDegree_eq_index_mul_inertia_ratio T S SM hf
  · calc
      _ = ∑ i ∈ Finset.range b, ((Ramification.Padic.lowerGroupOrder SM F.Carrier i : ℚ) -
          Ramification.Padic.lowerGroupOrder SM E.Carrier i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [lowerGroup_relative_card F E M SM]
        rfl
      _ = _ := (sum_lowerGroupOrder_sub_eq_different T S SM hd (hb b le_rfl)).trans (by
        rw [lowerGroup_relative_card F E M SM])

end Langlands.BaseChange
