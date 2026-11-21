import Langlands.BaseChange.PadicArithmeticTransport
import Langlands.BaseChange.PadicNormPullbackArtinData

/-! # The conductor identity for a p-adic norm pullback -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField LocalClassField.NYLL Ramification
open scoped BigOperators Classical

universe u v

private theorem sum_twistConductors_of_artinData
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {χ : Quasicharacter F} {η : Quasicharacter E} {f d : ℕ} {X : Finset (Fˣ →* ℂˣ)}
    (D : CyclicNormPullbackArtinData χ η f d X) :
    ∑ κ : X, (LocalFieldData.ofInstances F).multiplicativeConductor (D.twists κ) =
      f * ((LocalFieldData.ofInstances E).multiplicativeConductor η + d) := by
  let := D.commGroup
  let := D.finiteGroup
  let := D.commRing
  let := D.localRing
  let := D.noetherianRing
  let := D.action
  let := D.faithfulAction
  let Q := (CommGroup.subgroupOrderIsoSubgroupMonoidHom D.G ℂ D.H).ofDual
  let : Fintype Q := Fintype.ofFinite Q
  have hsum : (∑ κ : X, ((LocalFieldData.ofInstances F).multiplicativeConductor (D.twists κ) : ℚ)) =
      ∑ κ : Q, artinConductor D.R D.G (characterRepresentation (D.character * κ.val)) :=
    Fintype.sum_equiv D.indices _ _ D.twistConductor
  have h := sum_artinConductor_twists_trivial_on D.R D.H D.character
  rw [sum_artinConductor_trivial_on D.R D.H D.cutoff D.cutoff_spec,
    D.differentOrderSum, ← D.restrictionConductor] at h
  have hfactor := D.residueDegree
  have h' : (∑ κ : Q, artinConductor D.R D.G (characterRepresentation (D.character * κ.val))) =
      (f : ℚ) * ((LocalFieldData.ofInstances E).multiplicativeConductor η + (d : ℚ)) := by
    rw [h, hfactor]
    ring
  exact_mod_cast hsum.trans h'

/-- The local norm-pullback conductor formula for supplied p-adic fields
in independent carrier universes. -/
def PadicNormPullbackConductorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
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
        ∃ a : (F.Carrierˣ →* ℂˣ) → ℕ,
          (∀ κ ∈ X, ∃ χκ : Quasicharacter F.Carrier,
            χκ.toMonoidHom = κ * χ.toMonoidHom ∧
            (LocalFieldData.ofInstances F.Carrier).multiplicativeConductor χκ = a κ) ∧
          ∑ κ ∈ X, a κ = f * ((LocalFieldData.ofInstances E.Carrier).multiplicativeConductor
            (χ.comp (localNorm T S)) + d)

set_option maxHeartbeats 400000 in
/-- Apply the common finite Artin presentation in universe zero, then
transport the characters and conductors to the supplied fields. -/
theorem padicNormPullbackConductor : PadicNormPullbackConductorStatement.{u, v} := by
  intro p _ F E _ _ _ T S
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  intro χ f d hf hd X hX
  let F₀ := universeZeroModel F
  let E₀ := universeZeroModel E
  let T₀ := F₀.canonicalTopologicalData
  let S₀ := E₀.canonicalTopologicalData
  let := T₀.topology
  let := T₀.valuativeRel
  let := T₀.localField
  let := S₀.topology
  let := S₀.valuativeRel
  let := S₀.localField
  let := universeZeroAlgebra F E
  let := universeZeroAlgebra_isScalarTower F E
  let := universeZeroAlgebra_isAbelianGalois F E
  let eF := universeZeroEquiv F
  let eE := universeZeroEquiv E
  let j := Units.mapEquiv eF.toMulEquiv
  let k := Units.mapEquiv eE.toMulEquiv
  let emb : (F.Carrierˣ →* ℂˣ) ↪ (F₀.Carrierˣ →* ℂˣ) :=
    ⟨fun κ => κ.comp j.toMonoidHom, fun {_ _} h => MonoidHom.ext fun a => by
      obtain ⟨a, rfl⟩ := j.surjective a
      exact DFunLike.congr_fun h a⟩
  let X₀ := X.map emb
  let eX : X ≃ X₀ := Finset.equivMap emb X
  have hn (a : E₀.Carrierˣ) : j (Units.map (Algebra.norm F₀.Carrier) a) =
      Units.map (Algebra.norm F.Carrier) (k a) := Units.ext (universeZeroEquiv_norm F E a.val)
  have hnorm (κ : F.Carrierˣ →* ℂˣ) : IsNormTrivial E₀.Carrier (emb κ) ↔
      IsNormTrivial E.Carrier κ := by
    constructor
    · intro h a
      obtain ⟨a, rfl⟩ := k.surjective a
      exact congrArg κ (hn a) ▸ h a
    · intro h a
      exact (congrArg κ (hn a)).trans (h (k a))
  have hX₀ (κ₀ : F₀.Carrierˣ →* ℂˣ) : κ₀ ∈ X₀ ↔ IsNormTrivial E₀.Carrier κ₀ := by
    let κ : F.Carrierˣ →* ℂˣ := κ₀.comp j.symm.toMonoidHom
    have he : emb κ = κ₀ := MonoidHom.ext fun x => congrArg κ₀ (j.symm_apply_apply x)
    rw [← he]
    have hmem : emb κ ∈ X₀ ↔ κ ∈ X := by
      constructor
      · intro h
        obtain ⟨κ', hκ', h'⟩ := Finset.mem_map.mp h
        exact emb.injective h' ▸ hκ'
      · intro h
        exact Finset.mem_map.mpr ⟨κ, h, rfl⟩
    exact hmem.trans ((hX κ).trans (hnorm κ).symm)
  let χ₀ := padicCharacterPullback T₀ T eF χ
  obtain ⟨D⟩ := padicNormPullbackArtinData p F₀ E₀ T₀ S₀ χ₀ f d
    (isResidueDegree_universeZero T S hf) (isDifferentExponent_universeZero T S hd) X₀ hX₀
  let a (κ : F.Carrierˣ →* ℂˣ) : ℕ := if hκ : κ ∈ X then
    (LocalFieldData.ofInstances F₀.Carrier).multiplicativeConductor (D.twists (eX ⟨κ, hκ⟩)) else 0
  refine ⟨a, ?_, ?_⟩
  · intro κ hκ
    let κ₀ := eX ⟨κ, hκ⟩
    let χκ := padicCharacterPullback T T₀ eF.symm (D.twists κ₀)
    refine ⟨χκ, ?_, ?_⟩
    · apply MonoidHom.ext
      intro y
      obtain ⟨y, rfl⟩ := j.surjective y
      change (D.twists κ₀) (j.symm (j y)) = κ (j y) * χ (j y)
      rw [j.symm_apply_apply]
      exact DFunLike.congr_fun (D.twistCharacter κ₀) y
    · dsimp only [a]
      rw [dite_eq_left hκ]
      exact padicCharacterPullback_multiplicativeConductor T T₀ eF.symm (D.twists κ₀)
  · have hsum : ∑ κ ∈ X, a κ =
        ∑ κ₀ : X₀, (LocalFieldData.ofInstances F₀.Carrier).multiplicativeConductor (D.twists κ₀) := by
      rw [← Finset.sum_coe_sort]
      exact Fintype.sum_equiv eX _ _ (fun κ => by simp only [a, dite_eq_left κ.property])
    have hη : χ₀.comp (localNorm T₀ S₀) = padicCharacterPullback S₀ S eE (χ.comp (localNorm T S)) :=
      ContinuousMonoidHom.ext fun a => congrArg χ (hn a)
    have he := congrArg (LocalFieldData.ofInstances E₀.Carrier).multiplicativeConductor hη
    calc
      ∑ κ ∈ X, a κ = _ := hsum
      _ = _ := sum_twistConductors_of_artinData D
      _ = _ := congrArg (fun n : ℕ => f * (n + d))
        (he.trans (padicCharacterPullback_multiplicativeConductor S₀ S eE (χ.comp (localNorm T S))))

end Langlands.BaseChange
