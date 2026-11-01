import Langlands.Representation.Exponents.CoarseFineTwistScalarCharacterProof
import Langlands.Representation.Exponents.RealCentralBlock

/-! Coarse scalar action on actual inner induction. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV

namespace InnerInducedCoarseScalar

/-- Actual inner induction inherits a scalar character along the repeated
coarse block scalars, since its half modulus is trivial there. -/
theorem scalarAction
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (hscalar : ∀ (a : Fin B.length → F.Carrierˣ) (w : τ),
      τ.ρ (flattenedLeviEquiv F.Carrier B S
        ((B.flatten S).blockScalarLevi F.Carrier (a ∘ B.flattenOuter S))) w =
          (χ a : ℂ) • w) :
    Classification.HasScalarCharacter (innerInduced T B S τ).ρ
      (B.blockScalarLevi F.Carrier) χ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro a f
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change Induction.eval _ _ f (g * B.blockScalarLevi F.Carrier a) =
    (χ a : ℂ) • Induction.eval _ _ f g
  let m := flattenedLeviEquiv F.Carrier B S
    ((B.flatten S).blockScalarLevi F.Carrier (a ∘ B.flattenOuter S))
  have hcov := normalizedRefinedInducedOf_covariant B S
    (T.refinedLeviHalfModulus B S) τ.ρ f
    (refinedLeviSection F.Carrier B S m) g
  simp only [refinedLeviSection_val, refinedLeviProjection_section] at hcov
  have hm : m.val = B.blockScalarLevi F.Carrier a :=
    B.flattenedLeviEquiv_blockScalarLevi_comp S F.Carrier a
  rw [hm, B.blockScalarLevi_commute F.Carrier a g] at hcov
  have hδ : T.refinedLeviHalfModulus B S m = 1 :=
    T.refinedLeviHalfModulus_blockScalarLevi_comp B S a
  rw [hδ, Units.val_one, one_smul, hscalar] at hcov
  exact hcov

/-- An exact coarse scalar character of a smooth representation places the
entire actual carrier in its corresponding full-central real block. -/
theorem realBlockEqTopOfScalar
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ)
    (x : Fin B.length → ℝ)
    (hscalar : Classification.HasScalarCharacter ρ (B.blockScalarLevi F.Carrier) χ) :
    letI := T.topology
    IsSmooth ρ → T.IsRealPartOf χ x → T.realCentralBlock B ρ x = ⊤ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro hρ hreal
  rcases subsingleton_or_nontrivial V with hV | hV
  · let := hV
    apply le_antisymm le_top
    intro v _
    have hv : v = 0 := Subsingleton.elim _ _
    rw [hv]
    exact Submodule.zero_mem _
  let := hV
  let e := B.blockScalarCenterEquiv F.Carrier
  let ψ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ :=
    χ.comp e.symm.toMonoidHom
  have hψ : Classification.HasScalarCharacter ρ
      (Subgroup.center (B.Levi F.Carrier)).subtype ψ := by
    intro z v
    obtain ⟨a, rfl⟩ := e.surjective z
    change ρ (B.blockScalarLevi F.Carrier a) v = (χ (e.symm (e a)) : ℂ) • v
    rw [e.symm_apply_apply]
    exact hscalar a v
  have heq : ψ.comp (B.blockScalarToCenter F.Carrier) = χ := by
    apply MonoidHom.ext
    intro a
    change χ (e.symm (e a)) = χ a
    rw [e.symm_apply_apply]
  apply groupedCentralCharacterSpace_eq_top_of_scalar ρ _ ψ ?_ hψ
  refine ⟨hψ.isOpen_ker continuous_subtype_val hρ, ?_⟩
  rw [heq]
  exact hreal

/-- The nested fine twist gives the actual inner induction an open-kernel
coarse scalar character with the prescribed size-weighted real part. -/
theorem nestedScalarCharacter
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (ω : Rep.{uV} ℂ (((B.flatten Q).flatten R).Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → IsAdmissible ω.ρ → IsUnitarizable ω.ρ →
    ∀ (v₀ : Fin ((B.flatten Q).flatten R).length → ℝ),
      IsPositiveRootParameter (B.flatten Q) R v₀ →
      let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
      let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
      ∀ t : Fin B.length → ℝ,
        ∃ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
          IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) ∧
          Classification.HasScalarCharacter
            (innerInduced T B S (fineTwist T B S ωB vB t)).ρ
            (B.blockScalarLevi F.Carrier) χ ∧
          T.IsRealPartOf χ (fun i => (B.size i : ℝ) * t i) := by
  let := T.topology
  dsimp only
  intro hi ha hu v₀ hv t
  obtain ⟨χ, hopen, hscalar, hreal⟩ :=
    Exponents.coarseFineTwistScalarCharacter
      p F T n B Q R S h ω hi ha hu v₀ hv t
  exact ⟨χ, hopen, scalarAction T B S _ χ hscalar, hreal⟩

/-- The actual nested inner induction is its entire real central block at the
size-weighted coarse parameter. -/
theorem nestedRealBlockEqTop
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (ω : Rep.{uV} ℂ (((B.flatten Q).flatten R).Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → IsAdmissible ω.ρ → IsUnitarizable ω.ρ →
    ∀ (v₀ : Fin ((B.flatten Q).flatten R).length → ℝ),
      IsPositiveRootParameter (B.flatten Q) R v₀ →
      let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
      let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
      ∀ t : Fin B.length → ℝ,
        T.realCentralBlock B (innerInduced T B S (fineTwist T B S ωB vB t)).ρ
          (fun i => (B.size i : ℝ) * t i) = ⊤ := by
  let := T.topology
  dsimp only
  intro hi ha hu v₀ hv t
  obtain ⟨χ, _, hscalar, hreal⟩ :=
    nestedScalarCharacter T B Q R S h ω hi ha hu v₀ hv t
  exact realBlockEqTopOfScalar T B _ χ _ hscalar
    (T.isSmooth_normalizedRefinedInduced B S _) hreal

end InnerInducedCoarseScalar

end Langlands
