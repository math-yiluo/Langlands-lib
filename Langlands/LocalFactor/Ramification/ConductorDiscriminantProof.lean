import Langlands.LocalFactor.Ramification.ConductorDiscriminantStatement
import Langlands.LocalFactor.Ramification.ArtinCharacter
import Langlands.LocalFactor.DeligneHenniartTopLayerDifferent
import Langlands.LocalField.DVRDiscriminantDifferentProof
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# The conductor–discriminant formula: proof

The function `δ = |G|·[g = 1]` (the character of the regular representation) is a class function
whose pairing with an irreducible character `χ` is `χ(1)`; by completeness of the irreducible
characters, `δ = Σ_χ χ(1) χ`. Applying the Artin functional,
`Σ_χ χ(1) a(χ) = |G_0|⁻¹ Σ_g i_G(g)(δ(1) − δ(g)) = [G:G_0] Σ_g i_G(g)`
(`sum_finrank_mul_artinConductor`). For a Galois extension `M/K` of p-adic fields, Hilbert's formula
(`TopLayer.differentIdeal_eq_maximalIdeal_pow`) gives the different `m_M ^ D` with
`D = Σ_{i<N}(|G_i| − 1) = Σ_{g≠1} i_G(g)`, the discriminant is then `m_K ^ (f D)`
(`LocalField.DiscriminantDifferent.span_discr_eq_maximalIdeal_pow`), and the fundamental identity
`e f = |G|` with `e = |G_0|` gives `f = [G:G_0]`.
-/

noncomputable section

namespace Langlands.Ramification

open Module

universe uR uG

section Generic

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R] [IsNoetherianRing R] [FaithfulSMul G R] [Fintype G]

/-- **The Artin conductor of the regular character**:
`Σ_χ χ(1) a(χ) = [G:G_0] Σ_g i_G(g)`, the sum over the irreducible classes. -/
theorem sum_finrank_mul_artinConductor [Fintype (FiniteRep.IrreducibleClass G)] :
    ∑ a : FiniteRep.IrreducibleClass G,
        (finrank ℂ a.out : ℂ) * ((artinConductor R G a.out.ρ : ℚ) : ℂ) =
      ((lowerGroup R G 0).index : ℂ) * ∑ g, (lowerDepth R G g : ℂ) := by
  classical
  let δ : G → ℂ := fun g => if g = 1 then (Fintype.card G : ℂ) else 0
  have hδ : ∀ g h : G, δ (h * g * h⁻¹) = δ g := by
    intro g h
    simp only [δ, conj_eq_one_iff]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hchar (a : FiniteRep.IrreducibleClass G) : FiniteRep.character a.1 = a.out.character := by
    rw [← FiniteRep.character_classOf]
    exact congrArg FiniteRep.character (Quotient.out_eq _).symm
  have hpair (a : FiniteRep.IrreducibleClass G) :
      FiniteRep.VirtualCharacter.pairing (FiniteRep.character a.1) δ = finrank ℂ a.out := by
    rw [FiniteRep.CharacterCompleteness.pairing_apply]
    simp only [δ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, inv_one]
    rw [hchar, FDRep.char_one]
    field_simp
  have hexp := FiniteRep.CharacterCompleteness.eq_sum_pairing_smul δ hδ
  simp only [hpair] at hexp
  -- apply the Artin functional to both sides
  have hfun := congrArg (artinFunctional R G) hexp
  rw [map_sum] at hfun
  simp only [map_smul, smul_eq_mul] at hfun
  have hterm (a : FiniteRep.IrreducibleClass G) :
      artinFunctional R G (FiniteRep.character a.1) = ((artinConductor R G a.out.ρ : ℚ) : ℂ) := by
    rw [hchar]
    exact artinFunctional_character R G a.out.ρ
  simp only [hterm] at hfun
  rw [← hfun, artinFunctional_apply]
  have hδdiff : ∀ g : G, (lowerDepth R G g : ℂ) * (δ 1 - δ g) =
      (Fintype.card G : ℂ) * lowerDepth R G g := by
    intro g
    by_cases hg : g = 1
    · subst hg
      simp
    · simp only [δ, hg, ↓reduceIte, sub_zero]
      ring
  simp only [hδdiff, ← Finset.mul_sum]
  rw [← mul_assoc]
  congr 1
  have hi := (lowerGroup R G 0).index_mul_card
  have hc : (Nat.card (lowerGroup R G 0) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [Nat.card_eq_fintype_card (α := G)] at hi
  rw [← hi]
  push_cast
  field_simp

end Generic

namespace Padic

open IsLocalRing PadicField.TopologicalData LocalFactor.NonabelianSystem.DeligneHenniart

universe uK uM uι

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uK} p} {M : PadicField.{uM} p}
  [Algebra K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier M.Carrier]
  (TK : K.TopologicalData) (TM : M.TopologicalData)

/-- The sum of the depths is the exponent of Hilbert's formula. -/
theorem sum_lowerDepth_eq [Fintype (M.Carrier ≃ₐ[K.Carrier] M.Carrier)] {N : ℕ}
    (hN : lowerRamificationGroup TM K.Carrier N = ⊥) :
    letI := integerAction TM K.Carrier
    ∑ g, Ramification.lowerDepth TM.Integers (M.Carrier ≃ₐ[K.Carrier] M.Carrier) g =
      ∑ i ∈ Finset.range N, (lowerGroupOrder TM K.Carrier i - 1) := by
  classical
  let := integerAction TM K.Carrier
  have hb : ∀ i ≥ N, lowerGroup TM.Integers (M.Carrier ≃ₐ[K.Carrier] M.Carrier) i = ⊥ :=
    fun i hi => le_bot_iff.mp (hN ▸ lowerRamificationGroup_antitone TM K.Carrier hi)
  rw [← TopLayer.sum_lowerDepth_erase_one TM N,
    ← Finset.sum_erase _ (Ramification.lowerDepth_one (R := TM.Integers))]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [← lowerCount_eq_lowerDepth hb (Finset.ne_of_mem_erase hσ)]
  rfl

/-- **The residue degree is the index of inertia**: for `M/K` Galois, the inertia degree of the
maximal ideal of `O_M` over `O_K` is `[G:G_0]`. -/
theorem inertiaDeg_eq_index [IsGalois K.Carrier M.Carrier] :
    letI := TK.valuativeRel
    letI := TM.valuativeRel
    letI := relativeIntegerAlgebra TK TM
    (maximalIdeal TM.Integers).inertiaDeg TK.Integers = (inertia TM K.Carrier).index := by
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeIntegerAlgebra TK TM
  let := integerAction TM K.Carrier
  have : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  have hG := TopLayer.isGaloisGroup_integers TK TM
  have := relativeIntegerAlgebra_isTorsionFree TK TM
  have : IsLocalHom (algebraMap TK.Integers TM.Integers) := relativeIntegerMap_isLocalHom TK TM
  let := relativeIntegerFieldAlgebra (E := M) TK
  have := (LocalClassField.UniverseZero.relativeIntegerStructure p K M TK TM).2
  have : Algebra.IsIntegral TK.Integers TM.Integers := Algebra.IsIntegral.of_finite _ _
  have : Finite (maximalIdeal TK.Integers).ResidueField := by
    have : Finite (TK.Integers ⧸ maximalIdeal TK.Integers) := TK.finite_residueField
    exact Finite.of_surjective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal TK.Integers)).2
  have : Module.Free TK.Integers TM.Integers := Module.free_of_finite_type_torsion_free'
  have : Finite (M.Carrier ≃ₐ[K.Carrier] M.Carrier) :=
    LocalFactor.SpectralConductor.automorphismGroup_finite' (E := M) K.Carrier
  have hLies : (maximalIdeal TM.Integers).LiesOver (maximalIdeal TK.Integers) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap TK.Integers TM.Integers)).symm⟩
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (maximalIdeal TK.Integers) TM.Integers (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
  have hprimes : (Ideal.primesOver (maximalIdeal TK.Integers) TM.Integers).ncard = 1 := by
    refine Set.ncard_eq_one.mpr ⟨maximalIdeal TM.Integers, Set.ext fun P => ?_⟩
    constructor
    · rintro ⟨hP, hPo⟩
      have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (maximalIdeal TK.Integers)
      exact IsLocalRing.eq_maximalIdeal this
    · rintro rfl
      exact ⟨inferInstance, hLies⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := M.Carrier ≃ₐ[K.Carrier] M.Carrier) (maximalIdeal TK.Integers) (maximalIdeal TM.Integers)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg _ (maximalIdeal TM.Integers)
    (M.Carrier ≃ₐ[K.Carrier] M.Carrier), hprimes, one_mul, ← hcard,
    ← TopLayer.lowerRamificationGroup_zero_eq_inertia TM, lowerRamificationGroup_zero] at hfund
  have hi := (inertia TM K.Carrier).index_mul_card
  have hpos : 0 < Nat.card (inertia TM K.Carrier) := Nat.card_pos
  rw [← hi, mul_comm] at hfund
  exact Nat.eq_of_mul_eq_mul_right hpos hfund

/-- **The conductor–discriminant formula.** -/
theorem finiteConductorDiscriminant : FiniteConductorDiscriminantStatement.{uK, uM, uι} := by
  intro p _ K M _ _ _ TK TM ι _ _ b
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeIntegerAlgebra TK TM
  let := relativeIntegerFieldAlgebra (E := M) TK
  have := relativeIntegerFieldTower (E := M) TK
  have := relativeIntegerTower TK TM
  have := relativeIntegerAlgebra_isTorsionFree TK TM
  have : IsLocalHom (algebraMap TK.Integers TM.Integers) := relativeIntegerMap_isLocalHom TK TM
  have : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  obtain ⟨hic, hfin⟩ := LocalClassField.UniverseZero.relativeIntegerStructure p K M TK TM
  have : Finite (ResidueField TK.Integers) := TK.finite_residueField
  have : Finite (ResidueField TM.Integers) := TM.finite_residueField
  have : Algebra.IsSeparable (ResidueField TK.Integers) (ResidueField TM.Integers) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Module.Free TK.Integers TM.Integers := Module.free_of_finite_type_torsion_free'
  have hdisc : ∀ N : ℕ, lowerRamificationGroup TM K.Carrier N = ⊥ →
      Ideal.span {Algebra.discr TK.Integers b} =
        maximalIdeal TK.Integers ^ ((inertia TM K.Carrier).index *
          ∑ i ∈ Finset.range N, (lowerGroupOrder TM K.Carrier i - 1)) := by
    intro N hN
    rw [← inertiaDeg_eq_index TK TM]
    exact LocalField.DiscriminantDifferent.span_discr_eq_maximalIdeal_pow K.Carrier M.Carrier b _
      (TopLayer.differentIdeal_eq_maximalIdeal_pow TK TM hN)
  refine ⟨hdisc, ?_⟩
  intro _
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot TM K.Carrier
  rw [hdisc N (hN N le_rfl)]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  -- the exponents: `[G:G_0] D = Σ_χ a(χ) χ(1)`
  let := integerAction TM K.Carrier
  have := HerbrandBridge.integerAction_faithful TM K.Carrier
  have := LocalFactor.SpectralConductor.integerRing_noetherian' TM
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := M) K.Carrier
  let := Fintype.ofFinite (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
  have hsum := Ramification.sum_finrank_mul_artinConductor TM.Integers
    (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
  have hD := sum_lowerDepth_eq TM (hN N le_rfl)
  have h0 : lowerGroup TM.Integers (M.Carrier ≃ₐ[K.Carrier] M.Carrier) 0 = inertia TM K.Carrier :=
    lowerRamificationGroup_zero TM K.Carrier
  rw [h0, ← Nat.cast_sum, hD] at hsum
  have hexp (a : FiniteRep.IrreducibleClass (M.Carrier ≃ₐ[K.Carrier] M.Carrier)) :
      ((Ramification.artinConductor TM.Integers (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
        a.out.ρ : ℚ) : ℂ) = (artinExponent TM K.Carrier a.out.ρ : ℂ) := by
    rw [← Rat.cast_natCast, artinExponent_cast]
    rfl
  simp only [hexp] at hsum
  apply Nat.cast_injective (R := ℂ)
  rw [Nat.cast_mul, ← hsum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun a _ => by push_cast; ring

end Padic

end Langlands.Ramification
