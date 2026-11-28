import Langlands.BushnellKutzko.SimpleTypeTransportStatement
import Langlands.BushnellKutzko.LayerReductionTransport
import Langlands.BushnellKutzko.PrincipalOrderConjugacy
import Langlands.BushnellKutzko.ElementFieldInvariantTransport

/-! # Transport of simple type data and conjugacy of principal orders: proof -/

noncomputable section

open ValuativeRel IsLocalRing
open Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Conjugation carries principal orders to principal orders. -/
theorem isPrincipalOrder_linearEquivMap (f : V ≃ₗ[F] V) {L : LatticeChain 𝒪[F] F V}
    (h : IsPrincipalOrder L.order) : IsPrincipalOrder (L.linearEquivMap f).order := by
  obtain ⟨M, hM, hP⟩ := h
  exact ⟨M.linearEquivMap f, ((M.corresponds_linearEquivMap f).order_eq_iff
    (L.corresponds_linearEquivMap f)).2 hM, M.isPrincipal_linearEquivMap f hP⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A linear automorphism carries a lattice chain onto its image chain, linearly over
`𝒪_F`. -/
theorem LatticeChain.semilinearImage_linearEquivMap (L : LatticeChain 𝒪[F] F V)
    (f : V ≃ₗ[F] V) :
    L.SemilinearImage (RingEquiv.refl 𝒪[F]) f.toAddEquiv (L.linearEquivMap f) where
  map_smul a v := by
    change f (a • v) = a • f v
    rw [← algebraMap_smul F a v, ← algebraMap_smul F a (f v), map_smul]
  mem_iff i v := by
    change v ∈ L.lattice i ↔ f v ∈ (L.linearEquivMap f).lattice i
    rw [LatticeChain.mem_linearEquivMap, LinearEquiv.symm_apply_apply]

/-- **Kind (b).** Conjugation transports level-zero simple type data (BK93 (5.5.10)(b)). -/
theorem isLevelZeroSimpleTypeData_conj (g : G) {J : Subgroup G} (ρ : Representation ℂ J W)
    (L : LatticeChain 𝒪[F] F V) (e : ℕ) (h : IsLevelZeroSimpleTypeData L e ρ) :
    (L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g)).period = L.period ∧
      IsLevelZeroSimpleTypeData (L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g))
        e (conjRepresentation g ρ) := by
  obtain ⟨hP, he, f, d, σ₀, hirr, hcusp, b, φ, hred, htriv, hpair⟩ := h
  let fL := LinearMap.GeneralLinearGroup.toLinearEquiv g
  let L' := L.linearEquivMap fL
  have hper : L'.period = L.period := L.period_linearEquivMap fL
  have hSI := L.semilinearImage_linearEquivMap fL
  have hU : L'.unitFiltration 0 = conjugateSubgroup g (L.unitFiltration 0) :=
    unitFiltration_linearEquivMap g L 0
  have hU1 : L'.unitFiltration 1 = conjugateSubgroup g (L.unitFiltration 1) :=
    unitFiltration_linearEquivMap g L 1
  let b' : ∀ i : Fin e, Module.Basis (Fin f) (ResidueField 𝒪[F]) (L'.Layer ((i : ℕ) : ℤ)) :=
    fun i => hSI.layerBasis _ (b i)
  let φ' : L'.unitFiltration 0 →* (Fin e → GeneralLinear f (ResidueField 𝒪[F])) :=
    φ.comp (conjEquivOfEq g hU).symm.toMonoidHom
  refine ⟨hper, isPrincipalOrder_linearEquivMap fL hP, he.trans hper.symm, f, d, σ₀, hirr, hcusp,
    b', φ', ?_, ?_, ?_⟩
  · refine hSI.isLayerReduction g (fun _ => rfl) hU _ _ b' φ'
      (fun i x => hSI.layerBasis_equivFun _ (b i) x) (fun u i => ?_) hred
    rw [ResidueField.mapEquiv_refl]
    ext a c
    rfl
  · intro j hj
    apply htriv
    change ((conjSubgroupEquiv g J).symm j : G) ∈ L.unitFiltration 1
    rw [conjSubgroupEquiv_symm_val, ← mem_conjugateSubgroup_iff, ← hU1]
    exact hj
  · have := IsPairIsomorphic.conj g hU hpair
    rwa [MonoidHom.comp_assoc] at this

/-- **Kind (a).** Conjugation transports simple type data over a simple character
(BK93 (5.5.10)(a)), with the conjugated stratum, the conjugated character and the same
period. -/
theorem isSimpleTypeDataOver_conj (ψF : AddChar F ℂ) (g : G) {J : Subgroup G}
    (ρ : Representation ℂ J W) (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (e : ℕ)
    (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ) (h : IsSimpleTypeDataOver ψF S q e θ ρ) :
    ∃ (T : Stratum 𝒪[F] F V) (q' : T.DefiningSequenceChoice)
      (θ' : simpleHGroup T.chain T.n T.b q'.tail 1 →* ℂˣ),
      T.chain = S.chain.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g) ∧
      T.n = S.n ∧ T.r = S.r ∧
      T.b = (LinearMap.GeneralLinearGroup.toLinearEquiv g).conjRingEquiv S.b ∧
      (⟨_, θ'⟩ : CharacterPair G) = CharacterPair.conj g⁻¹ ⟨_, θ⟩ ∧
      IsSimpleTypeDataOver ψF T q' e θ' (conjRepresentation g ρ) := by
  obtain ⟨hψ, hr, hP, hS, he, hθ, dη, η, hη, dκ, κ, hκ, fdeg, d, σ₀, hirr, hcusp, b, φ, hred,
    dσ, σ, hσsm, hσtriv, ⟨eσ⟩, hpair⟩ := h
  let fL := LinearMap.GeneralLinearGroup.toLinearEquiv g
  let L := S.chain
  let L' := L.linearEquivMap fL
  have hLL' : L.Corresponds fL L' := L.corresponds_linearEquivMap fL
  let T : Stratum 𝒪[F] F V := S.transport fL L' hLL'
  have hST : S.Corresponds fL T := S.corresponds_transport fL L' hLL'
  have hT : T.IsSimple := hST.isSimple_iff.2 hS
  let q' : T.DefiningSequenceChoice := q.transport fL hST
  have htail : q'.tail = q.tail.map (endConj fL) :=
    Stratum.DefiningSequenceChoice.tail_transport fL hST q
  have hHk : ∀ k, simpleHGroup L' T.n T.b q'.tail k =
      conjugateSubgroup g (simpleHGroup L S.n S.b q.tail k) := fun k =>
    (hLL'.simpleHGroup_eq_of_eq S.n rfl htail k).trans (map_unitsConj_toLinearEquiv g _)
  have hJk : ∀ k, simpleJGroup L' T.n T.b q'.tail k =
      conjugateSubgroup g (simpleJGroup L S.n S.b q.tail k) := fun k =>
    (hLL'.simpleJGroup_eq_of_eq S.n rfl htail k).trans (map_unitsConj_toLinearEquiv g _)
  let θ' : simpleHGroup T.chain T.n T.b q'.tail 1 →* ℂˣ :=
    θ.comp (conjEquivOfEq g (hHk 1)).symm.toMonoidHom
  have hcorr : CharacterCorresponds (unitsConj fL) θ θ' := by
    intro x hx hx'
    change θ ((conjEquivOfEq g (hHk 1)).symm ⟨_, hx'⟩) = θ ⟨x, hx⟩
    congr 1
    apply Subtype.ext
    rw [coe_conjEquivOfEq_symm]
    change g⁻¹ * unitsConj fL x * g = x
    rw [unitsConj_toLinearEquiv]
    group
  refine ⟨T, q', θ', rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact characterPair_eq_conj (unitsConj fL) g (unitsConj_toLinearEquiv g)
      (hLL'.simpleHGroup_eq_of_eq S.n rfl htail 1) hcorr
  -- the fields and residue fields
  let := hS.1.1.fst.toField
  let := hT.1.1.fst.toField
  have : FiniteDimensional F (elementAlgebra S.b) :=
    S.chain.finiteDimensional_subfield (elementAlgebra S.b)
  have : FiniteDimensional F (elementAlgebra T.b) :=
    T.chain.finiteDimensional_subfield (elementAlgebra T.b)
  have := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b)
  have := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra T.b)
  let σE : elementAlgebra S.b ≃ₐ[F] elementAlgebra T.b := elementAlgebraAlgConj fL S.b
  let σO : subfieldIntegers F (elementAlgebra S.b) ≃+* subfieldIntegers F (elementAlgebra T.b) :=
    (subfieldIntegersAlgEquiv F σE).toRingEquiv
  let σk := ResidueField.mapEquiv σO
  let μ := generalLinearMapEquiv σk fdeg
  let 𝓛E := S.chain.subfieldChain (elementAlgebra S.b) hS.1.1.snd
  let 𝓛E' := T.chain.subfieldChain (elementAlgebra T.b) hT.1.1.snd
  have hSI : 𝓛E.SemilinearImage σO fL.toAddEquiv 𝓛E' :=
    { map_smul := fun a v => by
        change fL ((((a : elementAlgebra S.b) : Module.End F V)) v) =
          (((σO a : elementAlgebra T.b) : Module.End F V)) (fL v)
        change _ = endConj fL ((a : elementAlgebra S.b) : Module.End F V) (fL v)
        rw [endConj_apply_apply]
      mem_iff := fun i v => hLL' i v }
  have hU : relativeUnitFiltration T.chain T.b 0 =
      conjugateSubgroup g (relativeUnitFiltration S.chain S.b 0) :=
    relativeUnitFiltration_linearEquivMap g S.chain S.b 0
  let b' : ∀ i : Fin e, Module.Basis (Fin fdeg) (ResidueField (subfieldIntegers F
      (elementAlgebra T.b))) (𝓛E'.Layer ((i : ℕ) : ℤ)) :=
    fun i => hSI.layerBasis _ (b i)
  let φ' : relativeUnitFiltration T.chain T.b 0 →*
      (Fin e → GeneralLinear fdeg (ResidueField (subfieldIntegers F (elementAlgebra T.b)))) :=
    (MonoidHom.piMap fun _ : Fin e => μ.toMonoidHom).comp
      (φ.comp (conjEquivOfEq g hU).symm.toMonoidHom)
  let η' := η.comp (conjEquivOfEq g (hJk 1)).symm.toMonoidHom
  let κ' := κ.comp (conjEquivOfEq g (hJk 0)).symm.toMonoidHom
  let σ' := σ.comp (conjEquivOfEq g (hJk 0)).symm.toMonoidHom
  refine ⟨hψ, hr, isPrincipalOrder_linearEquivMap fL hP, hT, he.trans hSI.period_eq.symm,
    (hLL'.mem_simpleCharacters_of_eq ψF S.n rfl htail 0 θ θ' hcorr).2 hθ, dη, η',
    hη.conj g (hHk 1) (hJk 1), dκ, κ', hκ.conj g (hJk 1) (hJk 0), fdeg, d,
    σ₀.comp μ.symm.toMonoidHom, isIrreducible_comp_mulEquiv σ₀ μ.symm hirr,
    isCuspidal_comp_generalLinearMapEquiv σk hcusp, b', φ', ?_, dσ, σ', hσsm.conj g (hJk 0),
    ?_, ?_, ?_⟩
  · exact hSI.isLayerReduction g (fun _ => rfl) hU _ _ b' φ'
      (fun i x => hSI.layerBasis_equivFun _ (b i) x) (fun u i => rfl) hred
  · intro j hj
    apply hσtriv
    change ((conjEquivOfEq g (hJk 0)).symm j : G) ∈ simpleJGroup S.chain S.n S.b q.tail 1
    have hj' : (j : G) ∈ simpleJGroup L' T.n T.b q'.tail 1 := hj
    rw [hJk 1, mem_conjugateSubgroup_iff] at hj'
    convert hj' using 1
    exact coe_conjEquivOfEq_symm g (hJk 0) j
  · refine ⟨equivOfPullback eσ (conjEquivOfEq g hU).symm.toMonoidHom (fun x => ?_) (fun x => ?_)⟩
    · change σ ((conjEquivOfEq g (hJk 0)).symm _) = σ (Subgroup.inclusion _ _)
      congr 1
      apply Subtype.ext
      exact (coe_conjEquivOfEq_symm g (hJk 0) _).trans (coe_conjEquivOfEq_symm g hU x).symm
    · exact DFunLike.congr_fun (tensorPowerRepresentation_comp_piMap σ₀ μ e)
        (φ ((conjEquivOfEq g hU).symm x))
  · exact IsPairIsomorphic.conj g (hJk 0) hpair

/-- **Transport of simple type data and conjugacy of principal orders** (BK93 (5.5.10),
§1.1 printed pp. 22–23; BK94 printed p. 126). -/
theorem simpleTypeTransport : SimpleTypeTransportStatement.{uF, uV, uW} := by
  intro F _ _ _ _ V _ _ _ ψF _ _ GV Lattice S₀
  refine ⟨?_, ?_, ?_⟩
  · intro W _ _ g J ρ gLin
    exact ⟨fun S q e θ h => isSimpleTypeDataOver_conj ψF g ρ S q e θ h,
      fun L e h => isLevelZeroSimpleTypeData_conj g ρ L e h⟩
  · intro L hL
    exact L.period_dvd_finrank_of_isPrincipalOrder hL
  · intro L₁ L₂ h₁ h₂ he
    exact LatticeChain.exists_order_eq_of_isPrincipalOrder L₁ L₂ h₁ h₂ he

end Langlands.BushnellKutzko
