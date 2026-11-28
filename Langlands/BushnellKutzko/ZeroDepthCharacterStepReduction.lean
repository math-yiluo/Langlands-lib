import Langlands.BushnellKutzko.ZeroDepthCharacterStepConstruction
import Langlands.BushnellKutzko.SplitTypeExistenceSteps
import Langlands.BushnellKutzko.SubfieldLayerObstructions

/-! # The depth-zero step of BK93 (8.1.5), from the existence of `β`-extensions

`ZeroDepthCharacterStepReductionStatement` says that the depth-zero step
`ZeroDepthCharacterStepStatement` of BK93 (8.1.5) follows from the existence of `β`-extensions
(`BetaExtensionStatement`, BK93 (5.2.2)) and from the non-cuspidal case of the step
(`ZeroDepthNonCuspidalStepStatement`, BK93 p. 269 with Lemma (8.1.6)). The theorem
`zeroDepthCharacterStepReduction` proves it.
-/

open IsLocalRing Module ValuativeRel Representation

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uπ uρ

section Step

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ

set_option maxHeartbeats 1600000 in
/-- **One depth-zero step of BK93 (8.1.5) (printed pp. 268–270).** If `π` contains a simple
character of a simple stratum `S` with `S.r = 0`, then `π` contains a simple type or a split
type of level `(x, 0)`, or `π` contains a simple character of a simple stratum `T` with
`T.r = 0` and `e(𝔄_S) < e(𝔄_T)`. -/
theorem zeroDepth_step (hV2 : BetaExtensionStatement.{uF, uF, 0, 0, 0})
    (hNC : ZeroDepthNonCuspidalStepStatement.{uF, uπ})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (S : Stratum 𝒪[F] F (Fin n → F))
    (hr : S.r = 0) (hc : ContainsSimpleCharacter ψF π S) :
    (∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      (IsGLSimpleType (n := n) ψF ρ ∨
        ∃ x : ℚ, IsPositiveZeroSplitType (V := Fin n → F) ψF x (glRepresentationToAut ρ))) ∨
    ∃ T : Stratum 𝒪[F] F (Fin n → F), T.r = 0 ∧ S.chain.period < T.chain.period ∧
      ContainsSimpleCharacter ψF π T := by
  classical
  obtain ⟨hS, -, q, hθ'⟩ := hc
  rw [show S.r.toNat = 0 by simp [hr]] at hθ'
  obtain ⟨θ, hθ, hπθ⟩ := hθ'
  obtain ⟨dη, η, hη, dκ, κ, hκ, dξ, ξ, hξirr, hξ1, f, hf⟩ :=
    exists_beta_tensor_intertwining hV2 ψF hψ π S hr hS q θ hθ hπθ
  have hξsm : IsSmoothRepresentation ξ := by
    obtain ⟨k, hk⟩ := exists_unitFiltration_le_simpleJGroup S.chain S.n S.b q.tail 1
    exact ⟨S.chain, k, fun j hj => hξ1 j (hk hj)⟩
  have hsm : IsSmoothRepresentation (κ.tprod ξ) := isSmoothRepresentation_tprod hκ.2.1 hξsm
  have hirr : (κ.tprod ξ).IsIrreducible := by
    obtain ⟨e⟩ := hκ.2.2.1
    exact isIrreducible_tensor_of_irreducible_restriction
      (Subgroup.inclusion (simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail)) κ ξ
      (Clifford.isIrreducible_of_equiv e.symm hη.2.2.1) hξirr (fun h => hξ1 _ h.2)
  let E := elementAlgebra S.b
  let _ : Field E := hS.1.1.fst.toField
  have : FiniteDimensional F (Fin n → F) := S.chain.finiteDimensional
  have : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  have := subfieldIntegers_isDiscreteValuationRing F E
  let L_E := S.chain.subfieldChain E hS.1.1.snd
  let kE := ResidueField (subfieldIntegers F E)
  have : Finite kE := S.chain.finite_subfieldResidueField E
  let _ : Fintype kE := Fintype.ofFinite kE
  let e0 := S.chain.relativeUnitFiltrationEquiv hS.1.1.snd (adjoin_elementGenerator S.b) 0
  let ι : L_E.unitFiltration 0 →* simpleJ S.chain S.n S.b q.tail :=
    (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)).comp
      e0.toMonoidHom
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : Fin L_E.period → ℕ,
      Nonempty (∀ i, Module.Basis (Fin (d i)) kE (L_E.Layer (i : ℕ))) :=
    ⟨_, ⟨fun i => haveI := L_E.finite_layer ((i : ℕ) : ℤ)
      Module.finBasis kE (L_E.Layer (i : ℕ))⟩⟩
  have hι : ∀ g, ∃ x, ξ g = ξ (ι x) := by
    intro g
    obtain ⟨u, hu, k, hk, huk⟩ := exists_relativeUnit_mul_simpleJGroup_one S hr hS q g.2
    refine ⟨e0.symm ⟨u, hu⟩, ?_⟩
    have hιx : ι (e0.symm ⟨u, hu⟩) =
        ⟨u, relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail hu⟩ := by
      apply Subtype.ext
      change ((e0 (e0.symm ⟨u, hu⟩) : relativeUnitFiltration S.chain S.b 0) : Aut) = u
      rw [e0.apply_symm_apply]
    have hg : g = ⟨u, relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail hu⟩ *
        ⟨k, simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail hk⟩ := Subtype.ext huk.symm
    rw [hιx, hg, map_mul, hξ1 ⟨k, simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail hk⟩ hk,
      mul_one]
  have hker : ∀ h, L_E.layerReduction b h = 1 → ξ (ι h) = 1 := by
    intro h hh
    have h1 := L_E.mem_unitFiltration_one_of_layerReduction_eq_one b h hh
    have h2 := ((S.chain.relativeUnitFiltrationEquiv hS.1.1.snd
      (adjoin_elementGenerator S.b) 1) ⟨h.1, h1⟩).2
    exact hξ1 (ι h) (relativeUnitFiltration_le_simpleJGroup S.chain S.n S.b q.tail 1 h2)
  obtain ⟨a, ⟨Φ⟩⟩ := exists_equiv_classTensor_comp ξ hξirr ι hι (L_E.layerReduction b)
    (L_E.layerReduction_surjective b) hker
  by_cases hcusp : ∀ i, FiniteGeneralLinear.IsCuspidal (FiniteRep.VirtualCharacter.rep (a i)).ρ
  swap
  · push Not at hcusp
    obtain ⟨i, hi⟩ := hcusp
    exact Or.inr (hNC F n ψF hψ π S hS q hr θ hθ dη η hη dκ κ hκ dξ ξ hξsm hξ1 d
      (fun i => finrank ℂ (FiniteRep.VirtualCharacter.rep (a i))) b
      (fun i => Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep (a i)).ρ)
      (fun i => isIrreducible_coordinateRep_rep (a i)) ⟨Φ⟩
      ⟨i, fun h => hi (h.of_equiv (Clifford.coordinateEquiv _).symm)⟩ ⟨f, hf⟩)
  left
  have hpair := isPairIsomorphic_matrixSmoothRep.{uF, uρ} (κ.tprod ξ) hsm
  refine ⟨matrixSubgroup (simpleJ S.chain S.n S.b q.tail),
    matrixSmoothRep.{uF, uρ} (κ.tprod ξ) hsm, containsType_matrixSmoothRep π hsm f hf, ?_⟩
  by_cases hdiff : ∃ i j, (L_E.classCuspidalData b a hcusp).factorClass i ≠
      (L_E.classCuspidalData b a hcusp).factorClass j
  · have Φ₂ : Nonempty (Representation.Equiv (ξ.comp ι)
        (L_E.classCuspidalData b a hcusp).inflation) := by
      rw [L_E.classCuspidalData_inflation b a hcusp]
      exact ⟨Φ⟩
    exact Or.inr ⟨(S.n : ℚ) / S.chain.period, hψ, hpair.isIrreducible hirr, S, q, hS, hr, rfl,
      θ, hθ, dη, η, hη, dκ, κ, hκ, dξ, ξ, L_E.classCuspidalData b a hcusp, hξsm, hξ1, hdiff,
      Φ₂, hpair⟩
  push Not at hdiff
  let i₀ : Fin L_E.period := ⟨0, L_E.period_pos⟩
  obtain ⟨r, rfl⟩ : ∃ r, d = fun _ => r :=
    ⟨d i₀, funext fun i => congrArg Sigma.fst (hdiff i i₀)⟩
  have ha : ∀ i, a i = a i₀ := by
    intro i
    have h3 := eq_of_heq (Sigma.ext_iff.mp (hdiff i i₀)).2
    obtain ⟨E'⟩ := (FiniteGeneralLinear.CuspidalRep.isoClass_eq_iff _ _).mp h3
    let E'' : Representation.Equiv (FiniteRep.VirtualCharacter.rep (a i)).ρ
        (FiniteRep.VirtualCharacter.rep (a i₀)).ρ :=
      (Clifford.coordinateEquiv _).trans (E'.trans (Clifford.coordinateEquiv _).symm)
    have hc : FiniteRep.classOf (FiniteRep.VirtualCharacter.rep (a i)) =
        FiniteRep.classOf (FiniteRep.VirtualCharacter.rep (a i₀)) :=
      (FiniteRep.classOf_eq_iff _ _).mpr ⟨FiniteRep.isoOfEquiv E''⟩
    rw [FiniteRep.VirtualCharacter.classOf_rep, FiniteRep.VirtualCharacter.classOf_rep] at hc
    exact Subtype.ext hc
  obtain ⟨c, rfl⟩ : ∃ c, a = fun _ => c := ⟨a i₀, funext ha⟩
  have hrel : ∀ j : ℤ,
      (S.chain.lattice (j + 1)).toAddSubgroup.relIndex (S.chain.lattice j).toAddSubgroup =
        Nat.card (Fin r → kE) := fun j => L_E.relIndex_eq_of_bases b j
  have hιe : ∀ u, ι (e0.symm u) =
      Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail) u := by
    intro u
    apply Subtype.ext
    change ((e0 (e0.symm u) : relativeUnitFiltration S.chain S.b 0) : Aut) = (u : Aut)
    rw [e0.apply_symm_apply]
  have hΦ := nonempty_equiv_tensorPower_comp ξ ι e0
    (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)) hιe c
    (L_E.layerReduction b) Φ
  have hε : ∀ (u : relativeUnitFiltration S.chain S.b 0) (v : Fin n → F),
      (((e0.symm.toMonoidHom u : L_E.unitFiltration 0) : (Module.End E (Fin n → F))ˣ) :
        Module.End E (Fin n → F)) v = ((u : Aut) : Module.End F (Fin n → F)) v :=
    fun u v => congrArg (fun z : relativeUnitFiltration S.chain S.b 0 =>
      ((z : Aut) : Module.End F (Fin n → F)) v) (e0.apply_symm_apply u)
  exact Or.inl (Or.inl ⟨S, q, L_E.period, hψ, hr, ⟨S.chain, rfl, fun i j => by rw [hrel, hrel]⟩,
    hS, rfl, θ, hθ, dη, η, hη, dκ, κ, hκ, r, finrank ℂ (FiniteRep.VirtualCharacter.rep c),
    Clifford.coordinateRep (FiniteRep.VirtualCharacter.rep c).ρ, isIrreducible_coordinateRep_rep c,
    (hcusp i₀).of_equiv (Clifford.coordinateEquiv _), b,
    (L_E.layerReduction b).comp e0.symm.toMonoidHom,
    L_E.isLayerReduction_comp _ _ b e0.symm.toMonoidHom hε, dξ, ξ, hξsm, hξ1, hΦ, hpair⟩)

end Step

/-- **BK93 (8.1.5), depth zero, from the existence of `β`-extensions (printed pp. 268–270).**
The existence of `β`-extensions (BK93 (5.2.2)) and the non-cuspidal case of the depth-zero step
(BK93 p. 269 with Lemma (8.1.6)) imply the depth-zero step of BK93 (8.1.5): an irreducible smooth
representation of `GL_N(F)` containing a simple character `θ ∈ C(𝔄, 0, β)` of a simple stratum
`[𝔄, n, 0, β]` contains a simple type or a split type of level `(x, 0)`. -/
def ZeroDepthCharacterStepReductionStatement : Prop :=
  BetaExtensionStatement.{uF, uF, 0, 0, 0} →
    ZeroDepthNonCuspidalStepStatement.{uF, uπ} →
    ZeroDepthCharacterStepStatement.{uF, uπ, uρ}

/-- The depth-zero step of BK93 (8.1.5) follows from the existence of `β`-extensions and from
its non-cuspidal case. -/
theorem zeroDepthCharacterStepReduction :
    ZeroDepthCharacterStepReductionStatement.{uF, uπ, uρ} := by
  intro hV2 hNC F _ _ _ _ n _ ψF hψ π _ S hr hc
  suffices H : ∀ (m : ℕ) (S : Stratum 𝒪[F] F (Fin n → F)), n - S.chain.period = m →
      S.r = 0 → ContainsSimpleCharacter ψF π S →
      ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
        (IsGLSimpleType (n := n) ψF ρ ∨
          ∃ x : ℚ, IsPositiveZeroSplitType (V := Fin n → F) ψF x (glRepresentationToAut ρ)) from
    H _ S rfl hr hc
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hm hr hc
    rcases zeroDepth_step hV2 hNC ψF hψ π S hr hc with h | ⟨T, hTr, hlt, hT⟩
    · exact h
    · have hT' : T.chain.period ≤ n := by simpa using T.chain.period_le_card
      exact ih (n - T.chain.period) (by omega) T rfl hTr hT

end Langlands.BushnellKutzko
