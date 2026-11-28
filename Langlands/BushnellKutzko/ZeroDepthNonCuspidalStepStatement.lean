import Langlands.BushnellKutzko.SplitTypeExistenceSteps

/-! # The noncuspidal case of the depth-zero step of BK93 (8.1.5) (printed p. 269, (8.1.6)) -/

open ValuativeRel IsLocalRing

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uπ

set_option maxHeartbeats 1600000 in
/-- **BK93 (8.1.5), proof, printed p. 269, with Lemma (8.1.6).** Let `S = [𝔄, n, 0, β]` be a
simple stratum in `F^N`, `E = F[β]`, `𝓛_E` the `𝔬_E`-lattice chain of `𝔅 = 𝔄 ∩ End_E(F^N)`,
`θ ∈ C(𝔄, 0, β)`, `η` a representation of `J^1(β, 𝔄)` lying over `θ` and `κ` a `β`-extension
of `η`. Let `ξ` be a smooth representation of `J(β, 𝔄)`, trivial on `J^1(β, 𝔄)`, whose
restriction to `U(𝔅)` is equivalent to the inflation, along the layer reduction of `𝓛_E` in
bases `b` of the layers, of an external tensor product of irreducible representations `σ_i` of
the groups `GL(m_i, k_E)`, one of which is not cuspidal. If a smooth representation `π` of
`GL_N(F)` contains `κ ⊗ ξ` (through `toLin`), then `π` contains a simple character of a simple
stratum `[𝔄', n', 0, β']` whose lattice chain has a larger period than that of `S`. -/
def ZeroDepthNonCuspidalStepStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
      (S : Stratum 𝒪[F] F (Fin n → F)) (hS : S.IsSimple) (q : S.DefiningSequenceChoice),
    S.r = 0 →
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    haveI : FiniteDimensional F (Fin n → F) := S.chain.finiteDimensional
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    haveI := subfieldIntegers_isDiscreteValuationRing F E
    let L_E := S.chain.subfieldChain E hS.1.1.snd
    let J := simpleJ S.chain S.n S.b q.tail
    let J₁ := simpleJGroup S.chain S.n S.b q.tail 1
    let ι : L_E.unitFiltration 0 →* J :=
      (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)).comp
        (S.chain.relativeUnitFiltrationEquiv hS.1.1.snd (adjoin_elementGenerator S.b) 0).toMonoidHom
    let toGL : J →* GeneralLinear n F :=
      (Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom :
        (Module.End F (Fin n → F))ˣ →* GeneralLinear n F).comp J.subtype
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∀ (dη : ℕ) (η : Representation ℂ J₁ (Fin dη → ℂ)),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η →
    ∀ (dκ : ℕ) (κ : Representation ℂ J (Fin dκ → ℂ)),
      IsBetaExtension S.chain S.n S.b q.tail η κ →
    ∀ (dξ : ℕ) (ξ : Representation ℂ J (Fin dξ → ℂ)),
      IsSmoothRepresentation ξ →
      (∀ j : J, (j : (Module.End F (Fin n → F))ˣ) ∈ J₁ → ξ j = 1) →
    ∀ (rank dim : Fin L_E.period → ℕ)
      (b : ∀ i, Module.Basis (Fin (rank i)) (ResidueField (subfieldIntegers F E))
        (L_E.Layer (i : ℕ)))
      (σ : ∀ i, Representation ℂ (GeneralLinear (rank i) (ResidueField (subfieldIntegers F E)))
         (Fin (dim i) → ℂ)),
      (∀ i, (σ i).IsIrreducible) →
      Nonempty (Representation.Equiv (ξ.comp ι)
        (((PiTensorProduct.mapMonoidHom (R := ℂ) (s := fun i => Fin (dim i) → ℂ)).comp
            (MonoidHom.piMap σ)).comp (L_E.layerReduction b) :
          Representation ℂ (L_E.unitFiltration 0)
            (PiTensorProduct ℂ fun i => Fin (dim i) → ℂ))) →
      (∃ i, ¬ FiniteGeneralLinear.IsCuspidal (σ i)) →
      (∃ f : (κ.tprod ξ).IntertwiningMap (π.representation.comp toGL), f ≠ 0) →
      ∃ T : Stratum 𝒪[F] F (Fin n → F), T.r = 0 ∧
        S.chain.period < T.chain.period ∧ ContainsSimpleCharacter ψF π T

end Langlands.BushnellKutzko
