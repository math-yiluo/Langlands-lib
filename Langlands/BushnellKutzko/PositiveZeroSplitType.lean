import Langlands.BushnellKutzko.AdjointCentralizer
import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.LevelZeroSplitType
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.SubfieldLatticeChain

/-! # Split types of level `(x, 0)` for `x > 0` -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

section CentralizerUnits

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_relativeEnd_of_commute {β : E}
    (hβ : Algebra.adjoin F ({β} : Set E) = ⊤) {x : Module.End F V}
    (hx : Commute (subfieldEmbedding F E V β) x) :
    ∃ y : Module.End E V, y.restrictScalars F = x := by
  have hk : x ∈ (adjointMap F (subfieldEmbedding F E V β)).ker :=
    LinearMap.mem_ker.mpr (sub_eq_zero.mpr hx.eq)
  rwa [ker_adjointMap_eq_range_restrictScalars β hβ, LinearMap.mem_range] at hk

/-- Restriction of scalars identifies `U^m(𝔅)` on the centralizer chain with the
subgroup of `U^m(𝔄)` commuting with a field generator. -/
def LatticeChain.relativeUnitFiltrationEquiv (L : LatticeChain 𝒪[F] F V)
    [FiniteDimensional F E] (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    {β : E} (hβ : Algebra.adjoin F ({β} : Set E) = ⊤) (m : ℕ) :
    (L.subfieldChain E hE).unitFiltration m ≃*
      relativeUnitFiltration L (subfieldEmbedding F E V β) m := by
  let U := (L.subfieldChain E hE).unitFiltration m
  let U_F := relativeUnitFiltration L (subfieldEmbedding F E V β) m
  let ι := (relativeEndUnits (F := F) (V := V) E).comp U.subtype
  let f : U →* U_F := ι.codRestrict U_F fun g => by
    refine ⟨?_, g.property⟩
    show Commute (subfieldEmbedding F E V β) ((g.1 : Module.End E V).restrictScalars F)
    apply LinearMap.ext
    intro v
    exact ((g.1 : Module.End E V).map_smul β v).symm
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro g h heq
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.restrictScalars_injective F
    exact congrArg (fun z : U_F => ((z.1 : (Module.End F V)ˣ) : Module.End F V)) heq
  · intro g
    obtain ⟨y, hy⟩ := exists_relativeEnd_of_commute hβ g.2.1
    obtain ⟨z, hz⟩ := exists_relativeEnd_of_commute hβ (U_F.inv_mem g.2).1
    have hyz : y * z = 1 := by
      apply LinearMap.restrictScalars_injective F
      change y.restrictScalars F * z.restrictScalars F = 1
      rw [hy, hz, Units.mul_inv]
    have hzy : z * y = 1 := by
      apply LinearMap.restrictScalars_injective F
      change z.restrictScalars F * y.restrictScalars F = 1
      rw [hy, hz, Units.inv_mul]
    let u : (Module.End E V)ˣ := ⟨y, z, hyz, hzy⟩
    have hu : relativeEndUnits (F := F) E u = g.1 := Units.ext hy
    have hU : u ∈ U := by
      change relativeEndUnits (F := F) E u ∈ L.unitFiltration m
      rw [hu]
      exact g.2.2
    exact ⟨⟨u, hU⟩, Subtype.ext hu⟩

end CentralizerUnits

/-- **BK93 (8.1.4).** A split type of level `(x,0)` with `x > 0` is a pair on `J(β,𝔄)`
of the form `κ ⊗ ξ`. Here `κ` is a `β`-extension attached to a simple character, and `ξ`
is trivial on `J^1` and has inhomogeneous cuspidal factors on `U(𝔅)`. -/
def IsPositiveZeroSplitType {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {K : Subgroup (Module.End F V)ˣ} (ψF : AddChar F ℂ) (x : ℚ)
    (ρ : Representation ℂ K W) : Prop :=
  IsBKAdditiveCharacter ψF ∧ ρ.IsIrreducible ∧
  ∃ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (hS : S.IsSimple),
    S.r = 0 ∧ x = (S.n : ℚ) / S.chain.period ∧
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    haveI : FiniteDimensional F V := S.chain.finiteDimensional
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    haveI := subfieldIntegers_isDiscreteValuationRing F E
    let L_E := S.chain.subfieldChain E hS.1.1.snd
    let J := simpleJ S.chain S.n S.b q.tail
    let J₁ := simpleJGroup S.chain S.n S.b q.tail 1
    let ι : L_E.unitFiltration 0 →* J :=
      (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)).comp
        (S.chain.relativeUnitFiltrationEquiv hS.1.1.snd (adjoin_elementGenerator S.b) 0).toMonoidHom
    ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∃ (dη : ℕ) (η : Representation ℂ J₁ (Fin dη → ℂ)),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η ∧
    ∃ (dκ : ℕ) (κ : Representation ℂ J (Fin dκ → ℂ)),
      IsBetaExtension S.chain S.n S.b q.tail η κ ∧
    ∃ (dξ : ℕ) (ξ : Representation ℂ J (Fin dξ → ℂ)) (a : L_E.CuspidalLayerData),
      IsSmoothRepresentation ξ ∧
      (∀ j : J, (j : (Module.End F V)ˣ) ∈ J₁ → ξ j = 1) ∧
      (∃ i j, a.factorClass i ≠ a.factorClass j) ∧
      Nonempty (Representation.Equiv (ξ.comp ι) a.inflation) ∧
      IsPairIsomorphic ρ (κ.tprod ξ)

end Langlands.BushnellKutzko
