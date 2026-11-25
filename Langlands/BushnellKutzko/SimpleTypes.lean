import Langlands.BushnellKutzko.PairConjugation
import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.SubfieldChainLayers
import Langlands.Representation.FiniteGeneralLinear.Cuspidal

/-! # Simple types and maximal simple types (BK93 (5.5.10), printed pp. 184–185; p. 204) -/

open ValuativeRel IsLocalRing

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uF uV uW uH

section Generic

/-- The representation `σ₀ ⊗ ⋯ ⊗ σ₀` (`e` factors) of the product group `H^e`. -/
def tensorPowerRepresentation {H : Type uH} [Group H] {W : Type uW} [AddCommGroup W]
    [Module ℂ W] (σ₀ : Representation ℂ H W) (e : ℕ) :
    Representation ℂ (Fin e → H) (PiTensorProduct ℂ fun _ : Fin e => W) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.piMap fun _ : Fin e => σ₀)

variable {O : Type uO} {K : Type uK} {F : Type uF} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [Field F] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  [Module F V]

/-- An element of `U^m(𝔄)` maps every lattice `L_i` of the chain into itself. -/
theorem LatticeChain.apply_mem_lattice_of_mem_unitFiltration (L : LatticeChain O K V) {m : ℕ}
    {u : (Module.End K V)ˣ} (hu : u ∈ L.unitFiltration m) (i : ℤ) {v : V}
    (hv : v ∈ L.lattice i) : (u : Module.End K V) v ∈ L.lattice i :=
  L.mem_order.1 hu.1 i v hv

variable [IsLocalRing O]

/-- `φ` is the reduction map of the subgroup `U` given by its action on the layers
`L_i / L_{i+1}`, `0 ≤ i < e`, of the chain, written as matrices in the residue-field bases
`b i`: for `u ∈ U`, the `i`-th component of `φ u` is the matrix of `u` acting on
`L_i / L_{i+1}` in the basis `b i`. -/
def IsLayerReduction (L : LatticeChain O K V) (U : Subgroup (Module.End F V)ˣ)
    (hU : ∀ u ∈ U, ∀ (i : ℤ) (v : V), v ∈ L.lattice i → (u : Module.End F V) v ∈ L.lattice i)
    {e f : ℕ} (b : ∀ i : Fin e, Module.Basis (Fin f) (ResidueField O) (L.Layer ((i : ℕ) : ℤ)))
    (φ : U →* (Fin e → GeneralLinear f (ResidueField O))) : Prop :=
  ∀ (u : U) (i : Fin e) (v : V) (hv : v ∈ L.lattice ((i : ℕ) : ℤ)),
    (b i).equivFun
        (L.intervalMk _ _ (((u : (Module.End F V)ˣ) : Module.End F V) v) (hU u u.2 _ v hv)) =
      Matrix.mulVec
        ((φ u i : GeneralLinear f (ResidueField O)) : Matrix (Fin f) (Fin f) (ResidueField O))
        ((b i).equivFun (L.intervalMk _ _ v hv))

end Generic

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "G" => (Module.End F V)ˣ

/-- **BK93 (5.5.10)(a).** `(J, ρ)` is a simple type of kind (a) exhibited by the simple stratum
`S = [𝔄, n, 0, β]` with principal `𝔄`, the defining-sequence choice `q`, and
`e = e(𝔅_β | 𝔬_E)`: for `E = F[β]` and `𝓛_E` the `𝔬_E`-lattice chain of `𝔅_β`, there are
`θ ∈ C(𝔄, 0, β)`, a representation `η` of `J^1(β, 𝔄)` lying over `θ`, a `β`-extension `κ`
of `η`, an irreducible cuspidal representation `σ₀` of `GL_f(k_E)`, bases of the layers
of `𝓛_E` with the corresponding reduction `φ : U(𝔅_β) → GL_f(k_E)^e`, and a smooth
representation `σ` of `J(β, 𝔄)`, trivial on `J^1(β, 𝔄)` and restricting on `U(𝔅_β)` to the
inflation of `σ₀ ⊗ ⋯ ⊗ σ₀` along `φ`, such that `(J, ρ) ≅ (J(β, 𝔄), κ ⊗ σ)`. The character
`ψF` must have the conductor of BK93 §1.1 (`IsBKAdditiveCharacter ψF`). -/
def IsSimpleTypeData (ψF : AddChar F ℂ) (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice)
    (e : ℕ) {J : Subgroup G} (ρ : Representation ℂ J W) : Prop :=
  IsBKAdditiveCharacter ψF ∧ S.r = 0 ∧ IsPrincipalOrder S.chain.order ∧ ∃ hS : S.IsSimple,
    letI := hS.1.1.fst.toField
    haveI : FiniteDimensional F (elementAlgebra S.b) :=
      S.chain.finiteDimensional_subfield (elementAlgebra S.b)
    haveI := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b)
    let 𝓛E := S.chain.subfieldChain (elementAlgebra S.b) hS.1.1.snd
    let kE := ResidueField (subfieldIntegers F (elementAlgebra S.b))
    let U := relativeUnitFiltration S.chain S.b 0
    e = 𝓛E.period ∧
    ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∃ (dη : ℕ) (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) (Fin dη → ℂ)),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η ∧
    ∃ (dκ : ℕ) (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin dκ → ℂ)),
      IsBetaExtension S.chain S.n S.b q.tail η κ ∧
    ∃ (f d : ℕ) (σ₀ : Representation ℂ (GeneralLinear f kE) (Fin d → ℂ)),
      σ₀.IsIrreducible ∧ FiniteGeneralLinear.IsCuspidal σ₀ ∧
    ∃ (b : ∀ i : Fin e, Module.Basis (Fin f) kE (𝓛E.Layer ((i : ℕ) : ℤ)))
      (φ : U →* (Fin e → GeneralLinear f kE)),
      IsLayerReduction 𝓛E U (fun _ hu i _ hv => S.chain.apply_mem_lattice_of_mem_unitFiltration
        hu.2 i hv) b φ ∧
    ∃ (dσ : ℕ) (σ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin dσ → ℂ)),
      IsSmoothRepresentation σ ∧
      (∀ j : simpleJ S.chain S.n S.b q.tail,
        (j : G) ∈ simpleJGroup S.chain S.n S.b q.tail 1 → σ j = 1) ∧
      Nonempty (Representation.Equiv
        (σ.comp (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)))
        ((tensorPowerRepresentation σ₀ e).comp φ)) ∧
      IsPairIsomorphic ρ (κ.tprod σ)

/-- **BK93 (5.5.10)(b).** `(J, ρ)` is a simple type of kind (b) (level zero) exhibited by the
lattice chain `L` of a principal order `𝔄` with `e = e(𝔄 | 𝔬_F)`: there are an irreducible
cuspidal representation `σ₀` of `GL_f(k_F)` and bases of the layers of `L`, with the
corresponding reduction `φ : U(𝔄) → GL_f(k_F)^e`, such that `ρ` is trivial on `U^1(𝔄)` and
`(J, ρ) ≅ (U(𝔄), (σ₀ ⊗ ⋯ ⊗ σ₀) ∘ φ)`. -/
def IsLevelZeroSimpleTypeData (L : LatticeChain 𝒪[F] F V) (e : ℕ) {J : Subgroup G}
    (ρ : Representation ℂ J W) : Prop :=
  IsPrincipalOrder L.order ∧ e = L.period ∧
    ∃ (f d : ℕ) (σ₀ : Representation ℂ (GeneralLinear f (ResidueField 𝒪[F])) (Fin d → ℂ)),
      σ₀.IsIrreducible ∧ FiniteGeneralLinear.IsCuspidal σ₀ ∧
    ∃ (b : ∀ i : Fin e, Module.Basis (Fin f) (ResidueField 𝒪[F]) (L.Layer ((i : ℕ) : ℤ)))
      (φ : L.unitFiltration 0 →* (Fin e → GeneralLinear f (ResidueField 𝒪[F]))),
      IsLayerReduction L (L.unitFiltration 0)
        (fun _ hu i _ hv => L.apply_mem_lattice_of_mem_unitFiltration hu i hv) b φ ∧
      (∀ j : J, (j : G) ∈ L.unitFiltration 1 → ρ j = 1) ∧
      IsPairIsomorphic ρ ((tensorPowerRepresentation σ₀ e).comp φ)

/-- **BK93 (5.5.10).** A simple type in `G`: a pair `(J, ρ)` of kind (a) or of kind (b). -/
def IsSimpleType (ψF : AddChar F ℂ) {J : Subgroup G} (ρ : Representation ℂ J W) : Prop :=
  (∃ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (e : ℕ),
      IsSimpleTypeData ψF S q e ρ) ∨
    ∃ (L : LatticeChain 𝒪[F] F V) (e : ℕ), IsLevelZeroSimpleTypeData L e ρ

/-- **BK93 p. 204.** A maximal simple type: a simple type exhibited by data of kind (a) with
`e(𝔅_β | 𝔬_E) = 1`, or by data of kind (b) with `e(𝔄 | 𝔬_F) = 1`. -/
def IsMaximalSimpleType (ψF : AddChar F ℂ) {J : Subgroup G} (ρ : Representation ℂ J W) :
    Prop :=
  (∃ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice), IsSimpleTypeData ψF S q 1 ρ) ∨
    ∃ L : LatticeChain 𝒪[F] F V, IsLevelZeroSimpleTypeData L 1 ρ

end Langlands.BushnellKutzko
