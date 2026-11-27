import Langlands.BushnellKutzko.SimpleCharacterCriticalTranslationStatement
import Langlands.BushnellKutzko.SimpleCharacterResidueComparisonStatement
import Langlands.BushnellKutzko.SimpleCharacterLoweringStatement
import Langlands.BushnellKutzko.SimpleCharacterPairsReindex
import Langlands.BushnellKutzko.NonsplitFundamentalSimpleStatement
import Langlands.BushnellKutzko.DerivedStratumComparison
import Langlands.BushnellKutzko.CriticalDerivedStratumProof
import Langlands.BushnellKutzko.StratumEquivalenceProof
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.CorestrictionChains
import Langlands.BushnellKutzko.PureStratumApproximationChainImprovement
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences
import Langlands.BushnellKutzko.PureStratumApproximationImprovementSteps

/-! # Reduction of the critical translation (BK94 (5.3)–(5.6), printed pp. 132–133) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

/-- The residue comparison of BK94 (5.2), the lowering theorem BK93 (3.5.9) and the
semisimplicity criterion BK93 (2.4.13) imply the critical translation. -/
def SimpleCharacterCriticalTranslationReductionStatement : Prop :=
  SimpleCharacterResidueComparisonStatement.{uF, uV} →
  SimpleCharacterLoweringStatement.{uF, uV} →
  NonsplitFundamentalSimpleStatement.{uF, uV, uV} →
  SimpleCharacterCriticalTranslationStatement.{uF, uV}

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- Lowering a pair of strata with equal depth-`j` pairs to depth zero, changing the first
element only modulo `𝔓^{−j}` and keeping its critical exponent. -/
theorem exists_depthZero_of_pairs_eq [FiniteDimensional F V]
    (hLow : SimpleCharacterLoweringStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (n : ℤ) :
    ∀ (j : ℕ) (S T : SimpleStratumAt L n j),
      simpleCharacterPairs ψF S.1 j = simpleCharacterPairs ψF T.1 j →
      ∃ R : SimpleStratumAt L n 0, R.1.b - S.1.b ∈ L.endFiltration (-(j : ℤ)) ∧
        criticalExponent L R.1.b = criticalExponent L S.1.b ∧
        simpleCharacterPairs ψF R.1 0 = simpleCharacterPairs ψF T.1 0 := by
  intro j
  induction j with
  | zero =>
    intro S T h
    exact ⟨S, by simp, rfl, h⟩
  | succ j ih =>
    intro S T h
    obtain ⟨-, S', hS'eq, hS'C⟩ := hLow F V ψF hψ L n (j + 1) (by omega) S T h
    rw [Nat.add_sub_cancel] at hS'C
    have hrS' : ((j : ℕ) : ℤ) ≤ S'.1.r := by rw [S'.2.2.2.1]; push_cast; omega
    have hrT : ((j : ℕ) : ℤ) ≤ T.1.r := by rw [T.2.2.2.1]; push_cast; omega
    let S'' : SimpleStratumAt L n j :=
      ⟨S'.1.lowerIndex j hrS', S'.2.1, S'.2.2.1, rfl, S'.2.2.2.2.lowerIndex hrS'⟩
    let T'' : SimpleStratumAt L n j :=
      ⟨T.1.lowerIndex j hrT, T.2.1, T.2.2.1, rfl, T.2.2.2.2.lowerIndex hrT⟩
    have hC'' : simpleCharacterPairs ψF S''.1 j = simpleCharacterPairs ψF T''.1 j := by
      rw [simpleCharacterPairs_congr ψF (S := S'.1) (S' := S''.1) rfl rfl rfl S'.2.2.2.2
          S''.2.2.2.2 j, hS'C,
        simpleCharacterPairs_congr ψF (S := T.1) (S' := T''.1) rfl rfl rfl T.2.2.2.2
          T''.2.2.2.2 j]
    obtain ⟨R, hR, hRk, hRC⟩ := ih S'' T'' hC''
    have hE := stratumEquivalence F V S'.1 S.1 hS'eq
    refine ⟨R, ?_, ?_, ?_⟩
    · have h1 := Stratum.sub_mem_of_equivalent hS'eq
      rw [S'.2.1, S'.2.2.2.1] at h1
      rw [show R.1.b - S.1.b = (R.1.b - S''.1.b) + (S'.1.b - S.1.b) by
        change R.1.b - S.1.b = (R.1.b - S'.1.b) + (S'.1.b - S.1.b)
        abel]
      exact add_mem (L.endFiltration_antitone (by push_cast; omega) hR) h1
    · have hk := (hE.2.2.2 S'.2.2.2.2 S.2.2.2.2).2.1
      rw [S'.2.1, S.2.1] at hk
      rw [hRk]
      exact hk
    · rw [hRC]
      exact simpleCharacterPairs_congr ψF (S := T.1) (S' := T''.1) rfl rfl rfl T.2.2.2.2
        T''.2.2.2.2 0

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The residue ring `𝔄/𝔓` of a lattice chain is nontrivial. -/
theorem LatticeChain.nontrivial_residue (L : LatticeChain 𝒪[F] F V) :
    Nontrivial (L.order ⧸ L.firstFiltrationIdeal) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h1 : (1 : L.order) ∈ L.firstFiltrationIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact h
  have h2 : ((1 : L.order) : Module.End F V) ∈ L.endFiltration 1 := h1
  have hle : L.lattice 0 ≤ L.lattice 1 := by
    intro v hv
    simpa using h2 0 v hv
  exact lt_irrefl _ (lt_of_le_of_lt hle (L.lattice_succ_lt 0))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem restrictScalars_algebraMap_order {E : Type uV} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (C : LatticeChain (subfieldIntegers F E) E V)
    (o : subfieldIntegers F E) :
    ((algebraMap (subfieldIntegers F E) C.order o : C.order) : Module.End E V).restrictScalars F =
      subfieldEmbedding F E V (o : E) := by
  ext v
  rfl

/-- A derived stratum over an extension field is nonsplit fundamental if, at the level of `F`,
its element is congruent to an endomorphism shifting the chain by `−n`, and its scalars and its
element `y_b` reduce into the residue image of a subring whose nonzero elements lie in `𝔎(𝔄)`. -/
theorem derived_isNonsplit {E : Type uV} [Field E] [Algebra F E] [FiniteDimensional F E]
    [Module E V] [IsScalarTower F E V] (L : LatticeChain 𝒪[F] F V)
    (D : Stratum (subfieldIntegers F E) E V)
    (hlat : ∀ i, (D.chain.lattice i : Set V) = L.lattice i)
    (hr : D.r = D.n - 1) (hn : 0 ≤ D.n) (hb : D.b ∈ D.chain.endFiltration (-D.n))
    {g : Module.End F V} (hg : ∀ i (v : V), g v ∈ L.lattice (i + -D.n) ↔ v ∈ L.lattice i)
    (hcoset : D.b.restrictScalars F - g ∈ L.endFiltration (1 - D.n))
    (π : RingPrimeElement (subfieldIntegers F E)) (R : Subring (Module.End F V))
    (hR : ∀ x ∈ R, x ≠ 0 → ∃ u ∈ L.stabilizer, (u : Module.End F V) = x)
    (hscal : ∀ o : subfieldIntegers F E, ∃ x ∈ R, x ∈ L.order ∧
      subfieldEmbedding F E V (o : E) - x ∈ L.endFiltration 1)
    (hy : ∃ x ∈ R, x ∈ L.order ∧
      (D.fundamentalElement π).restrictScalars F - x ∈ L.endFiltration 1) :
    D.IsNonsplit := by
  let := subfieldIntegers_isDiscreteValuationRing F E
  let := subfieldIntegers_isFractionRing F E
  have : FiniteDimensional E V := D.chain.finiteDimensional
  have : Nontrivial (L.order ⧸ L.firstFiltrationIdeal) := L.nontrivial_residue
  have hfund : D.IsFundamental := by
    refine ⟨hr, fun x hx hnil => ?_⟩
    have hx' : x - D.b ∈ D.chain.endFiltration (-D.r) := hx
    rw [mem_endFiltration_restrictScalars hlat, hr, show -(D.n - 1) = 1 - D.n by ring] at hx'
    have hX : x.restrictScalars F - g ∈ L.endFiltration (-(D.n - 1)) := by
      have h := add_mem hx' hcoset
      rw [show 1 - D.n = -(D.n - 1) by ring] at h
      convert h using 1
      change x.restrictScalars F - g =
        (x.restrictScalars F - D.b.restrictScalars F) + (D.b.restrictScalars F - g)
      abel
    exact L.not_isNilpotent_of_shift hg hX (PureApproximation.isNilpotent_restrictScalars hnil)
  let f : D.chain.order →+* L.order ⧸ L.firstFiltrationIdeal := residueRestrict (L := L) hlat
  have hf : ∀ x, f x = 0 ↔ x ∈ D.chain.firstFiltrationIdeal :=
    residueRestrict_eq_zero_iff (L := L) hlat
  have hfeq : ∀ (x : D.chain.order) (y : L.order),
      (x : Module.End E V).restrictScalars F - (y : Module.End F V) ∈ L.endFiltration 1 →
        Ideal.Quotient.mk L.firstFiltrationIdeal y = f x :=
    fun x y h => ((residueRestrict_eq_iff (L := L) hlat x y).mpr h).symm
  refine Stratum.isNonsplit_of_residue_domain D hfund π
    (Stratum.fundamentalElement_mem_order D π hn hb) f hf
    ((R.comap L.order.val.toRingHom).map (Ideal.Quotient.mk L.firstFiltrationIdeal))
    (L.residue_mul_eq_zero hR) (fun o => ?_) ?_
  · obtain ⟨x, hxR, hxo, hdiff⟩ := hscal o
    refine ⟨⟨x, hxo⟩, hxR, hfeq _ _ ?_⟩
    rw [restrictScalars_algebraMap_order]
    exact hdiff
  · obtain ⟨x, hxR, hxo, hdiff⟩ := hy
    exact ⟨⟨x, hxo⟩, hxR, hfeq _ _ hdiff⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The residue data of a simple stratum `[𝔅,n,r,α]` over an extension field `E`, with the
lattices of `L`: the image of `E[α]` in `End_F(V)` has its nonzero elements in `𝔎(𝔄)`, the
element `α` shifts the chain by `−n`, and the integers of `E` and the elements `y_α` lie in this
image and in `𝔄`. -/
theorem simple_residue_data {E : Type uV} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (L : LatticeChain 𝒪[F] F V) (C : Stratum (subfieldIntegers F E) E V)
    (hlat : ∀ i, (C.chain.lattice i : Set V) = L.lattice i) (hC : C.IsSimple) (hn : 0 ≤ C.n) :
    ∃ R : Subring (Module.End F V),
      (∀ x ∈ R, x ≠ 0 → ∃ u ∈ L.stabilizer, (u : Module.End F V) = x) ∧
      (∀ i (v : V), C.b.restrictScalars F v ∈ L.lattice (i + -C.n) ↔ v ∈ L.lattice i) ∧
      (∀ o : subfieldIntegers F E,
        subfieldEmbedding F E V (o : E) ∈ R ∧ subfieldEmbedding F E V (o : E) ∈ L.order) ∧
      (∀ π : RingPrimeElement (subfieldIntegers F E),
        (C.fundamentalElement π).restrictScalars F ∈ R ∧
          (C.fundamentalElement π).restrictScalars F ∈ L.order) := by
  obtain ⟨⟨⟨hfield, hnorm⟩, hval⟩, -⟩ := hC
  let := hfield.toField
  let K := elementAlgebra C.b
  let ρ : Module.End E V →+* Module.End F V :=
    { toFun := fun f => f.restrictScalars F
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hunit : ∀ u : Kˣ, ((restrictUnit (subfieldUnits E K V u) : (Module.End F V)ˣ) :
      Module.End F V) = ρ ((u : K) : Module.End E V) := fun u => by
    ext v
    rfl
  have hα : C.b ∈ K := Algebra.self_mem_adjoin_singleton E C.b
  have hshift : ∀ i (v : V), C.b.restrictScalars F v ∈ L.lattice (i + -C.n) ↔
      v ∈ L.lattice i := by
    have hα0 : (⟨C.b, hα⟩ : K) ≠ 0 := by
      intro h
      have hb0 : C.b = 0 := congrArg Subtype.val h
      rw [hb0, LatticeChain.valuation_zero] at hval
      exact WithTop.top_ne_coe hval
    let u : Kˣ := Units.mk0 _ hα0
    let g : C.chain.stabilizer := ⟨subfieldUnits E K V u, hnorm u⟩
    have hg : (((g : (Module.End E V)ˣ)) : Module.End E V) = C.b := by
      ext v
      rfl
    have hd : C.chain.stabilizerValuation g = -C.n := by
      have h := C.chain.valuation_eq_shift g
      rw [hg, hval] at h
      exact (WithTop.coe_injective h).symm
    intro i v
    rw [← SetLike.mem_coe, ← hlat, ← SetLike.mem_coe (x := v), ← hlat, SetLike.mem_coe,
      SetLike.mem_coe, ← hd, ← C.chain.map_lattice_stabilizer g i]
    constructor
    · rintro ⟨w, hw, hwv⟩
      have hinj : Function.Injective ((g : (Module.End E V)ˣ) : Module.End E V) := by
        intro a b hab
        have h := congrArg (fun x => ((g⁻¹ : (Module.End E V)ˣ) : Module.End E V) x) hab
        simpa [← Module.End.mul_apply] using h
      have hwv' : w = v := hinj (by rw [hg]; exact hwv)
      exact hwv' ▸ hw
    · intro hv
      refine ⟨v, hv, ?_⟩
      change ((g : (Module.End E V)ˣ) : Module.End E V) v = C.b v
      rw [hg]
  have hb : C.b ∈ C.chain.endFiltration (-C.n) := by
    intro i v hv
    rw [← SetLike.mem_coe, hlat] at hv ⊢
    exact (hshift i v).mpr hv
  refine ⟨K.toSubring.map ρ, ?_, hshift, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ hz0
    have hzK : (⟨z, hz⟩ : K) ≠ 0 := fun h => hz0 (by
      have : z = 0 := congrArg Subtype.val h
      rw [this, map_zero])
    let u : Kˣ := Units.mk0 _ hzK
    exact ⟨_, restrictUnit_mem_stabilizer hlat (hnorm u), hunit u⟩
  · intro o
    refine ⟨⟨algebraMap E (Module.End E V) (o : E), Subalgebra.algebraMap_mem K _, ?_⟩, ?_⟩
    · ext v
      rfl
    · rw [← restrictScalars_algebraMap_order C.chain o,
        LatticeChain.mem_order_iff_mem_endFiltration,
        ← mem_endFiltration_restrictScalars hlat]
      exact (algebraMap (subfieldIntegers F E) C.chain.order o).2
  · intro π
    have hmem := Stratum.fundamentalElement_mem_order C π hn hb
    rw [Stratum.fundamentalElement_eq_pow C π hn] at hmem ⊢
    refine ⟨⟨_, Subalgebra.smul_mem K (pow_mem hα _) _, rfl⟩, ?_⟩
    rw [LatticeChain.mem_order_iff_mem_endFiltration, ← mem_endFiltration_restrictScalars hlat]
    exact hmem

section TwoFields

variable {E₁ E₂ : Type uV} [Field E₁] [Algebra F E₁] [Module E₁ V] [IsScalarTower F E₁ V]
  [Field E₂] [Algebra F E₂] [Module E₂ V] [IsScalarTower F E₂ V]
  {O₁ O₂ : Type uV} [CommRing O₁] [Algebra O₁ E₁] [Module O₁ V] [IsScalarTower O₁ E₁ V]
  [CommRing O₂] [Algebra O₂ E₂] [Module O₂ V] [IsScalarTower O₂ E₂ V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `𝔅_{γ₁} + 𝔓 = 𝔅_{γ₂} + 𝔓`, every element of the order of a chain over `F[γ₁]` is
congruent modulo `𝔓` to an element of the order of a chain over `F[γ₂]` with the same
lattices. -/
theorem exists_order_congr_of_centralizer_eq (L : LatticeChain 𝒪[F] F V)
    (C₁ : LatticeChain O₁ E₁ V) (C₂ : LatticeChain O₂ E₂ V)
    (h₁ : ∀ i, (C₁.lattice i : Set V) = L.lattice i)
    (h₂ : ∀ i, (C₂.lattice i : Set V) = L.lattice i) (β₁ : E₁) (β₂ : E₂)
    (hβ₂ : Algebra.adjoin F ({β₂} : Set E₂) = ⊤)
    (hA : centralizerLattice L (subfieldEmbedding F E₁ V β₁) 0 ⊔ L.endFiltration 1 =
      centralizerLattice L (subfieldEmbedding F E₂ V β₂) 0 ⊔ L.endFiltration 1) :
    ∀ x : C₁.order, ∃ y : C₂.order,
      (x : Module.End E₁ V).restrictScalars F - (y : Module.End E₂ V).restrictScalars F ∈
        L.endFiltration 1 := by
  intro x
  have hX : (x : Module.End E₁ V).restrictScalars F ∈
      centralizerLattice L (subfieldEmbedding F E₁ V β₁) 0 := by
    refine ⟨(mem_endFiltration_restrictScalars h₁).mp x.2, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    change subfieldEmbedding F E₁ V β₁ * _ - _ * subfieldEmbedding F E₁ V β₁ = 0
    rw [(restrictScalars_commute (x : Module.End E₁ V) β₁).eq, sub_self]
  have hX' : (x : Module.End E₁ V).restrictScalars F ∈
      centralizerLattice L (subfieldEmbedding F E₁ V β₁) 0 ⊔ L.endFiltration 1 :=
    Submodule.mem_sup_left hX
  rw [hA, Submodule.mem_sup] at hX'
  obtain ⟨Y, hY, P, hP, hYP⟩ := hX'
  have hYc : Commute Y (subfieldEmbedding F E₂ V β₂) := by
    have h := hY.2
    rw [SetLike.mem_coe, LinearMap.mem_ker] at h
    change subfieldEmbedding F E₂ V β₂ * Y - Y * subfieldEmbedding F E₂ V β₂ = 0 at h
    exact (sub_eq_zero.mp h).symm
  obtain ⟨y, rfl⟩ := exists_restrictScalars_of_commute hβ₂ hYc
  refine ⟨⟨y, (mem_endFiltration_restrictScalars h₂).mpr hY.1⟩, ?_⟩
  change (x : Module.End E₁ V).restrictScalars F - y.restrictScalars F ∈ L.endFiltration 1
  rw [← hYP, add_sub_cancel_left]
  exact hP

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The lattice one period forward is the image under a prime element. -/
theorem lattice_add_period_eq_image (L : LatticeChain 𝒪[F] F V) (C : LatticeChain O₁ E₁ V)
    (h : ∀ i, (C.lattice i : Set V) = L.lattice i) (π : RingPrimeElement O₁) (i : ℤ) :
    (L.lattice (i + C.period) : Set V) =
      subfieldEmbedding F E₁ V (algebraMap O₁ E₁ π.1) '' (L.lattice i : Set V) := by
  obtain ⟨p, -, hp⟩ := π
  dsimp only
  rw [← h, ← h]
  ext v
  rw [SetLike.mem_coe, C.lattice_add_period i, ← hp, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [subfieldEmbedding_apply, algebraMap_smul]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [subfieldEmbedding_apply, algebraMap_smul]⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Prime elements congruent modulo `U¹(𝔄)` give the same period over the two fields. -/
theorem period_eq_of_primeElement_congr (L : LatticeChain 𝒪[F] F V)
    (C₁ : LatticeChain O₁ E₁ V) (C₂ : LatticeChain O₂ E₂ V)
    (h₁ : ∀ i, (C₁.lattice i : Set V) = L.lattice i)
    (h₂ : ∀ i, (C₂.lattice i : Set V) = L.lattice i)
    (π₁ : RingPrimeElement O₁) (π₂ : RingPrimeElement O₂) {u : (Module.End F V)ˣ}
    (hu : u ∈ L.unitFiltration 1)
    (hπ : subfieldEmbedding F E₂ V (algebraMap O₂ E₂ π₂.1) =
      subfieldEmbedding F E₁ V (algebraMap O₁ E₁ π₁.1) * (u : Module.End F V)) :
    C₂.period = C₁.period := by
  have hu0 : ((u : Module.End F V) '' (L.lattice 0 : Set V)) = L.lattice 0 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      simpa using (L.mem_order.mp hu.1) 0 v hv
    · intro v hv
      refine ⟨((u⁻¹ : (Module.End F V)ˣ) : Module.End F V) v,
        by simpa using (L.mem_order.mp hu.2.1) 0 v hv, ?_⟩
      change ((u : Module.End F V) * ((u⁻¹ : (Module.End F V)ˣ) : Module.End F V)) v = v
      rw [Units.mul_inv, Module.End.one_apply]
  have h := lattice_add_period_eq_image L C₂ h₂ π₂ 0
  rw [hπ, Module.End.coe_mul, Set.image_comp, hu0, ← lattice_add_period_eq_image L C₁ h₁ π₁ 0]
    at h
  have h' := L.injective (SetLike.coe_injective h)
  omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A prime element over `E` lies in `𝔓^e` for the period `e` over `E`. -/
theorem primeElement_pow_mem_endFiltration (L : LatticeChain 𝒪[F] F V)
    (C : LatticeChain O₁ E₁ V) (h : ∀ i, (C.lattice i : Set V) = L.lattice i)
    (π : RingPrimeElement O₁) (k : ℕ) :
    subfieldEmbedding F E₁ V (algebraMap O₁ E₁ π.1) ^ k ∈ L.endFiltration (k * C.period) := by
  intro i v hv
  rw [← SetLike.mem_coe, ← h] at hv ⊢
  rw [← map_pow, subfieldEmbedding_apply]
  exact Stratum.primeElement_smul_mem C π k hv

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The elements `y_b` of two strata over different fields are congruent modulo `𝔓` when their
elements and their prime elements are congruent. -/
theorem restrict_fundamentalElement_sub_mem (L : LatticeChain 𝒪[F] F V)
    (D₁ : Stratum O₁ E₁ V) (D₂ : Stratum O₂ E₂ V)
    (h₁ : ∀ i, (D₁.chain.lattice i : Set V) = L.lattice i)
    (h₂ : ∀ i, (D₂.chain.lattice i : Set V) = L.lattice i)
    (hn : D₂.n = D₁.n) (hn0 : 0 ≤ D₁.n) (he : D₂.chain.period = D₁.chain.period)
    (hb₁ : D₁.b ∈ D₁.chain.endFiltration (-D₁.n)) (hb₂ : D₂.b ∈ D₂.chain.endFiltration (-D₂.n))
    (hcong : D₂.b.restrictScalars F - D₁.b.restrictScalars F ∈ L.endFiltration (-D₁.n + 1))
    (π₁ : RingPrimeElement O₁) (π₂ : RingPrimeElement O₂)
    (hπ : subfieldEmbedding F E₂ V (algebraMap O₂ E₂ π₂.1) -
      subfieldEmbedding F E₁ V (algebraMap O₁ E₁ π₁.1) ∈ L.endFiltration (D₁.chain.period + 1)) :
    (D₂.fundamentalElement π₂).restrictScalars F - (D₁.fundamentalElement π₁).restrictScalars F ∈
      L.endFiltration 1 := by
  set e := D₁.chain.period
  set a := (D₁.n / (Nat.gcd e D₁.n.natAbs : ℤ)).toNat
  set c := e / Nat.gcd e D₁.n.natAbs
  have hy₁ := Stratum.fundamentalElement_eq_pow D₁ π₁ hn0
  have hy₂ := Stratum.fundamentalElement_eq_pow D₂ π₂ (hn ▸ hn0)
  rw [hn, he] at hy₂
  have hres : ∀ {E : Type uV} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
      (s : E) (X : Module.End E V) (k : ℕ),
      (s • X ^ k).restrictScalars F = subfieldEmbedding F E V s * (X.restrictScalars F) ^ k := by
    intro E _ _ _ _ s X k
    let ρ : Module.End E V →+* Module.End F V :=
      { toFun := fun f => f.restrictScalars F
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hpow : (X ^ k).restrictScalars F = (X.restrictScalars F) ^ k := map_pow ρ X k
    rw [← hpow]
    ext v
    rfl
  rw [hy₁, hy₂, hres, hres, map_pow, map_pow]
  have hP₁ := primeElement_pow_mem_endFiltration L D₁.chain h₁ π₁ a
  have hB₁ : (D₁.b.restrictScalars F) ^ c ∈ L.endFiltration (c * -D₁.n) :=
    L.pow_mem_endFiltration_mul ((mem_endFiltration_restrictScalars h₁).mp hb₁) c
  have hB₂ : (D₂.b.restrictScalars F) ^ c ∈ L.endFiltration (c * -D₁.n) := by
    have := (mem_endFiltration_restrictScalars h₂).mp hb₂
    rw [hn] at this
    exact L.pow_mem_endFiltration_mul this c
  have hPd := L.pow_sub_pow_mem_endFiltration
    (by rw [← he]; simpa using primeElement_pow_mem_endFiltration L D₂.chain h₂ π₂ 1)
    (by simpa using primeElement_pow_mem_endFiltration L D₁.chain h₁ π₁ 1) hπ a
  have hBd := L.pow_sub_pow_mem_endFiltration
    ((mem_endFiltration_restrictScalars h₂).mp (hn ▸ hb₂))
    ((mem_endFiltration_restrictScalars h₁).mp hb₁) hcong c
  have h := L.mul_sub_mul_mem_endFiltration
    (by simpa [← he] using primeElement_pow_mem_endFiltration L D₂.chain h₂ π₂ a) hB₁ hPd hBd
  rwa [show (a : ℤ) * e + (c : ℤ) * -D₁.n + 1 = 1 by
    have := Stratum.fundamental_shift_zero e D₁.n hn0
    linarith] at h

end TwoFields

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1600000 in
/-- **Reduction of BK94 (5.3)–(5.6).** -/
theorem simpleCharacterCriticalTranslationReduction :
    SimpleCharacterCriticalTranslationReductionStatement.{uF, uV} := by
  intro hRC hLow hNS F _ _ _ _ V _ _ _ ψF hψ L n m T₁ T₂ S₁ hTC hS₁ hcrit
  -- Lower the comparison to depth zero, keeping the critical exponent of `γ₁`.
  have hr₁ : (m : ℤ) ≤ T₁.1.r := by rw [T₁.2.2.2.1]; omega
  have hr₂ : (m : ℤ) ≤ T₂.1.r := by rw [T₂.2.2.2.1]; omega
  have hr₂₀ : (0 : ℤ) ≤ T₂.1.r := by rw [T₂.2.2.2.1]; omega
  let T₁m : SimpleStratumAt L n m :=
    ⟨T₁.1.lowerIndex m hr₁, T₁.2.1, T₁.2.2.1, rfl, T₁.2.2.2.2.lowerIndex hr₁⟩
  let T₂m : SimpleStratumAt L n m :=
    ⟨T₂.1.lowerIndex m hr₂, T₂.2.1, T₂.2.2.1, rfl, T₂.2.2.2.2.lowerIndex hr₂⟩
  let T₂₀ : SimpleStratumAt L n 0 :=
    ⟨T₂.1.lowerIndex 0 hr₂₀, T₂.2.1, T₂.2.2.1, rfl, T₂.2.2.2.2.lowerIndex hr₂₀⟩
  have hCm : simpleCharacterPairs ψF T₁m.1 m = simpleCharacterPairs ψF T₂m.1 m := by
    rw [simpleCharacterPairs_congr ψF (S := T₁.1) (S' := T₁m.1) rfl rfl rfl T₁.2.2.2.2
        T₁m.2.2.2.2 m, hTC,
      simpleCharacterPairs_congr ψF (S := T₂.1) (S' := T₂m.1) rfl rfl rfl T₂.2.2.2.2
        T₂m.2.2.2.2 m]
  obtain ⟨R₁, hR₁b, hR₁k, hR₁C⟩ := exists_depthZero_of_pairs_eq hLow ψF hψ L n m T₁m T₂m hCm
  have hR₁T₂ : simpleCharacterPairs ψF R₁.1 0 = simpleCharacterPairs ψF T₂₀.1 0 := by
    rw [hR₁C]
    exact (simpleCharacterPairs_congr ψF (S := T₂m.1) (S' := T₂₀.1) rfl rfl rfl T₂m.2.2.2.2
      T₂₀.2.2.2.2 0).symm
  -- The new first element `γ₁*` keeps the critical exponent of `γ₁`.
  have hmn : (m : ℤ) + 1 < n := by
    have h := T₁.1.r_lt_n
    rw [T₁.2.2.2.1, T₁.2.2.1] at h
    exact h
  have hk₁ : criticalExponent L R₁.1.b < ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ) := by
    rw [hR₁k]
    have h := T₁.2.2.2.2.2
    rw [T₁.2.1, T₁.2.2.2.1] at h
    exact h
  let T₁s : Stratum 𝒪[F] F V :=
    { R₁.1 with r := (m : ℤ) + 1, r_lt_n := by rw [R₁.2.2.1]; exact hmn }
  have hT₁s : T₁s.IsSimple := ⟨R₁.2.2.2.2.1, by
    change criticalExponent R₁.1.chain R₁.1.b < _
    rw [R₁.2.1]
    exact hk₁⟩
  -- The perturbation `c = β₁ − γ₁*` has valuation exactly `−(m+1)`.
  set c := S₁.1.b - R₁.1.b with hcdef
  have hc : c ∈ L.endFiltration (-((m : ℤ) + 1)) := by
    rw [show c = (S₁.1.b - T₁.1.b) - (R₁.1.b - T₁.1.b) by rw [hcdef]; abel]
    exact sub_mem hS₁ (L.endFiltration_antitone (by omega) hR₁b)
  have hcn : c ∉ L.endFiltration (-(m : ℤ)) := by
    intro hcm
    let Rm : Stratum 𝒪[F] F V :=
      { R₁.1 with r := (m : ℤ), r_lt_n := by rw [R₁.2.2.1]; omega }
    have hRm : Rm.IsSimple := ⟨R₁.2.2.2.2.1, by
      change criticalExponent R₁.1.chain R₁.1.b < ((-(m : ℤ) : ℤ) : WithBot ℤ)
      rw [R₁.2.1]
      exact hk₁.trans (WithBot.coe_lt_coe.mpr (by omega))⟩
    have hEq : S₁.1.Equivalent Rm := Stratum.equivalent_of_sub_mem (S := S₁.1) (T := Rm)
      (by change R₁.1.chain = S₁.1.chain; rw [R₁.2.1, S₁.2.1])
      (by change (m : ℤ) = S₁.1.r; rw [S₁.2.2.2.1])
      (by rw [S₁.2.1, S₁.2.2.2.1]; exact hcm)
    have hk := ((stratumEquivalence F V S₁.1 Rm hEq).2.2.2 S₁.2.2.2.2 hRm).2.1
    change criticalExponent S₁.1.chain S₁.1.b = criticalExponent R₁.1.chain R₁.1.b at hk
    rw [S₁.2.1, R₁.2.1, hcrit] at hk
    rw [← hk] at hk₁
    exact lt_irrefl _ hk₁
  have hval : L.valuation c = ((-((m : ℤ) + 1) : ℤ) : WithTop ℤ) :=
    L.valuation_eq_of_mem_of_notMem hc (by rwa [show -((m : ℤ) + 1) + 1 = -(m : ℤ) by ring])
  -- The residue comparison of BK94 (5.2) for `γ₁*` and `γ₂`.
  obtain ⟨hA, hrest⟩ := hRC F V ψF hψ L n R₁ T₂₀ hR₁T₂
  obtain ⟨hf₁, hnorm₁⟩ := R₁.2.2.2.2.1.1
  obtain ⟨hf₂, hnorm₂⟩ := T₂₀.2.2.2.2.1.1
  letI := hf₁.toField
  letI := hf₂.toField
  obtain ⟨hi₁₂, hi₂₁, ⟨π₁, π₂, u, hu, hπ⟩, s₁, s₂, hs⟩ := hrest hf₁ hf₂
  have : FiniteDimensional F (elementAlgebra R₁.1.b) :=
    Module.Finite.of_injective (elementAlgebra R₁.1.b).val.toLinearMap Subtype.val_injective
  have : FiniteDimensional F (elementAlgebra T₂₀.1.b) :=
    Module.Finite.of_injective (elementAlgebra T₂₀.1.b).val.toLinearMap Subtype.val_injective
  -- The derived stratum of `γ₁*` (BK93 (2.4.1)(iii)).
  let Sβ : Stratum 𝒪[F] F V :=
    { S₁.1 with r := (m : ℤ) + 1, r_lt_n := by rw [S₁.2.2.1]; exact hmn }
  have hSβk : criticalExponent Sβ.chain Sβ.b = ((-Sβ.r : ℤ) : WithBot ℤ) := by
    change criticalExponent S₁.1.chain S₁.1.b = ((-((m : ℤ) + 1) : ℤ) : WithBot ℤ)
    rw [S₁.2.1]
    exact hcrit
  have hSβT : Sβ.Equivalent T₁s := Stratum.equivalent_of_sub_mem (S := Sβ) (T := T₁s)
    (by change R₁.1.chain = S₁.1.chain; rw [R₁.2.1, S₁.2.1]) rfl
    (by change c ∈ S₁.1.chain.endFiltration (-((m : ℤ) + 1)); rw [S₁.2.1]; exact hc)
  have hDer := criticalDerivedStratum F V Sβ T₁s S₁.2.2.2.2.1 hSβk
    (by change R₁.1.chain = S₁.1.chain; rw [R₁.2.1, S₁.2.1])
    (by change R₁.1.n = S₁.1.n; rw [R₁.2.2.1, S₁.2.2.1]) rfl hT₁s hSβT
  obtain ⟨D₁, C₁, ⟨-, -, -, hD₁lat, hD₁n, hD₁r, hD₁b⟩, hC₁c, hC₁n, hC₁r, hD₁C₁, hC₁s⟩ :
      ∃ D C : Stratum (subfieldIntegers F (elementAlgebra R₁.1.b)) (elementAlgebra R₁.1.b) V,
        T₁s.IsDerivedStratum (elementAlgebra R₁.1.b) c s₁ D ∧ C.chain = D.chain ∧ C.n = D.n ∧
          C.r = D.r ∧ D.Equivalent C ∧ C.IsSimple :=
    hDer hf₁ s₁
  have hlat₁ : ∀ i, (D₁.chain.lattice i : Set V) = L.lattice i := fun i =>
    (hD₁lat i).trans (by rw [show T₁s.chain = L from R₁.2.1])
  -- The candidate derived stratum of `γ₂`.
  have hE₂ : ∀ a : (elementAlgebra T₂₀.1.b)ˣ,
      subfieldUnits F (elementAlgebra T₂₀.1.b) V a ∈ L.stabilizer := by
    intro a
    have h := hnorm₂ a
    rwa [T₂₀.2.1] at h
  let B₂ := L.extensionChain hE₂
  have hlat₂ : ∀ i, (B₂.lattice i : Set V) = L.lattice i := fun _ => rfl
  have hs₂c : s₂ c ∈ B₂.endFiltration (-((m : ℤ) + 1)) := by
    change (s₂ c).restrictScalars F ∈ L.endFiltration (-((m : ℤ) + 1))
    have h := (tameCorestriction F V (elementAlgebra T₂₀.1.b)).2.2 s₂ L hE₂ (-((m : ℤ) + 1))
    have hmem : s₂ c ∈ s₂ '' (L.endFiltration (-((m : ℤ) + 1)) : Set (Module.End F V)) :=
      ⟨c, hc, rfl⟩
    exact (Set.ext_iff.mp h _).mp hmem
  let D₂ : Stratum (subfieldIntegers F (elementAlgebra T₂₀.1.b)) (elementAlgebra T₂₀.1.b) V :=
    ⟨B₂, (m : ℤ) + 1, m, s₂ c, by omega, PureApproximation.le_valuation_of_mem_subfield B₂ hs₂c⟩
  -- Residue data of the simple stratum `C₁` equivalent to the derived stratum of `γ₁*`.
  have hlatC₁ : ∀ i, (C₁.chain.lattice i : Set V) = L.lattice i := by
    intro i
    rw [hC₁c]
    exact hlat₁ i
  have hn₁ : D₁.n = (m : ℤ) + 1 := hD₁n
  have hr₁' : D₁.r = D₁.n - 1 := by rw [hD₁r, hD₁n]
  have hC₁n' : C₁.n = (m : ℤ) + 1 := hC₁n.trans hn₁
  obtain ⟨R, hR, hg, hscal, hyC⟩ :=
    simple_residue_data L C₁ hlatC₁ hC₁s (by rw [hC₁n']; omega)
  have hb₁ : D₁.b ∈ D₁.chain.endFiltration (-D₁.n) :=
    PureApproximation.mem_endFiltration_of_le_valuation_subfield D₁.chain D₁.valuation_ge
  have hbC₁ : C₁.b ∈ D₁.chain.endFiltration (-D₁.n) := by
    have h := PureApproximation.mem_endFiltration_of_le_valuation_subfield C₁.chain
      C₁.valuation_ge
    rwa [hC₁c, hC₁n] at h
  have hdC₁ : D₁.b - C₁.b ∈ D₁.chain.endFiltration (1 - D₁.n) := by
    have h := Stratum.sub_mem_of_equivalent hD₁C₁
    rwa [hr₁', show -(D₁.n - 1) = 1 - D₁.n by ring] at h
  have hcoset₁ : D₁.b.restrictScalars F - C₁.b.restrictScalars F ∈
      L.endFiltration (1 - D₁.n) :=
    (mem_endFiltration_restrictScalars hlat₁).mp hdC₁
  have hgD₁ : ∀ i (v : V), C₁.b.restrictScalars F v ∈ L.lattice (i + -D₁.n) ↔
      v ∈ L.lattice i := by
    rw [← hC₁n]
    exact hg
  have hyD₁ : (D₁.fundamentalElement π₁).restrictScalars F -
      (C₁.fundamentalElement π₁).restrictScalars F ∈ L.endFiltration 1 := by
    have h := Stratum.fundamentalElement_sub_mem D₁ C₁ π₁ hC₁c hC₁n (by rw [hn₁]; omega)
      hb₁ hbC₁ hdC₁
    exact (mem_endFiltration_restrictScalars hlat₁).mp h
  have hD₁ns : D₁.IsNonsplit := derived_isNonsplit L D₁ hlat₁ hr₁' (by rw [hn₁]; omega) hb₁
    hgD₁ hcoset₁ π₁ R hR
    (fun o => ⟨_, (hscal o).1, (hscal o).2, by rw [sub_self]; exact zero_mem _⟩)
    ⟨_, (hyC π₁).1, (hyC π₁).2, hyD₁⟩
  -- BK93 (2.4.13) for the derived stratum of `γ₁*`: its residue centralizer is semisimple.
  have : FiniteDimensional (elementAlgebra R₁.1.b) V := D₁.chain.finiteDimensional
  have : FiniteDimensional (elementAlgebra T₂₀.1.b) V := B₂.finiteDimensional
  have hsemi₁ : IsSemisimpleRing D₁.residueCentralizer :=
    ((hNS F).2 (elementAlgebra R₁.1.b) V D₁ (by rw [hn₁]; omega) hD₁ns).mp
      ⟨C₁, hC₁c, hC₁n, hC₁r, hD₁C₁, hC₁s⟩
  -- The two residue centralizers have the same image in `𝔄/𝔓`.
  have hb₂ : D₂.b ∈ D₂.chain.endFiltration (-D₂.n) := hs₂c
  have hn₂₁ : D₂.n = D₁.n := hn₁.symm
  have hcong : D₁.b.restrictScalars F - D₂.b.restrictScalars F ∈ L.endFiltration (-(m : ℤ)) := by
    rw [hD₁b]
    exact hs m c hc
  have hcong₁₂ : D₁.b.restrictScalars F - D₂.b.restrictScalars F ∈
      L.endFiltration (1 - D₁.n) := by
    rw [hn₁, show (1 : ℤ) - ((m : ℤ) + 1) = -(m : ℤ) by ring]
    exact hcong
  have hcong₂₁ : D₂.b.restrictScalars F - D₁.b.restrictScalars F ∈
      L.endFiltration (1 - D₂.n) := by
    have h := neg_mem hcong₁₂
    rw [neg_sub] at h
    rwa [hn₂₁]
  have hA' : centralizerLattice L (subfieldEmbedding F (elementAlgebra R₁.1.b) V
        (elementGenerator R₁.1.b)) 0 ⊔ L.endFiltration 1 =
      centralizerLattice L (subfieldEmbedding F (elementAlgebra T₂₀.1.b) V
        (elementGenerator T₂₀.1.b)) 0 ⊔ L.endFiltration 1 := by
    rw [subfieldEmbedding_elementGenerator R₁.1.b hf₁,
      subfieldEmbedding_elementGenerator T₂₀.1.b hf₂]
    exact hA
  have hA₁₂ := exists_order_congr_of_centralizer_eq L D₁.chain D₂.chain hlat₁ hlat₂
    (elementGenerator R₁.1.b) (elementGenerator T₂₀.1.b) (adjoin_elementGenerator T₂₀.1.b) hA'
  have hA₂₁ := exists_order_congr_of_centralizer_eq L D₂.chain D₁.chain hlat₂ hlat₁
    (elementGenerator T₂₀.1.b) (elementGenerator R₁.1.b) (adjoin_elementGenerator R₁.1.b) hA'.symm
  have heq := le_antisymm
    (residueCentralizer_map_le D₁ D₂ hlat₁ hlat₂ hn₂₁ hb₁ hb₂ hcong₁₂ hA₁₂)
    (residueCentralizer_map_le D₂ D₁ hlat₂ hlat₁ hn₂₁.symm hb₂ hb₁ hcong₂₁ hA₂₁)
  have hsemi₂ : IsSemisimpleRing D₂.residueCentralizer :=
    isSemisimpleRing_residueCentralizer_of_map_eq D₁ D₂ hlat₁ hlat₂ heq hsemi₁
  -- BK94 (5.3): the derived stratum of `γ₂` is nonsplit fundamental.
  have hper : D₂.chain.period = D₁.chain.period :=
    period_eq_of_primeElement_congr L D₁.chain D₂.chain hlat₁ hlat₂ π₁ π₂ hu hπ
  have hπ' : subfieldEmbedding F (elementAlgebra T₂₀.1.b) V (π₂.1 : elementAlgebra T₂₀.1.b) -
      subfieldEmbedding F (elementAlgebra R₁.1.b) V (π₁.1 : elementAlgebra R₁.1.b) ∈
        L.endFiltration (D₁.chain.period + 1) := by
    have h1 : subfieldEmbedding F (elementAlgebra R₁.1.b) V (π₁.1 : elementAlgebra R₁.1.b) ∈
        L.endFiltration D₁.chain.period := by
      simpa using primeElement_pow_mem_endFiltration L D₁.chain hlat₁ π₁ 1
    rw [hπ, show ∀ a b : Module.End F V, a * b - a = a * (b - 1) from
      fun a b => by noncomm_ring]
    exact L.mul_mem_endFiltration h1 hu.2.2
  have hyD₂ : (D₂.fundamentalElement π₂).restrictScalars F -
      (C₁.fundamentalElement π₁).restrictScalars F ∈ L.endFiltration 1 := by
    have h := restrict_fundamentalElement_sub_mem L D₁ D₂ hlat₁ hlat₂ hn₂₁ (by rw [hn₁]; omega)
      hper hb₁ hb₂ (by rw [show -D₁.n + 1 = 1 - D₂.n by rw [hn₂₁]; ring]; exact hcong₂₁) π₁ π₂
      hπ'
    have h' := add_mem h hyD₁
    convert h' using 1
    abel
  have hcoset₂ : D₂.b.restrictScalars F - C₁.b.restrictScalars F ∈
      L.endFiltration (1 - D₂.n) := by
    have h' := add_mem hcong₂₁ (hn₂₁ ▸ hcoset₁)
    convert h' using 1
    abel
  have hgD₂ : ∀ i (v : V), C₁.b.restrictScalars F v ∈ L.lattice (i + -D₂.n) ↔
      v ∈ L.lattice i := by
    rw [hn₂₁]
    exact hgD₁
  have hD₂ns : D₂.IsNonsplit := derived_isNonsplit L D₂ hlat₂
    (by change (m : ℤ) = (m : ℤ) + 1 - 1; ring)
    (by change (0 : ℤ) ≤ (m : ℤ) + 1; omega) hb₂ hgD₂ hcoset₂ π₂ R hR
    (fun o => by
      obtain ⟨o₁, ho⟩ := hi₂₁ o
      refine ⟨_, (hscal o₁).1, (hscal o₁).2, ?_⟩
      have h := neg_mem ho
      rwa [neg_sub] at h)
    ⟨_, (hyC π₁).1, (hyC π₁).2, hyD₂⟩
  -- BK93 (2.4.13) for the derived stratum of `γ₂`, then the refinement theorem (2.2.8).
  obtain ⟨C₂, hC₂c, hC₂n, hC₂r, hD₂C₂, hC₂s⟩ :=
    ((hNS F).2 (elementAlgebra T₂₀.1.b) V D₂ (by change (1 : ℤ) ≤ (m : ℤ) + 1; omega)
      hD₂ns).mpr hsemi₂
  have hDer₂ : T₂.1.IsDerivedStratum (elementAlgebra T₂₀.1.b) c s₂ D₂ := by
    refine ⟨T₂.2.2.2.2, ⟨elementGenerator T₂₀.1.b, subfieldEmbedding_elementGenerator T₂₀.1.b hf₂,
      adjoin_elementGenerator T₂₀.1.b⟩, ?_, ?_, ?_, ?_, rfl⟩
    · rw [T₂.2.1, T₂.2.2.2.1]
      exact hc
    · intro i
      rw [T₂.2.1]
      rfl
    · exact T₂.2.2.2.1.symm
    · change (m : ℤ) = T₂.1.r - 1
      rw [T₂.2.2.2.1]
      ring
  obtain ⟨T, hTc, hTn, hTr, hTs, hTcoset, -⟩ := refinement F V (elementAlgebra T₂₀.1.b) T₂.1 c s₂
    D₂ C₂ hDer₂ (by rw [T₂.2.1, T₂.2.2.2.1]; exact hval) hC₂c hC₂n hC₂r hD₂C₂ hC₂s
  have hTb : T.b - (T₂.1.b + c) ∈ L.endFiltration (-(m : ℤ)) := by
    have hmem : T.b ∈ T.coset := by
      change T.b - T.b ∈ T.chain.endFiltration (-T.r)
      rw [sub_self]
      exact zero_mem _
    rw [hTcoset] at hmem
    have h : T₂.1.chain.endFiltration (1 - T₂.1.r) = L.endFiltration (-(m : ℤ)) := by
      rw [T₂.2.1, T₂.2.2.2.1, show (1 : ℤ) - ((m : ℤ) + 1) = -(m : ℤ) by ring]
    exact h ▸ hmem
  refine ⟨⟨T, hTc.trans T₂.2.1, hTn.trans T₂.2.2.1, by rw [hTr, T₂.2.2.2.1]; ring, hTs⟩, ?_⟩
  have hdiff : c - (S₁.1.b - T₁.1.b) ∈ L.endFiltration (-(m : ℤ)) := by
    rw [hcdef, show S₁.1.b - R₁.1.b - (S₁.1.b - T₁.1.b) = -(R₁.1.b - T₁.1.b) by abel]
    exact neg_mem hR₁b
  have h := add_mem hTb hdiff
  convert h using 1
  change T.b - (T₂.1.b + (S₁.1.b - T₁.1.b)) = T.b - (T₂.1.b + c) + (c - (S₁.1.b - T₁.1.b))
  abel

end Langlands.BushnellKutzko
