import Langlands.BushnellKutzko.ClassCoverAssembly
import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.CriticalDerivedStratumProof
import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceProof
import Langlands.BushnellKutzko.AdjointExactnessProof
import Langlands.BushnellKutzko.TameCorestrictionProof

/-! # Covering simple-character classes: scalar perturbations of simple refinements -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV uF

section Scalar

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- Multiplication by a scalar, as an endomorphism. -/
def scalarEnd (c : K) : Module.End K V := c • LinearMap.id

omit [CommRing O] [Algebra O K] [Module O V] [IsScalarTower O K V] in
@[simp] theorem scalarEnd_apply (c : K) (v : V) : scalarEnd c v = c • v := rfl

omit [CommRing O] [Algebra O K] [Module O V] [IsScalarTower O K V] in
theorem scalarEnd_eq_algebraMap (c : K) :
    scalarEnd c = algebraMap K (Module.End K V) c := by
  ext v
  simp [Module.algebraMap_end_apply]

omit [CommRing O] [Algebra O K] [Module O V] [IsScalarTower O K V] in
theorem scalarEnd_add (c d : K) : (scalarEnd (c + d) : Module.End K V) = scalarEnd c + scalarEnd d := by
  ext v
  simp [add_smul]

omit [CommRing O] [Algebra O K] [Module O V] [IsScalarTower O K V] in
theorem scalarEnd_neg (c : K) : (scalarEnd (-c) : Module.End K V) = -scalarEnd c := by
  ext v
  simp

/-- Adding a scalar does not change the generated algebra. -/
theorem elementAlgebra_add_algebraMap (x : Module.End K V) (c : K) :
    elementAlgebra (x + algebraMap K (Module.End K V) c) = elementAlgebra x := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact add_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ c)
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    have h := sub_mem (Algebra.subset_adjoin (Set.mem_singleton
      (x + algebraMap K (Module.End K V) c)))
      (Subalgebra.algebraMap_mem (elementAlgebra (x + algebraMap K (Module.End K V) c)) c)
    simpa using h

/-- Adding a scalar does not change the adjoint map. -/
theorem adjointMap_add_algebraMap (x : Module.End K V) (c : K) :
    adjointMap O (x + algebraMap K (Module.End K V) c) = adjointMap O x := by
  ext y : 1
  simp only [adjointMap, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    add_mul, mul_add, Algebra.commutes c y]
  abel

/-- Adding a scalar does not change the critical exponent. -/
theorem criticalExponent_add_algebraMap (L : LatticeChain O K V) (x : Module.End K V) (c : K) :
    criticalExponent L (x + algebraMap K (Module.End K V) c) = criticalExponent L x := by
  have h : Algebra.adjoin K ({x + algebraMap K (Module.End K V) c} : Set (Module.End K V)) =
      Algebra.adjoin K ({x} : Set (Module.End K V)) := elementAlgebra_add_algebraMap x c
  have hset : criticalIndexSet L (x + algebraMap K (Module.End K V) c) =
      criticalIndexSet L x := by
    unfold criticalIndexSet adjointLattice centralizerLattice
    rw [adjointMap_add_algebraMap]
  unfold criticalExponent
  rw [hset]
  by_cases hx : Algebra.adjoin K ({x} : Set (Module.End K V)) = ⊥
  · rw [ite_eq_left hx, ite_eq_left (h.trans hx)]
  · rw [ite_eq_right hx, ite_eq_right (fun h' => hx (h.symm.trans h'))]

/-- A stratum whose element is that of a simple stratum plus a scalar, with the same chain and
the same index `r`, and whose element has valuation exactly `-n`, is simple. -/
theorem Stratum.isSimple_of_add_algebraMap {C C' : Stratum O K V} (hchain : C'.chain = C.chain)
    (hr : C'.r = C.r) (c : K) (hb : C'.b = C.b + scalarEnd c)
    (hC : C.IsSimple) (hval : C'.chain.valuation C'.b = (-C'.n : WithTop ℤ)) : C'.IsSimple := by
  rw [scalarEnd_eq_algebraMap] at hb
  obtain ⟨⟨hpure, -⟩, hcrit⟩ := hC
  refine ⟨⟨?_, hval⟩, ?_⟩
  · have key : ∀ A : Subalgebra K (Module.End K V), A = elementAlgebra C.b →
        ∃ h : IsField A, letI := h.toField
          ∀ a : Aˣ, subfieldUnits K A V a ∈ C.chain.stabilizer := by
      rintro A rfl
      exact hpure
    rw [hchain]
    exact key _ (by rw [hb, elementAlgebra_add_algebraMap])
  · rw [hb, hchain, criticalExponent_add_algebraMap, hr]
    exact hcrit

/-- Two indexed lattice chains are equal when the underlying sets of their lattices agree at
every index `i`. -/
theorem LatticeChain.eq_of_lattice_coe {C D : LatticeChain O K V}
    (h : ∀ i, (C.lattice i : Set V) = D.lattice i) : C = D := by
  cases C
  cases D
  congr
  funext i
  exact SetLike.coe_injective (h i)

end Scalar

section Refine

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem restrictScalars_scalarEnd {E : Type uV} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (c : E) :
    (scalarEnd c : Module.End E V).restrictScalars F = subfieldEmbedding F E V c := by
  ext v
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Endomorphisms linear over an intermediate field commute with its elements. -/
theorem commute_subfieldEmbedding {E : Type uV} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (y : Module.End E V) (c : E) :
    subfieldEmbedding F E V c * y.restrictScalars F = y.restrictScalars F * subfieldEmbedding F E V c := by
  ext v
  simp [subfieldEmbedding_apply]

/-- **BK93 (1.4.10).** Let `E = F[β₀]` be a field generated by an element `β₀` that is not a
scalar, with `E^×` normalizing `L`, let `s` be a tame corestriction relative to `E/F`, and assume
`k₀(β₀,𝔄) < -(k + 1)`. If `b ∈ 𝔓^{-(k+1)}` and `s(b) ∈ 𝔓^{-k}`, then `b ≡ a_{β₀}(x) (mod 𝔓^{-k})`
for some `x ∈ 𝔓`. A simple stratum `[𝔄,n,k+1,β₀]` with `β₀` not a scalar supplies these
hypotheses. -/
theorem exists_adjoint_approx [FiniteDimensional F V] {E : Type uV} [Field E] [Algebra F E]
    [Module E V] [IsScalarTower F E V] (L : LatticeChain 𝒪[F] F V) (β₀ : E)
    (hgen : Algebra.adjoin F ({β₀} : Set E) = ⊤) (hns : ¬ ∃ a : F, algebraMap F E a = β₀)
    (hnorm : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) (s : TameCorestriction 𝒪[F] F E V)
    (k : ℤ) (hk : criticalExponent L (subfieldEmbedding F E V β₀) < ((-(k + 1) : ℤ) : WithBot ℤ))
    {b : A} (hb : b ∈ L.endFiltration (-(k + 1)))
    (hsb : (s b).restrictScalars F ∈ L.endFiltration (-k)) :
    ∃ x ∈ L.endFiltration 1,
      b - adjointMap 𝒪[F] (subfieldEmbedding F E V β₀) x ∈ L.endFiltration (-k) := by
  obtain ⟨-, -, -, ⟨k₀, -, hk₀⟩, hex⟩ := adjointExactness F V E L β₀ hgen hns hnorm
  rw [hk₀] at hk
  have hk' : k₀ < -(k + 1) := WithBot.coe_lt_coe.mp hk
  obtain ⟨-, -, -, h4⟩ := hex s (-(k + 1) - k₀) k₀ 1 (le_of_eq hk₀) le_rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h4
  have hm : -(k + 1) - k₀ + k₀ = -(k + 1) := by ring
  have hm' : -(k + 1) - k₀ + k₀ + 1 = -k := by ring
  have hbP : b ∈ (L.endFiltration (-(k + 1) - k₀ + k₀)).toAddSubgroup := by
    rw [hm]
    exact hb
  have hgT : (s b).restrictScalars F ∈
      (centralizerLattice L (subfieldEmbedding F E V β₀) (-(k + 1) - k₀ + k₀ + 1)).toAddSubgroup := by
    rw [hm']
    refine ⟨hsb, ?_⟩
    change subfieldEmbedding F E V β₀ * (s b).restrictScalars F -
      (s b).restrictScalars F * subfieldEmbedding F E V β₀ = 0
    rw [commute_subfieldEmbedding, sub_self]
  obtain ⟨x, hx, hbx⟩ := (hmid b hbP).mp hgT
  refine ⟨x, ?_, ?_⟩
  · have hle : centralizerLattice L (subfieldEmbedding F E V β₀) (-(k + 1) - k₀) *
        adjointLattice L (subfieldEmbedding F E V β₀) k₀ ≤ L.endFiltration 1 := by
      apply Submodule.mul_le.mpr
      intro q hq y hy
      have := L.mul_mem_endFiltration hq.1 hy.1
      exact L.endFiltration_antitone (by omega) this
    exact hle hx
  · change b - _ ∈ L.endFiltration (-(k + 1) - k₀ + k₀ + 1) at hbx
    rwa [hm'] at hbx

/-- Let `E` be an intermediate field all of whose elements are scalars of `F`, with `E^×`
normalizing `L`, and let `s` be a tame corestriction relative to `E/F`. If `s(y) ∈ 𝔓^j(𝔄)` then
`y ∈ 𝔓^j(𝔄)`. -/
theorem mem_endFiltration_of_tameCorestriction_scalar [FiniteDimensional F V] {E : Type uV}
    [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (hscalar : ∀ c : E, ∃ a : F, algebraMap F E a = c) (L : LatticeChain 𝒪[F] F V)
    (hnorm : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) (s : TameCorestriction 𝒪[F] F E V)
    (j : ℤ) {y : A} (hy : (s y).restrictScalars F ∈ L.endFiltration j) : y ∈ L.endFiltration j := by
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  let lift : A → Module.End E V := fun z =>
    { toFun := z
      map_add' := z.map_add
      map_smul' := fun c v => by
        obtain ⟨a, rfl⟩ := hscalar c
        simp only [algebraMap_smul, map_smul, RingHom.id_apply] }
  have hlift (z : A) : (lift z).restrictScalars F = z := rfl
  have himage := fun j => (tameCorestriction F V E).2.2 s L hnorm j
  have hsl (z : A) : s z = lift z * s 1 := by
    have := s.map_mul_left (lift z) 1
    rwa [hlift, mul_one] at this
  have hsr (z : A) : s z = s 1 * lift z := by
    have := s.map_mul_right 1 (lift z)
    rwa [hlift, one_mul] at this
  obtain ⟨a, -, ha⟩ : (1 : Module.End E V) ∈ s '' (L.endFiltration 0 : Set A) := by
    rw [himage 0]
    change (1 : Module.End E V).restrictScalars F ∈ L.endFiltration 0
    exact one_mem L.order
  have hinv : s 1 * lift a = 1 := (hsr a).symm.trans ha
  have hinj (z : A) (hz : s z = 0) : z = 0 := by
    have h : lift z * s 1 * lift a = 0 := by rw [← hsl, hz, zero_mul]
    rw [mul_assoc, hinv, mul_one] at h
    rw [← hlift z, h]
    rfl
  obtain ⟨y', hy', hss⟩ : s y ∈ s '' (L.endFiltration j : Set A) := by
    rw [himage j]
    exact hy
  have : y = y' := by
    have := hinj (y - y') (by rw [map_sub, hss, sub_self])
    exact (sub_eq_zero.mp this)
  rw [this]
  exact hy'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Let `V ≠ 0` and let `E` be an intermediate field whose units normalize `L`. A stratum over
`E` on a chain with the same underlying lattice sets as `L` at every index, whose element is a
scalar `c ∈ E` of exact valuation `-n`, is simple. -/
theorem isSimple_of_algebraMap {E : Type uV} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] [Nontrivial V] (L : LatticeChain 𝒪[F] F V)
    (hnorm : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (C : Stratum (subfieldIntegers F E) E V) (hC : ∀ i, (C.chain.lattice i : Set V) = L.lattice i)
    (c : E) (hb : C.b = scalarEnd c)
    (hval : C.chain.valuation C.b = (-C.n : WithTop ℤ)) : C.IsSimple := by
  rw [scalarEnd_eq_algebraMap] at hb
  have hbot : elementAlgebra C.b = ⊥ := by
    rw [hb, ← zero_add (algebraMap E (Module.End E V) c), elementAlgebra_add_algebraMap]
    exact le_bot_iff.mp (Algebra.adjoin_le (by simp))
  refine ⟨⟨?_, hval⟩, ?_⟩
  · have key : ∀ A' : Subalgebra E (Module.End E V), A' = ⊥ →
        ∃ h : IsField A', letI := h.toField
          ∀ a : A'ˣ, subfieldUnits E A' V a ∈ C.chain.stabilizer := by
      rintro A' rfl
      have hinj : Function.Injective (algebraMap E (Module.End E V)) :=
        (algebraMap E (Module.End E V)).injective
      refine ⟨(Algebra.botEquivOfInjective hinj).toMulEquiv.isField (Field.toIsField E), ?_⟩
      intro a
      obtain ⟨c', hc'⟩ := Algebra.mem_bot.mp (a : (⊥ : Subalgebra E (Module.End E V))).2
      have hc0 : c' ≠ 0 := by
        rintro rfl
        have := a.ne_zero
        apply this
        apply Subtype.ext
        simpa using hc'.symm
      have hF := hnorm (Units.mk0 c' hc0)
      intro i
      obtain ⟨j, hj⟩ := hF i
      refine ⟨j, SetLike.coe_injective ?_⟩
      rw [Submodule.map_coe, hC, hC, ← hj, Submodule.map_coe]
      congr 1
      funext v
      change ((a : (⊥ : Subalgebra E (Module.End E V))) : Module.End E V) v = c' • v
      rw [← hc']
      rfl
    exact key _ hbot
  · have : criticalExponent C.chain C.b = ⊥ := by
      unfold criticalExponent
      exact ite_eq_left hbot
    rw [this]
    exact WithBot.bot_lt_coe _

/-- Let `V` be finite-dimensional, `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F`,
`[𝔄,n,k+1,γ]` a simple stratum on `L`, `b ∈ 𝔓^{-(k+1)}` and `x ∈ 𝔓` with
`b ≡ γx - xγ (mod 𝔓^{-k})`. Assuming the conjugation statement for simple characters, a
conjugate of `[𝔄,n,k,γ]` by the unit `1 + x` of `U^1(𝔄)` gives a simple stratum `[𝔄,n,k,β']` on `L` with
`β' ≡ γ + b (mod 𝔓^{-k})`. -/
theorem exists_conj_refinement [FiniteDimensional F V] (ψF : AddChar F ℂ)
    (hConj : SimpleCharacterConjugationStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ))
    {b x : A} (hb : b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ))) (hx : x ∈ L.endFiltration 1)
    (hbx : b - (T.1.b * x - x * T.1.b) ∈ L.endFiltration (-(k : ℤ))) :
    ∃ S' : SimpleStratumAt L n k, S'.1.b - (T.1.b + b) ∈ L.endFiltration (-(k : ℤ)) := by
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  let Tk : SimpleStratumAt L n k :=
    ⟨T.1.lowerIndex k (by rw [hTr]; push_cast; omega), hTL, hTn, rfl, hTs.lowerIndex _⟩
  obtain ⟨u, hu, hux⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl (by exact_mod_cast hx)
  obtain ⟨S', hS'⟩ := exists_conj_simpleStratumAt ψF hConj hψ L n k Tk
    (L.unitFiltration_antitone (Nat.zero_le 1) hu)
  refine ⟨S', ?_⟩
  rw [hS']
  change (↑u⁻¹ : A) * T.1.b * (u : A) - (T.1.b + b) ∈ _
  have ha : T.1.b * x - x * T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) := by
    have h := sub_mem hb (L.endFiltration_antitone (by push_cast; omega) hbx)
    rwa [sub_sub_cancel] at h
  have hu1 : (↑u⁻¹ : A) - 1 ∈ L.endFiltration 1 := by
    have := (inv_mem hu).2.2
    exact_mod_cast this
  have key : (↑u⁻¹ : A) * T.1.b * (u : A) =
      (↑u⁻¹ : A) * (T.1.b * x - x * T.1.b) + T.1.b := by
    have e1 : T.1.b * x - x * T.1.b = T.1.b * (u : A) - (u : A) * T.1.b := by
      rw [hux]
      noncomm_ring
    rw [e1, mul_sub, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
    abel
  rw [key, show (↑u⁻¹ : A) * (T.1.b * x - x * T.1.b) + T.1.b - (T.1.b + b) =
      ((↑u⁻¹ : A) - 1) * (T.1.b * x - x * T.1.b) - (b - (T.1.b * x - x * T.1.b)) by noncomm_ring]
  refine sub_mem ?_ hbx
  have := L.mul_mem_endFiltration hu1 ha
  exact L.endFiltration_antitone (by push_cast; omega) this

set_option maxHeartbeats 1000000 in
/-- **BK93 (2.4.1)(ii)(c) and (iii).** Let `V` be finite-dimensional, let `[𝔄,n,k+1,γ]` and
`[𝔄,n,k,β]` be simple strata on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`, and assume that `F[γ]` is a
field. For every tame corestriction `s` relative to `F[γ]/F`, `s(β - γ)` is congruent modulo
`𝔓^{-k}` to a scalar of `F[γ]` or to the element of a simple stratum over `F[γ]` at index `k`
on a chain whose lattices have the same underlying sets as those of `L` at every index. -/
theorem exists_derived_approx [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (k : ℕ) (T : SimpleStratumAt L n ((k + 1 : ℕ) : ℤ)) (S : SimpleStratumAt L n k)
    (hSb : S.1.b - T.1.b ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)))
    (hEf : IsField (elementAlgebra T.1.b)) :
    letI := hEf.toField
    ∀ s : TameCorestriction 𝒪[F] F (elementAlgebra T.1.b) V,
      ∃ y : Module.End (elementAlgebra T.1.b) V,
        (s (S.1.b - T.1.b) - y).restrictScalars F ∈ L.endFiltration (-(k : ℤ)) ∧
        ((∃ c : elementAlgebra T.1.b, y = scalarEnd c) ∨
          ∃ C : Stratum (subfieldIntegers F (elementAlgebra T.1.b)) (elementAlgebra T.1.b) V,
            (∀ i, (C.chain.lattice i : Set V) = L.lattice i) ∧ C.r = T.1.r - 1 ∧ C.IsSimple ∧
              C.b = y) := by
  letI := hEf.toField
  intro s
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  obtain ⟨hSL, hSn, hSr, hSs⟩ := S.2
  have hlt : ((k + 1 : ℕ) : ℤ) < S.1.n := by
    have := T.1.r_lt_n
    rw [hTr, hTn] at this
    rw [hSn]
    exact this
  let S₁ : Stratum 𝒪[F] F V := { S.1 with r := ((k + 1 : ℕ) : ℤ), r_lt_n := hlt }
  have hS₁equiv : S₁.Equivalent T.1 :=
    Stratum.equivalent_of_sub_mem (S := S₁) (T := T.1) (hTL.trans hSL.symm) hTr
      (by change S.1.b - T.1.b ∈ S.1.chain.endFiltration (-((k + 1 : ℕ) : ℤ)); rw [hSL]; exact hSb)
  by_cases hcrit : criticalExponent L S.1.b < ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithBot ℤ)
  · have hS₁ : S₁.IsSimple :=
      ⟨hSs.1, by change criticalExponent S.1.chain S.1.b < _; rw [hSL]; exact hcrit⟩
    have hTS₁ : T.1.Equivalent S₁ := by
      unfold Stratum.Equivalent at hS₁equiv ⊢
      exact hS₁equiv.symm
    obtain ⟨δ₀, hδ₀⟩ := simpleStratumCorestrictionCongruence F V T.1 S₁ (hSL.trans hTL.symm)
      (hSn.trans hTn.symm) hTr.symm hTs hS₁ hTS₁ hEf s
    refine ⟨scalarEnd (-δ₀), ?_, Or.inl ⟨-δ₀, rfl⟩⟩
    have e1 : s (S.1.b - T.1.b) - scalarEnd (-δ₀) = -(s (T.1.b - S₁.b) - scalarEnd δ₀) := by
      rw [show S.1.b - T.1.b = -(T.1.b - S₁.b) from (neg_sub _ _).symm, map_neg, scalarEnd_neg]
      abel
    rw [e1]
    have e2 : (-(s (T.1.b - S₁.b) - scalarEnd δ₀)).restrictScalars F =
        -((s (T.1.b - S₁.b)).restrictScalars F - subfieldEmbedding F (elementAlgebra T.1.b) V δ₀) := by
      rw [← restrictScalars_scalarEnd]
      rfl
    rw [e2]
    refine neg_mem ?_
    rw [hTL, hTr] at hδ₀
    convert hδ₀ using 2
    push_cast
    ring
  · have hlt := hSs.2
    rw [hSL, hSr] at hlt
    have hk0 : criticalExponent L S.1.b = ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithBot ℤ) := by
      cases hc : criticalExponent L S.1.b with
      | bot => exact (hcrit (by rw [hc]; exact WithBot.bot_lt_coe _)).elim
      | coe j =>
        rw [hc] at hlt hcrit
        have h1 := WithBot.coe_lt_coe.mp hlt
        have h2 : ¬ j < -((k + 1 : ℕ) : ℤ) := fun h => hcrit (WithBot.coe_lt_coe.mpr h)
        congr 1
        push_cast at h1 h2 ⊢
        omega
    have hder := criticalDerivedStratum F V S₁ T.1 hSs.1
        (by change criticalExponent S.1.chain S.1.b = _; rw [hSL, hk0])
        (hTL.trans hSL.symm) (hTn.trans hSn.symm) hTr hTs hS₁equiv hEf s
    obtain ⟨D, hrest⟩ := hder
    obtain ⟨C, hDd, hCc, hCn, hCr, hDC, hCs⟩ := hrest
    have hDlat := hDd.2.2.2.1
    have hDr := hDd.2.2.2.2.2.1
    have hDb := hDd.2.2.2.2.2.2
    have hClat : ∀ i, (C.chain.lattice i : Set V) = L.lattice i := fun i => by
      rw [hCc, hDlat, hTL]
    refine ⟨C.b, ?_, Or.inr ⟨C, hClat, by rw [hCr, hDr], hCs, rfl⟩⟩
    have h1 : D.b - C.b ∈ C.chain.endFiltration (-C.r) := by
      have hDmem : D.b ∈ D.coset := by
        show D.b - D.b ∈ D.chain.endFiltration (-D.r)
        rw [sub_self]
        exact zero_mem _
      rw [hDC] at hDmem
      exact hDmem
    rw [hDb] at h1
    have h2 := (mem_endFiltration_restrictScalars hClat).mp h1
    rw [hCr, hDr, hTr] at h2
    convert h2 using 2
    push_cast
    ring

set_option maxHeartbeats 2000000 in
/-- **BK93 (2.2.8), (2.4.1), BK94 (1.8)**: `RefinementSimpleAt L n k` for finite-dimensional
`V`. Given a simple stratum `[𝔄,n,k+1,γ]`, a simple refinement `[𝔄,n,k,β]` of it on `L` and
`e ∈ 𝔓^{-(k+1)}` whose tame corestriction relative to `γ` is a scalar modulo `𝔓^{-k}`, some
simple stratum `[𝔄,n,k,β']` on `L` satisfies `β' ≡ β + e (mod 𝔓^{-k})`. The proof uses the
conjugation statement for simple characters, for an additive character `ψ_F` trivial on `𝔭_F`
and nontrivial on `𝔬_F`. -/
theorem refinementSimpleAt [FiniteDimensional F V] (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : RefinementSimpleAt L n k := by
  intro T S e hSb he hscal
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  have hb : (S.1.b - T.1.b) + e ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) := add_mem hSb he
  have htarget : T.1.b + ((S.1.b - T.1.b) + e) = S.1.b + e := by abel
  by_cases hnull0 : (S.1.b - T.1.b) + e ∈ L.endFiltration (-(k : ℤ))
  · refine ⟨⟨T.1.lowerIndex k (by rw [hTr]; push_cast; omega), hTL, hTn, rfl, hTs.lowerIndex _⟩, ?_⟩
    change T.1.b - (S.1.b + e) ∈ _
    rw [show T.1.b - (S.1.b + e) = -((S.1.b - T.1.b) + e) by abel]
    exact neg_mem hnull0
  obtain ⟨hEf, hEn⟩ := hTs.1.1
  letI := hEf.toField
  have : FiniteDimensional F (elementAlgebra T.1.b) :=
    Module.Finite.of_injective (elementAlgebra T.1.b).val.toLinearMap Subtype.val_injective
  obtain ⟨s⟩ := (tameCorestriction F V (elementAlgebra T.1.b)).1
  have hEnL : ∀ u : (elementAlgebra T.1.b)ˣ,
      subfieldUnits F (elementAlgebra T.1.b) V u ∈ L.stabilizer := by
    intro u
    have h := hEn u
    rwa [hTL] at h
  have hsmem : ∀ (j : ℤ), ∀ y ∈ L.endFiltration j, (s y).restrictScalars F ∈ L.endFiltration j := by
    intro j y hy
    have h := (tameCorestriction F V (elementAlgebra T.1.b)).2.2 s L hEnL j
    have h' : s y ∈ s '' (L.endFiltration j : Set A) := ⟨y, hy, rfl⟩
    rw [h] at h'
    exact h'
  have hcrit : criticalExponent L T.1.b < ((-((k : ℤ) + 1) : ℤ) : WithBot ℤ) := by
    have := hTs.2
    rw [hTL, hTr] at this
    simpa using this
  have hb' : (S.1.b - T.1.b) + e ∈ L.endFiltration (-((k : ℤ) + 1)) := by
    simpa using hb
  by_cases hnull : (s ((S.1.b - T.1.b) + e)).restrictScalars F ∈ L.endFiltration (-(k : ℤ))
  · -- the derived stratum is null
    by_cases hbot : elementAlgebra T.1.b = ⊥
    · exfalso
      apply hnull0
      refine mem_endFiltration_of_tameCorestriction_scalar (E := elementAlgebra T.1.b)
        (fun c => ?_) L hEnL s _ hnull
      have hc : (c : A) ∈ (⊥ : Subalgebra F A) := hbot ▸ c.2
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hc
      exact ⟨a, Subtype.ext ha⟩
    · have hgen := subfieldEmbedding_elementGenerator T.1.b hEf
      obtain ⟨x, hx1, hx⟩ := exists_adjoint_approx (E := elementAlgebra T.1.b) L
        (elementGenerator T.1.b) (adjoin_elementGenerator T.1.b)
        (not_exists_algebraMap_elementGenerator T.1.b hbot) hEnL s k
        (by rw [hgen]; exact hcrit) hb' hnull
      rw [hgen] at hx
      obtain ⟨S', hS'⟩ := exists_conj_refinement ψF hConj hψ L n k T hb hx1
        (by simpa [adjointMap] using hx)
      exact ⟨S', by rwa [htarget] at hS'⟩
  · -- the derived stratum is equivalent to a simple stratum
    obtain ⟨y, hy, hycase⟩ := exists_derived_approx L n k T S hSb hEf s
    obtain ⟨δ, hδ⟩ := hscal hEf s
    set w := s ((S.1.b - T.1.b) + e) with hw
    have hsadd : w = s (S.1.b - T.1.b) + s e := map_add s.toAddMonoidHom _ _
    have hres_sub : ∀ X Y : Module.End (elementAlgebra T.1.b) V,
        (X - Y).restrictScalars F = X.restrictScalars F - Y.restrictScalars F := fun X Y => rfl
    have hzdiff : (w - (y + scalarEnd δ)).restrictScalars F ∈ L.endFiltration (-(k : ℤ)) := by
      have e1 : w - (y + scalarEnd δ) = (s (S.1.b - T.1.b) - y) + (s e - scalarEnd δ) := by
        rw [hsadd]
        abel
      have e2 : ((s (S.1.b - T.1.b) - y) + (s e - scalarEnd δ)).restrictScalars F =
          (s (S.1.b - T.1.b) - y).restrictScalars F +
            ((s e).restrictScalars F - subfieldEmbedding F (elementAlgebra T.1.b) V δ) := by
        rw [← restrictScalars_scalarEnd]
        rfl
      rw [e1, e2]
      exact add_mem hy hδ
    have hwmem := hsmem _ _ hb
    have hzmem : (y + scalarEnd δ).restrictScalars F ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)) := by
      have e3 : (y + scalarEnd δ).restrictScalars F =
          w.restrictScalars F - (w - (y + scalarEnd δ)).restrictScalars F := by
        rw [hres_sub]
        abel
      rw [e3]
      exact sub_mem hwmem (L.endFiltration_antitone (by push_cast; omega) hzdiff)
    have hznot : (y + scalarEnd δ).restrictScalars F ∉ L.endFiltration (-(k : ℤ)) := by
      intro h
      apply hnull
      have := add_mem hzdiff h
      rwa [hres_sub, sub_add_cancel] at this
    let B := T.1.chain.extensionChain hEn
    have hBlat : ∀ i, (B.lattice i : Set V) = L.lattice i := fun i => by
      have h : (B.lattice i : Set V) = T.1.chain.lattice i := rfl
      rw [h, hTL]
    have hBmem : ∀ (j : ℤ) (x : Module.End (elementAlgebra T.1.b) V),
        x ∈ B.endFiltration j ↔ x.restrictScalars F ∈ L.endFiltration j :=
      fun j x => mem_endFiltration_restrictScalars hBlat
    have hr1 : -T.1.r = -((k + 1 : ℕ) : ℤ) := by rw [hTr]
    have hr2 : -(T.1.r - 1) = -(k : ℤ) := by rw [hTr]; push_cast; ring
    have hr3 : -T.1.r + 1 = -(k : ℤ) := by rw [hTr]; push_cast; ring
    have hvalw : B.valuation w = ((-T.1.r : ℤ) : WithTop ℤ) :=
      B.valuation_eq_of_mem_of_notMem ((hBmem _ _).mpr (by rw [hr1]; exact hwmem))
        (fun h => hnull (by have := (hBmem _ _).mp h; rwa [hr3] at this))
    have hvalz : B.valuation (y + scalarEnd δ) = ((-T.1.r : ℤ) : WithTop ℤ) :=
      B.valuation_eq_of_mem_of_notMem ((hBmem _ _).mpr (by rw [hr1]; exact hzmem))
        (fun h => hznot (by have := (hBmem _ _).mp h; rwa [hr3] at this))
    let D : Stratum (subfieldIntegers F (elementAlgebra T.1.b)) (elementAlgebra T.1.b) V :=
      ⟨B, T.1.r, T.1.r - 1, w, by omega, hvalw.ge⟩
    let C' : Stratum (subfieldIntegers F (elementAlgebra T.1.b)) (elementAlgebra T.1.b) V :=
      ⟨B, T.1.r, T.1.r - 1, y + scalarEnd δ, by omega, hvalz.ge⟩
    have hDC' : D.Equivalent C' :=
      Stratum.equivalent_of_sub_mem (S := D) (T := C') rfl rfl ((hBmem _ _).mpr (by
        change (w - (y + scalarEnd δ)).restrictScalars F ∈ L.endFiltration (-(T.1.r - 1))
        rw [hr2]
        exact hzdiff))
    have : Nontrivial V := L.nontrivialSpace
    have hC's : C'.IsSimple := by
      rcases hycase with ⟨c, hc⟩ | ⟨C, hClat, hCr, hCs, hCb⟩
      · refine isSimple_of_algebraMap L hEnL C' hBlat (c + δ) ?_ hvalz
        change y + scalarEnd δ = scalarEnd (c + δ)
        rw [hc, scalarEnd_add]
      · have hCchain : C.chain = B :=
          LatticeChain.eq_of_lattice_coe (fun i => (hClat i).trans (hBlat i).symm)
        refine Stratum.isSimple_of_add_algebraMap (C := C) (C' := C') hCchain.symm hCr.symm δ ?_
          hCs hvalz
        change y + scalarEnd δ = C.b + scalarEnd δ
        rw [hCb]
    have hD : T.1.IsDerivedStratum (elementAlgebra T.1.b) ((S.1.b - T.1.b) + e) s D :=
      ⟨hTs, ⟨elementGenerator T.1.b, subfieldEmbedding_elementGenerator T.1.b hEf,
        adjoin_elementGenerator T.1.b⟩, by rw [hTL, hTr]; exact hb, fun i => rfl, rfl, rfl, rfl⟩
    have hvalb : T.1.chain.valuation ((S.1.b - T.1.b) + e) = ((-T.1.r : ℤ) : WithTop ℤ) := by
      rw [hTL]
      exact L.valuation_eq_of_mem_of_notMem (by rw [hr1]; exact hb) (by rw [hr3]; exact hnull0)
    obtain ⟨T', hT'c, hT'n, hT'r, hT's, hT'coset, hT'e, hT'f, hT'k⟩ :=
      refinement F V (elementAlgebra T.1.b) T.1 _ s D C' hD hvalb rfl rfl rfl hDC' hC's
    refine ⟨⟨T', hT'c.trans hTL, hT'n.trans hTn, by rw [hT'r, hTr]; push_cast; ring, hT's⟩, ?_⟩
    have hmem : T'.b ∈ T'.coset := by
      show T'.b - T'.b ∈ T'.chain.endFiltration (-T'.r)
      rw [sub_self]
      exact zero_mem _
    rw [hT'coset] at hmem
    change T'.b - (T.1.b + ((S.1.b - T.1.b) + e)) ∈ T.1.chain.endFiltration (1 - T.1.r) at hmem
    rw [htarget, hTL, hTr] at hmem
    change T'.b - (S.1.b + e) ∈ L.endFiltration (-(k : ℤ))
    convert hmem using 2
    push_cast
    ring

end Refine

/-- **BK94 (2.3), upper half,** from the Library's statements on simple strata and simple
characters and the fibre characters `SimpleCharacterFibreCharacterStatement`. -/
theorem simpleCharacterClassCover_of_fibreCharacter
    (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    (hConj : SimpleCharacterConjugationStatement.{uF, uV})
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV})
    (hGroups : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (hRestr : SimpleCharacterRestrictionStatement.{uF, uV})
    (hCoh : SimpleCharacterCoherenceStatement.{uF, uV})
    (hTransl : SimpleCharacterTranslationStatement.{uF, uV})
    (hCov : SimpleCharacterCovarianceStatement.{uF, uV})
    (hFib : SimpleCharacterFibreCharacterStatement.{uF, uV}) :
    SimpleCharacterClassCoverStatement.{uF, uV} := by
  refine simpleCharacterClassCover_of_fibreInjection hApprox hConj hChoice hGroups hRestr ?_
  intro F _ _ _ _ V _ _ _ ψF hψ L n k hk
  exact fibreInjectionAt_of_fibreClassInjection ψF hApprox hConj hChoice hGroups hRestr hCoh
    hTransl hψ L n k hk
    (fibreClassInjectionAt_of_twist ψF hGroups hRestr hψ L n k
      (twistConjugacyAt ψF hApprox hConj hChoice hCov hψ L n k hk)
      (fibreTwistCoverAt_of ψF hψ L n k (twistDecompositionAt ψF hApprox hChoice hRestr hψ L n k)
        (hFib F V ψF hψ L n k hk) (refinementSimpleAt ψF hψ hConj L n k)))

end Langlands.BushnellKutzko
