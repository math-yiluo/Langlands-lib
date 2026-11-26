import Langlands.BushnellKutzko.PureStratumApproximationCommonBasis
import Langlands.BushnellKutzko.PureStratumApproximationFieldInvariants

/-! # Conjugating a perturbation of a simple stratum onto a second chain

This implements the conjugation step in the proof of BK93 (2.4.5), printed p. 68: a
perturbation `b` of a simple element whose corestriction lies in a filtration step of a second
chain normalized by the same field is conjugated, by an element of `U¹`, to a perturbation in
that step, modulo the next step of the original chain. It also records that conjugation by a
unit fixing every lattice of a chain preserves simple strata and their field invariants.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

section Conj

variable {F : Type uF} [Field F]
  {V : Type uV} [AddCommGroup V] [Module F V]

/-- Conjugation `x ↦ g⁻¹ x g` as an algebra endomorphism of `End_F(V)`. -/
def conjAlgHom (g : (Module.End F V)ˣ) : Module.End F V →ₐ[F] Module.End F V where
  toFun x := ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x * g
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' a := by
    rw [mul_assoc, Algebra.commutes a (g : Module.End F V), ← mul_assoc, Units.inv_mul, one_mul]

theorem conjAlgHom_apply (g : (Module.End F V)ˣ) (x : Module.End F V) :
    conjAlgHom g x = ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * x * g := rfl

theorem conjAlgHom_injective (g : (Module.End F V)ˣ) : Function.Injective (conjAlgHom g) := by
  intro x y h
  have h' := congrArg (fun z => (g : Module.End F V) * z * ((g⁻¹ : (Module.End F V)ˣ) :
    Module.End F V)) h
  simpa [conjAlgHom_apply, mul_assoc] using h'

theorem elementAlgebra_conj (g : (Module.End F V)ˣ) (β : Module.End F V) :
    elementAlgebra (conjAlgHom g β) = (elementAlgebra β).map (conjAlgHom g) :=
  (AlgHom.map_adjoin_singleton (conjAlgHom g) β).symm

variable [ValuativeRel F] (𝓛 : LatticeChain 𝒪[F] F V) {g : (Module.End F V)ˣ}
  (hg : (g : Module.End F V) ∈ 𝓛.endFiltration 0)
  (hg' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ 𝓛.endFiltration 0)

include hg hg' in
theorem mem_endFiltration_conj_iff {k : ℤ} {x : Module.End F V} :
    conjAlgHom g x ∈ 𝓛.endFiltration k ↔ x ∈ 𝓛.endFiltration k := by
  rw [conjAlgHom_apply]
  constructor
  · intro h
    have h1 := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hg h) hg'
    simp only [zero_add, add_zero, ← mul_assoc, Units.mul_inv, one_mul] at h1
    simpa [mul_assoc] using h1
  · intro h
    have h1 := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hg' h) hg
    simpa only [zero_add, add_zero] using h1

include hg hg' in
theorem mem_stabilizer_of_mem_order : g ∈ 𝓛.stabilizer := by
  intro i
  refine ⟨i, le_antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    simpa using hg i v hv
  · intro v hv
    refine ⟨((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) v, by simpa using hg' i v hv, ?_⟩
    change (g : Module.End F V) (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) v) = v
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

include hg hg' in
theorem valuation_conj (x : Module.End F V) :
    𝓛.valuation (conjAlgHom g x) = 𝓛.valuation x := by
  unfold LatticeChain.valuation
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : conjAlgHom g x ≠ 0 := fun h =>
      hx ((conjAlgHom_injective g) (h.trans (map_zero (conjAlgHom g)).symm))
    simp only [hx, hx', ↓reduceIte, mem_endFiltration_conj_iff 𝓛 hg hg']

include hg hg' in
theorem adjointLattice_le_conj {β : Module.End F V} {k : ℤ}
    (h : adjointLattice 𝓛 β k ≤ centralizerLattice 𝓛 β 0 ⊔ 𝓛.endFiltration 1) :
    adjointLattice 𝓛 (conjAlgHom g β) k ≤
      centralizerLattice 𝓛 (conjAlgHom g β) 0 ⊔ 𝓛.endFiltration 1 := by
  intro x hx
  rw [mem_adjointLattice_iff_mul] at hx
  let y := conjAlgHom g⁻¹ x
  have hgi : ((g⁻¹⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ 𝓛.endFiltration 0 := by
    simpa using hg
  have hxy : conjAlgHom g y = x := by
    simp [y, conjAlgHom_apply, mul_assoc]
  have hy : y ∈ adjointLattice 𝓛 β k := by
    rw [mem_adjointLattice_iff_mul]
    refine ⟨(mem_endFiltration_conj_iff 𝓛 hg hg').mp (hxy ▸ hx.1), ?_⟩
    rw [← mem_endFiltration_conj_iff 𝓛 hg hg', map_sub, map_mul, map_mul, hxy]
    exact hx.2
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp (h hy)
  rw [← hxy, ← huz, map_add]
  refine Submodule.add_mem_sup ?_ ((mem_endFiltration_conj_iff 𝓛 hg hg').mpr hz)
  rw [mem_centralizerLattice_iff_mul] at hu ⊢
  refine ⟨(mem_endFiltration_conj_iff 𝓛 hg hg').mpr hu.1, ?_⟩
  rw [← map_mul, ← map_mul, ← map_sub, hu.2, map_zero]

include hg hg' in
theorem criticalExponent_conj (β : Module.End F V) :
    criticalExponent 𝓛 (conjAlgHom g β) = criticalExponent 𝓛 β := by
  have hgi : ((g⁻¹⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ 𝓛.endFiltration 0 := by
    simpa using hg
  have hback : conjAlgHom g⁻¹ (conjAlgHom g β) = β := by
    simp [conjAlgHom_apply, mul_assoc]
  have hset : criticalIndexSet 𝓛 (conjAlgHom g β) = criticalIndexSet 𝓛 β := by
    ext k
    simp only [criticalIndexSet, Set.mem_ofPred_eq]
    refine not_congr ⟨fun h => ?_, adjointLattice_le_conj 𝓛 hg hg'⟩
    have := adjointLattice_le_conj 𝓛 hg' hgi h
    rwa [hback] at this
  have hbot : elementAlgebra (conjAlgHom g β) = ⊥ ↔ elementAlgebra β = ⊥ := by
    rw [elementAlgebra_conj]
    constructor
    · intro h
      apply Subalgebra.map_injective (conjAlgHom_injective g)
      rw [h, Algebra.map_bot]
    · intro h
      rw [h, Algebra.map_bot]
  unfold criticalExponent
  simp only [hset]
  by_cases h : elementAlgebra β = ⊥
  · have h' := hbot.mpr h
    simp only [elementAlgebra] at h h'
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ elementAlgebra (conjAlgHom g β) = ⊥ := fun h'' => h (hbot.mp h'')
    simp only [elementAlgebra] at h h'
    simp only [h, h', ↓reduceIte]

/-- The conjugate `[𝔄,n,r,g⁻¹bg]` of a stratum by a unit of its order. -/
def conjStratum (T : Stratum 𝒪[F] F V) (g : (Module.End F V)ˣ)
    (hg : (g : Module.End F V) ∈ T.chain.endFiltration 0)
    (hg' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ T.chain.endFiltration 0) :
    Stratum 𝒪[F] F V :=
  ⟨T.chain, T.n, T.r, conjAlgHom g T.b, T.r_lt_n, by
    rw [valuation_conj T.chain hg hg']
    exact T.valuation_ge⟩

/-- Conjugation by a unit of the order of a chain preserves simple strata on that chain. -/
theorem isSimple_conjStratum (T : Stratum 𝒪[F] F V) (g : (Module.End F V)ˣ)
    (hg : (g : Module.End F V) ∈ T.chain.endFiltration 0)
    (hg' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ T.chain.endFiltration 0)
    (hTs : T.IsSimple) : (conjStratum T g hg hg').IsSimple := by
  obtain ⟨⟨hf, hn⟩, hv⟩ := hTs.1
  have hN := normalizingUnits_of_isField T.chain hf hn
  have hN' : NormalizingUnits T.chain (elementAlgebra (conjAlgHom g T.b)) :=
    normalizingUnits_conj T.chain hN (mem_stabilizer_of_mem_order T.chain hg hg')
  refine ⟨⟨isField_of_normalizingUnits T.chain hN', ?_⟩, ?_⟩
  · change T.chain.valuation (conjAlgHom g T.b) = -(T.n : WithTop ℤ)
    rw [valuation_conj T.chain hg hg', hv]
  · change criticalExponent T.chain (conjAlgHom g T.b) < _
    rw [criticalExponent_conj T.chain hg hg']
    exact hTs.2

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

include hg hg' in
/-- Conjugation preserves the ramification index and residue degree of a generated field. -/
theorem elementInvariants_conj (β : Module.End F V) (hβ : NormalizingUnits 𝓛 (elementAlgebra β)) :
    elementRamificationIndex F (conjAlgHom g β) = elementRamificationIndex F β ∧
      elementResidueDegree F (conjAlgHom g β) = elementResidueDegree F β := by
  have : FiniteDimensional F V := 𝓛.finiteDimensional
  obtain ⟨hL, -⟩ := isField_of_normalizingUnits 𝓛 hβ
  have hN' : NormalizingUnits 𝓛 (elementAlgebra (conjAlgHom g β)) :=
    normalizingUnits_conj 𝓛 hβ (mem_stabilizer_of_mem_order 𝓛 hg hg')
  obtain ⟨hV, -⟩ := isField_of_normalizingUnits 𝓛 hN'
  have e : elementAlgebra β ≃ₐ[F] elementAlgebra (conjAlgHom g β) := by
    rw [elementAlgebra_conj]
    exact (elementAlgebra β).equivMapOfInjective (conjAlgHom g) (conjAlgHom_injective g)
  unfold elementRamificationIndex elementResidueDegree
  rw [dite_eq_left hV, dite_eq_left hL, dite_eq_left hV, dite_eq_left hL]
  let : Field (elementAlgebra β) := hL.toField
  let : Field (elementAlgebra (conjAlgHom g β)) := hV.toField
  exact subfieldInvariants_of_algEquiv e.symm

end Conj

section Perturbation

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The units of a field generated by the element of a pure stratum normalize its chain. -/
theorem normalized_of_generated (S : Stratum 𝒪[F] F V) (hS : S.IsPure) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤) :
    ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer := by
  obtain ⟨⟨hSfield, hSnorm⟩, -⟩ := hS
  have := S.chain.nontrivial_space
  have hSN : NormalizingUnits S.chain (elementAlgebra S.b) :=
    normalizingUnits_of_isField S.chain hSfield hSnorm
  have hℓinj : Function.Injective (subfieldEmbedding F E V) :=
    (subfieldEmbedding F E V).toRingHom.injective
  have hEmem : ∀ e : E, subfieldEmbedding F E V e ∈ elementAlgebra S.b := by
    intro e
    have h1 : subfieldEmbedding F E V e ∈
        (Algebra.adjoin F ({βE} : Set E)).map (subfieldEmbedding F E V) :=
      Subalgebra.mem_map.mpr ⟨e, by rw [hβE]; exact Algebra.mem_top, rfl⟩
    rw [AlgHom.map_adjoin_singleton, hβES] at h1
    exact h1
  intro a
  obtain ⟨g, hg, hgs⟩ := hSN _ (hEmem a)
    (fun h0 => a.ne_zero (hℓinj (h0.trans (map_zero _).symm)))
  have heq : subfieldUnits F E V a = g := Units.ext ((coe_subfieldUnits F E V a).trans hg.symm)
  rw [heq]
  exact hgs

/-- An element of `𝔓^{-r}` killed by a tame corestriction is a commutator with the simple
element `β` of an element of `𝔓^1` (BK93 (1.4.10), printed p. 38, with `k = −r−1`). -/
theorem exists_adjoint_eq_of_corestriction_eq_zero (S : Stratum 𝒪[F] F V) (hS : S.IsSimple)
    {βE : E} (hβES : subfieldEmbedding F E V βE = S.b)
    (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤) (s : TameCorestriction 𝒪[F] F E V)
    {z : Module.End F V} (hz : z ∈ S.chain.endFiltration (-S.r)) (hsz : s z = 0) :
    ∃ y ∈ S.chain.endFiltration 1, z = S.b * y - y * S.b := by
  have := S.chain.finiteDimensional
  have hE := normalized_of_generated S hS.1 hβES hβE
  have hkβ : criticalExponent S.chain S.b ≤ ((-S.r - 1 : ℤ) : WithBot ℤ) :=
    withBot_le_sub_one_of_lt hS.2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  by_cases hns : ∃ a : F, algebraMap F E a = βE
  · obtain ⟨a, ha⟩ := hns
    refine ⟨0, zero_mem _, ?_⟩
    rw [mul_zero, zero_mul, sub_zero]
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hsurj := s.surjective_of_clearing S.chain hE hϖ0
      (fun x => S.chain.exists_uniformizer_pow_mem_endFiltration hϖ x 0)
    have hker : z ∈ LinearMap.ker s.toLinearMap := by
      rw [LinearMap.mem_ker, s.toLinearMap_apply, hsz]
    rw [← s.range_adjointMap_eq_ker βE hβE hsurj] at hker
    obtain ⟨x, hx⟩ := hker
    have h0 : adjointMap F (subfieldEmbedding F E V βE) x = 0 := by
      rw [← ha]
      change subfieldEmbedding F E V (algebraMap F E a) * x -
        x * subfieldEmbedding F E V (algebraMap F E a) = 0
      rw [AlgHom.commutes, Algebra.commutes, sub_self]
    rw [← hx, h0]
  · have h := adjointExactness F V E S.chain βE hβE hns hE
    rw [hβES] at h
    have h3 := (h.2.2.2.2 s 1 (-S.r - 1) 1 hkβ le_rfl).2.2.1
    obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h3
    have hzm : z ∈ (S.chain.endFiltration (1 + (-S.r - 1))).toAddSubgroup := by
      rw [show (1 : ℤ) + (-S.r - 1) = -S.r by ring]
      exact hz
    have hs0 : (s z).restrictScalars F ∈ (⊥ : Submodule 𝒪[F] (Module.End F V)).toAddSubgroup := by
      rw [hsz]
      rfl
    obtain ⟨x, hx, hzx⟩ := (hmid z hzm).mp hs0
    refine ⟨x, centralizerLattice_mul_adjointLattice_le S.chain S.b _ _ hx, ?_⟩
    have hzx' : z - (S.b * x - x * S.b) = 0 := hzx
    exact sub_eq_zero.mp hzx'

/-- **The conjugation step of BK93 (2.4.5)**, printed p. 68. Let `[𝓛,n,r,β]` be simple with
`E = F[β]`, let `𝓛'` be a second chain normalized by `E`, and let `b ∈ 𝔓^{−r}` have
`s(b) ∈ 𝔓'^{−ρ}`. Then there are `p ∈ 𝔓^{−r} ∩ 𝔓'^{−ρ}` with `s(p) = s(b)` and `g ∈ U¹(𝓛)` with
`g(β + b)g⁻¹ ≡ β + p (mod 𝔓^{1−r})`. -/
theorem exists_conj_sub_mem (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) (𝓛' : LatticeChain 𝒪[F] F V)
    (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer) {b : Module.End F V}
    (hb : b ∈ S.chain.endFiltration (-S.r)) {ρ : ℤ}
    (hsb : (s b).restrictScalars F ∈ 𝓛'.endFiltration (-ρ)) :
    ∃ (g : (Module.End F V)ˣ) (p : Module.End F V),
      (g : Module.End F V) - 1 ∈ S.chain.endFiltration 1 ∧
      ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - 1 ∈ S.chain.endFiltration 1 ∧
      p ∈ S.chain.endFiltration (-S.r) ∧ p ∈ 𝓛'.endFiltration (-ρ) ∧ s p = s b ∧
      (g : Module.End F V) * (S.b + b) * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) -
        (S.b + p) ∈ S.chain.endFiltration (1 - S.r) := by
  have := S.chain.finiteDimensional
  have hE := normalized_of_generated S hS.1 hβES hβE
  have : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  obtain ⟨p, hp, hp', hsp⟩ := exists_corestriction_eq_of_mem S.chain 𝓛' hE hL' s hb hsb
  have hz : b - p ∈ S.chain.endFiltration (-S.r) := sub_mem hb hp
  have hsz : s (b - p) = 0 := by
    rw [map_sub]
    change s b - s p = 0
    rw [hsp, sub_self]
  obtain ⟨y, hy, hyz⟩ := exists_adjoint_eq_of_corestriction_eq_zero S hS hβES hβE s hz hsz
  obtain ⟨g, hg, hgy⟩ := S.chain.exists_mem_unitFiltration (n := 1) le_rfl hy
  have hg1 : (g : Module.End F V) - 1 ∈ S.chain.endFiltration 1 := by
    rw [hgy, add_sub_cancel_left]
    exact hy
  have hginv : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - 1 ∈ S.chain.endFiltration 1 :=
    ((S.chain.unitFiltration 1).inv_mem hg).2.2
  refine ⟨g, p, hg1, hginv, hp, hp', hsp, ?_⟩
  have hgi0 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ S.chain.endFiltration 0 := hg.2.1
  have hkey : (g : Module.End F V) * (S.b + b) - (S.b + p) * g =
      ((b - p) - (S.b * y - y * S.b)) + (y * b - p * y) := by
    rw [hgy]
    noncomm_ring
  have hmem : (g : Module.End F V) * (S.b + b) - (S.b + p) * g ∈
      S.chain.endFiltration (1 - S.r) := by
    rw [hkey, ← hyz, sub_self, zero_add]
    refine sub_mem ?_ ?_
    · have := S.chain.mul_mem_endFiltration hy hb
      rwa [show (1 : ℤ) + -S.r = 1 - S.r by ring] at this
    · have := S.chain.mul_mem_endFiltration hp hy
      rwa [show -S.r + (1 : ℤ) = 1 - S.r by ring] at this
  have h2 := S.chain.mul_mem_endFiltration hmem hgi0
  rw [add_zero, sub_mul, mul_assoc (S.b + p), Units.mul_inv, mul_one] at h2
  exact h2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An element of `U¹` of a chain fixes every lattice sandwiched between two consecutive lattices
of that chain. -/
theorem one_add_mem_order_of_sandwiched (𝓛 𝓛' : LatticeChain 𝒪[F] F V)
    (hsw : ∀ i, ∃ q, 𝓛.lattice (q + 1) ≤ 𝓛'.lattice i ∧ 𝓛'.lattice i ≤ 𝓛.lattice q)
    {y : Module.End F V} (hy : y ∈ 𝓛.endFiltration 1) : 1 + y ∈ 𝓛'.endFiltration 0 := by
  intro i v hv
  obtain ⟨q, h1, h2⟩ := hsw i
  rw [add_zero, LinearMap.add_apply, Module.End.one_apply]
  exact add_mem hv (h1 (hy q v (h2 hv)))

end Perturbation

end Langlands.BushnellKutzko.PureApproximation
