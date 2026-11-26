import Langlands.BushnellKutzko.NonsplitFundamentalSimpleLayers
import Mathlib.RingTheory.AdjoinRoot

/-! # The residue centralizer of a translating element

Let `S = [𝓛, n, r, b]` be a stratum over a discrete valuation ring `O` with fraction field `K`,
where `b` is a unit translating the chain by `-n`, and let `(g, h, k, u, v)` be Bézout shift
parameters for `(e(𝓛), -n)`. The residual element `y = b^h ϖ^{-k}` has shift zero and
`τ = b^u ϖ^v` has shift `g`. The residue centralizer `ℛ` of `S` is isomorphic to the product,
over `0 ≤ j < g`, of the centralizers of the action of `y` on the layers `L_j / L_{j+1}`
(`residueCentralizerEquiv`). For a polynomial `P` over `O` whose reduction is irreducible, `ℛ`
is semisimple if `P(y) ∈ 𝔓` (`isSemisimpleRing_of_aeval_mem`); conversely, if `ℛ` is
semisimple and `P(y)^m ∈ 𝔓`, then `P(y) ∈ 𝔓` (`aeval_mem_of_isSemisimpleRing`).
-/

noncomputable section

open Polynomial

namespace Langlands.BushnellKutzko.NonsplitSimple

open LatticeChain CriticalDerived

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- Scalars in the Jacobson radical lie in `𝔓`. -/
theorem algebraMap_mem_firstFiltrationIdeal (𝓛 : LatticeChain O K V) {a : O}
    (ha : a ∈ Ring.jacobson O) : algebraMap O 𝓛.order a ∈ 𝓛.firstFiltrationIdeal := by
  change algebraMap O (Module.End K V) a ∈ 𝓛.endFiltration 1
  apply 𝓛.endFiltration_antitone (b := (𝓛.period : ℤ)) (by exact_mod_cast 𝓛.period_pos)
  intro i v hv
  rw [𝓛.lattice_add_period]
  simpa only [Module.algebraMap_end_apply] using Submodule.smul_mem_smul ha hv

/-- A polynomial with coefficients in the Jacobson radical, evaluated in the order, lies in
`𝔓`. -/
theorem aeval_mem_firstFiltrationIdeal (𝓛 : LatticeChain O K V) (x : 𝓛.order) {r : O[X]}
    (hr : ∀ i, r.coeff i ∈ Ring.jacobson O) : aeval x r ∈ 𝓛.firstFiltrationIdeal := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (algebraMap_mem_firstFiltrationIdeal 𝓛 (hr i))

section Stratum

variable (S : Stratum O K V) {B : (Module.End K V)ˣ} (hB : Shifts S.chain (-S.n) B)

/-- The element `b` as a translation of the chain. -/
abbrev bStab : S.chain.stabilizer := ⟨B, hB.mem_stabilizer⟩

/-- The element `b` translates the chain by `-n`. -/
theorem bStab_shift : S.chain.stabilizerValuation (bStab S hB) = -S.n :=
  hB.stabilizerValuation_eq

/-- Membership in the residue centralizer is commutation of layer actions with `b`. -/
theorem mem_residueCentralizer_iff_commutes (hb : S.b = (B : Module.End K V))
    (x : S.chain.order) :
    Ideal.Quotient.mk _ x ∈ S.residueCentralizer ↔
      S.chain.LayerFamilyCommutes (S.chain.layerAction x) (bStab S hB) := by
  have hbS : S.b ∈ S.chain.endFiltration (-S.n) := hb ▸ hB.1
  rw [S.mk_mem_residueCentralizer_iff hbS, S.chain.layerAction_commutes_iff, bStab_shift, hb,
    show -S.n + 1 = 1 - S.n by ring]

end Stratum

section Residue

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
  (S : Stratum O K V) {B : (Module.End K V)ˣ} (hB : Shifts S.chain (-S.n) B)
  {ϖ : O} (hϖ : Irreducible ϖ) (N : ShiftParameters S.chain.period (-S.n))

/-- The normalized element `b^h ϖ^{-k}` of shift zero. -/
def residualStab : S.chain.stabilizer :=
  N.residual (bStab S hB) (S.chain.uniformizerStabilizer hϖ)

/-- The element `b^u ϖ^v` of shift `g`. -/
def shiftStab : S.chain.stabilizer :=
  N.shift (bStab S hB) (S.chain.uniformizerStabilizer hϖ)

/-- The element `b` commutes with the uniformizer. -/
theorem commute_bStab_uniformizer :
    Commute (bStab S hB) (S.chain.uniformizerStabilizer hϖ) := by
  apply Subtype.ext
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  change (B : Module.End K V) ((algebraMap O K ϖ) • v) =
    (algebraMap O K ϖ) • (B : Module.End K V) v
  rw [map_smul]

/-- The residual element has shift zero. -/
theorem residualStab_shift : S.chain.stabilizerValuation (residualStab S hB hϖ N) = 0 := by
  rw [residualStab, ShiftParameters.residual, S.chain.stabilizerValuation_mul,
    stabilizerValuation_zpow, stabilizerValuation_zpow, bStab_shift,
    S.chain.uniformizerStabilizer_shift]
  exact N.residual_degree

/-- The element `b^u ϖ^v` has shift `g`. -/
theorem shiftStab_shift : S.chain.stabilizerValuation (shiftStab S hB hϖ N) = N.g := by
  rw [shiftStab, ShiftParameters.shift, S.chain.stabilizerValuation_mul,
    stabilizerValuation_zpow, stabilizerValuation_zpow, bStab_shift,
    S.chain.uniformizerStabilizer_shift]
  exact N.shift_degree

/-- The residual and shift elements commute. -/
theorem commute_residualStab_shiftStab :
    Commute (residualStab S hB hϖ N) (shiftStab S hB hϖ N) :=
  N.residual_commutes_shift (commute_bStab_uniformizer S hB hϖ)

/-- The residual element as an element of the order. -/
def residualOrder : S.chain.order :=
  ⟨_, mem_order_of_shift_zero S.chain _ (residualStab_shift S hB hϖ N)⟩

theorem coe_residualOrder :
    (residualOrder S hB hϖ N : Module.End K V) =
      (((residualStab S hB hϖ N).val : (Module.End K V)ˣ) : Module.End K V) :=
  rfl

/-- On each layer, the residual element acts through the order. -/
theorem stabilizerLayerEquiv_residualStab (j : ℤ)
    (h : j = j + S.chain.stabilizerValuation (residualStab S hB hϖ N)) (q : S.chain.Layer j) :
    S.chain.stabilizerLayerEquiv (residualStab S hB hϖ N) j j h q =
      S.chain.layerAction (residualOrder S hB hϖ N) j q :=
  stabilizerLayerEquiv_eq_layerAction S.chain _ (residualStab_shift S hB hϖ N) j h q

/-- The centralizer of the residual element on the layer at `j`. -/
abbrev layerCentralizer (j : ℤ) : Subalgebra O (Module.End O (S.chain.Layer j)) :=
  Subalgebra.centralizer O ({S.chain.layerAction (residualOrder S hB hϖ N) j} : Set _)

/-- Families commuting with `b` and `ϖ` commute with the residual and shift elements. -/
theorem residual_shift_mem {D : ∀ i : ℤ, Module.End O (S.chain.Layer i)}
    (hb : bStab S hB ∈ S.chain.layerCommutingSubgroup D)
    (hπ : S.chain.uniformizerStabilizer hϖ ∈ S.chain.layerCommutingSubgroup D) :
    residualStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup D ∧
      shiftStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup D :=
  ⟨mul_mem (zpow_mem hb _) (zpow_mem hπ _), mul_mem (zpow_mem hb _) (zpow_mem hπ _)⟩

/-- Families commuting with the residual and shift elements commute with `b` and `ϖ`. -/
theorem bStab_uniformizer_mem {D : ∀ i : ℤ, Module.End O (S.chain.Layer i)}
    (hz : residualStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup D)
    (ht : shiftStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup D) :
    bStab S hB ∈ S.chain.layerCommutingSubgroup D ∧
      S.chain.uniformizerStabilizer hϖ ∈ S.chain.layerCommutingSubgroup D := by
  have hc := commute_bStab_uniformizer S hB hϖ
  refine ⟨?_, ?_⟩
  · rw [← N.reconstruct hc]
    exact mul_mem (zpow_mem ht _) (zpow_mem hz _)
  · have h := N.shift_carry hc
    rw [eq_mul_inv_of_mul_eq h.symm]
    exact mul_mem (pow_mem ht _) (inv_mem (zpow_mem hz _))

variable (hb : S.b = (B : Module.End K V))
include hb

/-- Layer actions of lifts of residue-centralizer elements commute with the residual and shift
elements. -/
theorem layerCommutes_of_mem (x : S.chain.order)
    (hx : Ideal.Quotient.mk _ x ∈ S.residueCentralizer) :
    residualStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup (S.chain.layerAction x) ∧
      shiftStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup (S.chain.layerAction x) :=
  residual_shift_mem S hB hϖ N ((mem_residueCentralizer_iff_commutes S hB hb x).mp hx)
    (S.chain.layerAction_commutes_uniformizer hϖ x)

/-- The action of a residue-centralizer element on a layer commutes with the residual element. -/
theorem residueLayerHom_mem (x : S.residueCentralizer) (j : ℤ) :
    residueLayerHom S.chain j x.1 ∈ layerCentralizer S hB hϖ N j := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hz := (layerCommutes_of_mem S hB hϖ N hb x₀ hx).1
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ rfl
  refine LinearMap.ext fun q => ?_
  have hj : j = j + S.chain.stabilizerValuation (residualStab S hB hϖ N) := by
    rw [residualStab_shift, add_zero]
  have h := hz j j hj q
  rw [stabilizerLayerEquiv_residualStab, stabilizerLayerEquiv_residualStab] at h
  exact h

set_option synthInstance.maxHeartbeats 200000 in
include hB hϖ in
/-- Elements of the residue centralizer are determined by their action on the layers at
`0 ≤ j < g`. -/
theorem residueLayer_injective {x y : S.chain.order ⧸ S.chain.firstFiltrationIdeal}
    (hx : x ∈ S.residueCentralizer) (hy : y ∈ S.residueCentralizer)
    (h : ∀ j : ℤ, 0 ≤ j → j < N.g → residueLayerHom S.chain j x = residueLayerHom S.chain j y) :
    x = y := by
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hxy : Ideal.Quotient.mk S.chain.firstFiltrationIdeal (x₀ - y₀) ∈ S.residueCentralizer := by
    rw [map_sub]
    exact sub_mem hx hy
  have ht := (layerCommutes_of_mem S hB hϖ N hb (x₀ - y₀) hxy).2
  have hzero : ∀ i, S.chain.layerAction (x₀ - y₀) i = 0 := by
    apply eq_zero_of_commutes S.chain (shiftStab S hB hϖ N) N.g_pos (shiftStab_shift S hB hϖ N)
      _ ht
    intro r hr₀ hr
    have := h r hr₀ hr
    rw [residueLayerHom_mk, residueLayerHom_mk] at this
    change layerHom S.chain r (x₀ - y₀) = 0
    rw [map_sub, sub_eq_zero]
    exact this
  exact Ideal.Quotient.eq.mpr ((layerAction_eq_zero_iff S.chain _).mp hzero)

/-- Every family of commuting layer endomorphisms at `0 ≤ j < g` comes from the residue
centralizer. -/
theorem residueLayer_surjective
    (c : ∀ j : Set.Ico (0 : ℤ) N.g, layerCentralizer S hB hϖ N j) :
    ∃ x ∈ S.residueCentralizer, ∀ j : Set.Ico (0 : ℤ) N.g,
      residueLayerHom S.chain j x = (c j : Module.End O (S.chain.Layer j)) := by
  classical
  let c' : ∀ r : ℤ, Module.End O (S.chain.Layer r) := fun r =>
    if h : r ∈ Set.Ico (0 : ℤ) N.g then ((c ⟨r, h⟩ : layerCentralizer S hB hϖ N r) :
      Module.End O (S.chain.Layer r)) else 0
  have hc' : ∀ r (h : r ∈ Set.Ico (0 : ℤ) N.g), c' r = c ⟨r, h⟩ := fun r h => dite_eq_left h
  let t := shiftStab S hB hϖ N
  have ht := shiftStab_shift S hB hϖ N
  let D := extendFamily S.chain t ht c'
  have hDt : t ∈ S.chain.layerCommutingSubgroup D :=
    extendFamily_commutes S.chain t N.g_pos ht c'
  have hDz : residualStab S hB hϖ N ∈ S.chain.layerCommutingSubgroup D := by
    apply extendFamily_commutes_of_commute S.chain t N.g_pos ht c' _
      (residualStab_shift S hB hϖ N) (commute_residualStab_shiftStab S hB hϖ N)
    intro r hr₀ hr h q
    rw [stabilizerLayerEquiv_residualStab, stabilizerLayerEquiv_residualStab, hc' r ⟨hr₀, hr⟩]
    have hmem := (c ⟨r, hr₀, hr⟩).2
    rw [Subalgebra.mem_centralizer_iff] at hmem
    exact LinearMap.congr_fun (hmem _ rfl) q
  obtain ⟨hDb, hDπ⟩ := bStab_uniformizer_mem S hB hϖ N hDz hDt
  obtain ⟨x₀, hx₀⟩ := S.chain.exists_order_lift_layers hϖ D hDπ
  have hlx : S.chain.layerAction x₀ = D := funext hx₀
  have hmem : Ideal.Quotient.mk _ x₀ ∈ S.residueCentralizer := by
    rw [mem_residueCentralizer_iff_commutes S hB hb, hlx]
    exact hDb
  refine ⟨_, hmem, ?_⟩
  rintro ⟨j, hj⟩
  rw [residueLayerHom_mk, hx₀]
  exact (extendFamily_of_mem S.chain t ht c' hj.1 hj.2).trans (hc' j hj)

set_option synthInstance.maxHeartbeats 200000 in
/-- The residue centralizer is isomorphic to the product of the centralizers of the residual
element on the layers at `0 ≤ j < g`. -/
def residueCentralizerEquiv :
    S.residueCentralizer ≃+* ∀ j : Set.Ico (0 : ℤ) N.g, layerCentralizer S hB hϖ N j where
  toFun x j := ⟨residueLayerHom S.chain j x.1, residueLayerHom_mem S hB hϖ N hb x j⟩
  invFun c := ⟨(residueLayer_surjective S hB hϖ N hb c).choose,
    (residueLayer_surjective S hB hϖ N hb c).choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    apply residueLayer_injective S hB hϖ N hb
      (residueLayer_surjective S hB hϖ N hb _).choose_spec.1 x.2
    intro j hj₀ hj
    exact (residueLayer_surjective S hB hϖ N hb _).choose_spec.2 ⟨j, hj₀, hj⟩
  right_inv c := by
    funext j
    apply Subtype.ext
    exact (residueLayer_surjective S hB hϖ N hb c).choose_spec.2 j
  map_mul' x y := by
    funext j
    exact Subtype.ext (map_mul (residueLayerHom S.chain j) x.1 y.1)
  map_add' x y := by
    funext j
    exact Subtype.ext (map_add (residueLayerHom S.chain j) x.1 y.1)

omit hb in
/-- Polynomials in the residual element act on layers through the layer action. -/
theorem aeval_layerAction (P : O[X]) (j : ℤ) :
    aeval (S.chain.layerAction (residualOrder S hB hϖ N) j) P =
      S.chain.layerAction (aeval (residualOrder S hB hϖ N) P) j :=
  aeval_algHom_apply (layerHom S.chain j) _ P

omit hb in
/-- If a lift `P` of an irreducible residue polynomial kills the residual element modulo `𝔓`,
then each layer centralizer is semisimple. -/
theorem isSemisimpleRing_layerCentralizer {P : O[X]}
    (hP : Irreducible (P.map (IsLocalRing.residue O)))
    (hPz : aeval (residualOrder S hB hϖ N) P ∈ S.chain.firstFiltrationIdeal) (j : ℤ) :
    IsSemisimpleRing (layerCentralizer S hB hϖ N j) := by
  have := Fact.mk hP
  let f : O[X] →+* AdjoinRoot (P.map (IsLocalRing.residue O)) :=
    (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (IsLocalRing.residue O))
  have hf : Function.Surjective f :=
    (AdjoinRoot.mk_surjective).comp
      (Polynomial.map_surjective _ IsLocalRing.residue_surjective)
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have := (S.chain.isLattice j).fg
  have : Module.Finite O (S.chain.lattice j) := Module.Finite.iff_fg.mpr this
  apply isSemisimpleRing_centralizer _ (RingHom.ker f)
  intro q hq
  rw [RingHom.mem_ker] at hq
  change AdjoinRoot.mk _ (q.map (IsLocalRing.residue O)) = 0 at hq
  obtain ⟨s', hs'⟩ := AdjoinRoot.mk_eq_zero.mp hq
  obtain ⟨s, rfl⟩ := Polynomial.map_surjective _ IsLocalRing.residue_surjective s'
  have hr : ∀ i, (q - P * s).coeff i ∈ Ring.jacobson O := by
    intro i
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, hs', sub_self,
      Polynomial.coeff_zero]
  have hmem : aeval (residualOrder S hB hϖ N) q ∈ S.chain.firstFiltrationIdeal := by
    have h := add_mem (Ideal.mul_mem_right (aeval (residualOrder S hB hϖ N) s) _ hPz)
      (aeval_mem_firstFiltrationIdeal S.chain (residualOrder S hB hϖ N) hr)
    rwa [← map_mul, ← map_add, add_sub_cancel] at h
  rw [aeval_layerAction]
  exact (layerAction_eq_zero_iff S.chain _).mpr hmem j

include hB hϖ in
set_option synthInstance.maxHeartbeats 200000 in
/-- If the residual element satisfies `P` modulo `𝔓`, the residue centralizer is semisimple. -/
theorem isSemisimpleRing_of_aeval_mem {P : O[X]}
    (hP : Irreducible (P.map (IsLocalRing.residue O)))
    (hPz : aeval (residualOrder S hB hϖ N) P ∈ S.chain.firstFiltrationIdeal) :
    IsSemisimpleRing S.residueCentralizer := by
  have : ∀ j : Set.Ico (0 : ℤ) N.g, IsSemisimpleRing (layerCentralizer S hB hϖ N j) :=
    fun j => isSemisimpleRing_layerCentralizer S hB hϖ N hP hPz j
  let : Ring (∀ j : Set.Ico (0 : ℤ) N.g, layerCentralizer S hB hϖ N j) :=
    @Pi.ring _ _ (fun _ => inferInstance)
  exact (residueCentralizerEquiv S hB hϖ N hb).symm.isSemisimpleRing

include hB hϖ in
set_option synthInstance.maxHeartbeats 200000 in
/-- Conversely, semisimplicity of the residue centralizer forces `P` to kill the residual
element modulo `𝔓` when some power of `P` does. -/
theorem aeval_mem_of_isSemisimpleRing [IsSemisimpleRing S.residueCentralizer] {P : O[X]}
    {m : ℕ} (hPm : aeval (residualOrder S hB hϖ N) P ^ m ∈ S.chain.firstFiltrationIdeal) :
    aeval (residualOrder S hB hϖ N) P ∈ S.chain.firstFiltrationIdeal := by
  classical
  let : Ring (∀ j : Set.Ico (0 : ℤ) N.g, layerCentralizer S hB hϖ N j) :=
    @Pi.ring _ _ (fun _ => inferInstance)
  have hpi : IsSemisimpleRing (∀ j : Set.Ico (0 : ℤ) N.g, layerCentralizer S hB hϖ N j) :=
    (residueCentralizerEquiv S hB hϖ N hb).isSemisimpleRing
  set z := residualOrder S hB hϖ N
  set w := aeval z P
  have hzero : ∀ r : ℤ, 0 ≤ r → r < N.g → S.chain.layerAction w r = 0 := by
    intro r hr₀ hr
    let j : Set.Ico (0 : ℤ) N.g := ⟨r, hr₀, hr⟩
    have hj : IsSemisimpleRing (layerCentralizer S hB hϖ N j) :=
      RingHom.isSemisimpleRing_of_surjective
        (Pi.evalRingHom (fun j : Set.Ico (0 : ℤ) N.g => layerCentralizer S hB hϖ N j) j)
        (fun c => ⟨Pi.single j c, by simp⟩)
    let φ := S.chain.layerAction z r
    have hφ : φ ∈ layerCentralizer S hB hϖ N j := by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      rfl
    let w' : layerCentralizer S hB hϖ N j := aeval (⟨φ, hφ⟩ : layerCentralizer S hB hϖ N j) P
    have hw' : (w' : Module.End O (S.chain.Layer r)) = aeval φ P :=
      Polynomial.aeval_subalgebra_coe P _ _
    have hnil : IsNilpotent w' := by
      refine ⟨m, Subtype.ext ?_⟩
      change (w' : Module.End O (S.chain.Layer r)) ^ m = 0
      rw [hw', aeval_layerAction]
      change layerHom S.chain r w ^ m = 0
      rw [← map_pow]
      exact (layerAction_eq_zero_iff S.chain _).mpr hPm r
    have hcomm : ∀ y, Commute w' y := by
      intro y
      apply Subtype.ext
      have hy := (Subalgebra.mem_centralizer_iff O).mp y.2 φ rfl
      change (w' : Module.End O (S.chain.Layer r)) * y = y * w'
      rw [hw']
      exact (commute_aeval_of_commute (Commute.symm hy) P).symm.eq
    have h0 := eq_zero_of_isNilpotent_of_commute (A := layerCentralizer S hB hϖ N j) hnil hcomm
    have h1 : (w' : Module.End O (S.chain.Layer r)) = 0 := congrArg Subtype.val h0
    rw [hw'] at h1
    rw [← aeval_layerAction]
    exact h1
  have hcomm : Commute (((shiftStab S hB hϖ N).val : (Module.End K V)ˣ) : Module.End K V)
      (w : Module.End K V) := by
    rw [Polynomial.aeval_subalgebra_coe]
    apply commute_aeval_of_commute
    rw [coe_residualOrder]
    exact (congrArg (fun u : S.chain.stabilizer => ((u.val : (Module.End K V)ˣ) : Module.End K V))
      (commute_residualStab_shiftStab S hB hϖ N).eq).symm
  have ht := S.chain.layerAction_commutes_of_commute w _ hcomm
  exact (layerAction_eq_zero_iff S.chain w).mp
    (eq_zero_of_commutes S.chain _ N.g_pos (shiftStab_shift S hB hϖ N) _ ht hzero)

end Residue

end Langlands.BushnellKutzko.NonsplitSimple
