import Langlands.BushnellKutzko.CriticalDerivedLayerBasis

/-! # The residual field acting on successive layers -/

noncomputable section

open ValuativeRel IsLocalRing Polynomial
open scoped BigOperators

namespace Langlands.BushnellKutzko.CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓒 : LatticeChain 𝒪[F] F V)

local notation "O" => 𝒪[F]
local notation "k" => ResidueField 𝒪[F]
local notation "Pᶜ" => 𝓒.endFiltration
local notation "L" => 𝓒.lattice

/-- The order acts on a successive layer by endomorphisms linear over the residue field. -/
def residueLayerHom (i : ℤ) : 𝓒.order →ₐ[O] Module.End k (𝓒.Layer i) where
  toFun x :=
    { toFun := 𝓒.layerAction x i
      map_add' := map_add _
      map_smul' := fun c q => by
        obtain ⟨r, rfl⟩ := residue_surjective c
        change 𝓒.layerAction x i ((algebraMap O k r) • q) =
          (algebraMap O k r) • 𝓒.layerAction x i q
        simp only [algebraMap_smul, map_smul] }
  map_zero' := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓒.intervalMk_surjective i (i + 1) q
    exact (𝓒.intervalMk_eq_zero_iff _).mpr (zero_mem _)
  map_one' := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓒.intervalMk_surjective i (i + 1) q
    rfl
  map_add' x y := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓒.intervalMk_surjective i (i + 1) q
    let Q := (𝓒.intervalSubmodule i (i + 1)).mkQ
    exact Q.map_add (⟨x.val v, 𝓒.mem_order.mp x.prop i v hv⟩ : L i)
      ⟨y.val v, 𝓒.mem_order.mp y.prop i v hv⟩
  map_mul' x y := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓒.intervalMk_surjective i (i + 1) q
    rfl
  commutes' r := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, hv, rfl⟩ := 𝓒.intervalMk_surjective i (i + 1) q
    change (𝓒.intervalSubmodule i (i + 1)).mkQ (r • (⟨v, hv⟩ : L i)) =
      (algebraMap O k r) • (𝓒.intervalMk i (i + 1) v hv)
    rw [algebraMap_smul]
    exact map_smul _ _ _

@[simp] theorem residueLayerHom_mk (i : ℤ) (x : 𝓒.order) (v : V) (hv : v ∈ L i) :
    residueLayerHom 𝓒 i x (𝓒.intervalMk i (i + 1) v hv) =
      𝓒.intervalMk i (i + 1) (x.val v) (𝓒.mem_order.mp x.prop i v hv) := rfl

theorem residueLayerHom_eq_zero (i : ℤ) {x : 𝓒.order} (hx : x.val ∈ Pᶜ 1) :
    residueLayerHom 𝓒 i x = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, hv, rfl⟩ := 𝓒.intervalMk_surjective i (i + 1) q
  exact (𝓒.intervalMk_eq_zero_iff _).mpr (hx i v hv)

/-- A shifting unit induces a residue-linear equivalence on the layers. -/
def residueLayerEquiv (g : 𝓒.stabilizer) (i j : ℤ) (h : j = i + 𝓒.stabilizerValuation g) :
    𝓒.Layer i ≃ₗ[k] 𝓒.Layer j :=
  { (𝓒.stabilizerLayerEquiv g i j h).toEquiv with
    map_add' := map_add (𝓒.stabilizerLayerEquiv g i j h)
    map_smul' := fun c q => by
      obtain ⟨r, rfl⟩ := residue_surjective c
      change (𝓒.stabilizerLayerEquiv g i j h) ((algebraMap O k r) • q) =
        (algebraMap O k r) • (𝓒.stabilizerLayerEquiv g i j h) q
      simp only [algebraMap_smul, map_smul] }

@[simp] theorem residueLayerEquiv_mk (g : 𝓒.stabilizer) {i j : ℤ}
    (h : j = i + 𝓒.stabilizerValuation g) (v : V) (hv : v ∈ L i) :
    residueLayerEquiv 𝓒 g i j h (𝓒.intervalMk i (i + 1) v hv) =
      𝓒.intervalMk j (j + 1) ((g.val : Module.End F V) v)
        (h.symm ▸ (𝓒.mem_lattice_stabilizer_iff g i v).mpr hv) := rfl

section PolynomialAction

variable (P : Polynomial 𝒪[F]) (z : 𝓒.order)
  (hz : aeval z.val (P.map (algebraMap 𝒪[F] F)) ∈ 𝓒.endFiltration 1)

local notation "p" => Polynomial.map (residue 𝒪[F]) P

include hz in
/-- The reduction of the polynomial kills the action of the normalized endomorphism. -/
theorem aeval_residueLayerHom_eq_zero (i : ℤ) :
    aeval (residueLayerHom 𝓒 i z) p = 0 := by
  have h₀ : (aeval z P : Module.End F V) ∈ Pᶜ 1 := by
    rw [aeval_subalgebra_coe, ← aeval_map_algebraMap (A := F)]
    exact hz
  calc
    aeval (residueLayerHom 𝓒 i z) p = residueLayerHom 𝓒 i (aeval z P) :=
      (map_aeval_eq_aeval_map (φ := residue O) (ψ := (residueLayerHom 𝓒 i).toRingHom)
        (RingHom.ext fun r => ((residueLayerHom 𝓒 i).commutes r).symm) P z).symm
    _ = 0 := residueLayerHom_eq_zero 𝓒 i h₀

/-- The action of the polynomial quotient, sending its root to the action of `z`. -/
def layerRootHom (i : ℤ) : AdjoinRoot p →ₐ[k] Module.End k (𝓒.Layer i) :=
  Ideal.Quotient.liftₐ _ (aeval (residueLayerHom 𝓒 i z)) (by
    intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [map_mul, aeval_residueLayerHom_eq_zero 𝓒 P z hz, zero_mul])

@[simp] theorem layerRootHom_root (i : ℤ) :
    layerRootHom 𝓒 P z hz i (AdjoinRoot.root p) = residueLayerHom 𝓒 i z := by
  change (aeval (residueLayerHom 𝓒 i z)) X = _
  simp

/-- The action by the polynomial quotient supplies scalars on the layer. -/
abbrev layerRootModule (i : ℤ) : Module (AdjoinRoot p) (𝓒.Layer i) :=
  Module.compHom _ (layerRootHom 𝓒 P z hz i).toRingHom

theorem layerRootTower (i : ℤ) :
    letI := layerRootModule 𝓒 P z hz i
    IsScalarTower k (AdjoinRoot p) (𝓒.Layer i) := by
  let := layerRootModule 𝓒 P z hz i
  apply IsScalarTower.of_algebraMap_smul
  intro a q
  change layerRootHom 𝓒 P z hz i (algebraMap k (AdjoinRoot p) a) q = a • q
  rw [(layerRootHom 𝓒 P z hz i).commutes]
  rfl

/-- The root-power basis of the residue extension, indexed by the degree before reduction. -/
def residuePowerBasis (hP : P.Monic) : Module.Basis (Fin P.natDegree) k (AdjoinRoot p) :=
  (AdjoinRoot.powerBasis' (hP.map (residue O))).basis.reindex
    (finCongr (hP.natDegree_map (residue O)))

@[simp] theorem residuePowerBasis_apply (hP : P.Monic) (l : Fin P.natDegree) :
    residuePowerBasis P hP l = AdjoinRoot.root p ^ (l : ℕ) := by
  rw [residuePowerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- A power of `z` on a representative induces multiplication by the corresponding root
power on the layer. -/
theorem root_pow_smul_mk (i : ℤ) (l : ℕ) (v : V) (hv : v ∈ L i) :
    letI := layerRootModule 𝓒 P z hz i
    (AdjoinRoot.root p ^ l) • 𝓒.intervalMk i (i + 1) v hv =
      𝓒.intervalMk i (i + 1) ((z.val ^ l) v) (𝓒.mem_order.mp (z ^ l).prop i v hv) := by
  change (layerRootHom 𝓒 P z hz i (AdjoinRoot.root p ^ l)) _ = _
  rw [map_pow, layerRootHom_root, ← map_pow]
  rfl

/-- If an order element is injective on all the layers, it is a degree-zero shifting unit. -/
theorem exists_unit_of_injective_layers {x : 𝓒.order}
    (h : ∀ i, Function.Injective (residueLayerHom 𝓒 i x)) :
    ∃ u : (Module.End F V)ˣ, (u : Module.End F V) = x.val ∧ Shifts 𝓒 0 u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hm (i : ℤ) (v : V) : x.val v ∈ L i ↔ v ∈ L i := by
    refine ⟨fun hxi => ?_, 𝓒.mem_order.mp x.prop i v⟩
    by_contra hvi
    have hv₀ : v ≠ 0 := fun hv => hvi (hv ▸ zero_mem _)
    obtain ⟨j, hj, hj'⟩ := exists_exact_lattice_depth 𝓒 hϖ hv₀
    have hji : j + 1 ≤ i := by
      by_contra! hk
      exact hvi (𝓒.antitone (by omega) hj)
    have hzero : residueLayerHom 𝓒 j x (𝓒.intervalMk j (j + 1) v hj) = 0 := by
      rw [residueLayerHom_mk, 𝓒.intervalMk_eq_zero_iff]
      exact 𝓒.antitone hji hxi
    exact hj' ((𝓒.intervalMk_eq_zero_iff hj).mp ((h j) (hzero.trans (map_zero _).symm)))
  have hinj : Function.Injective x.val := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro v hv
    rw [Submodule.mem_bot]
    apply 𝓒.lattice_eq_zero_of_forall
    intro i
    exact (hm i v).mp (by rw [LinearMap.mem_ker.mp hv]; exact zero_mem _)
  let : FiniteDimensional F V := 𝓒.finiteDimensional
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.ofBijective x.val ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩)
  have hu : (u : Module.End F V) = x.val := rfl
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hu, 𝓒.mem_endFiltration, add_zero] using 𝓒.mem_order.mp x.prop
  · intro i v hv
    rw [neg_zero, add_zero]
    apply (hm i _).mp
    rwa [← hu, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

/-- An integral linear combination of powers is an element of the order. -/
def integralPowerSum (x : 𝓒.order) {n : ℕ} (r : Fin n → 𝒪[F]) : 𝓒.order :=
  ∑ l, algebraMap O 𝓒.order (r l) * x ^ (l : ℕ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem integralPowerSum_val (x : 𝓒.order) {n : ℕ} (r : Fin n → 𝒪[F]) :
    (integralPowerSum 𝓒 x r).val = ∑ l, (r l : F) • (x.val ^ (l : ℕ)) := by
  change 𝓒.order.val (∑ l, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul, map_pow, AlgHom.commutes]
  apply LinearMap.ext
  intro v
  rfl

include hz in
/-- An integral power sum of length the residual degree and with a nonzero coefficient
in the residue field is a shifting unit. -/
theorem exists_unit_of_primitive_powerSum (hP : P.Monic) (hp : Irreducible p)
    (r : Fin P.natDegree → 𝒪[F]) (hr : ∃ l, residue O (r l) ≠ 0) :
    ∃ u : (Module.End F V)ˣ, (u : Module.End F V) = (integralPowerSum 𝓒 z r).val ∧
      Shifts 𝓒 0 u := by
  let : Fact (Irreducible (P.map (residue 𝒪[F]))) := ⟨hp⟩
  let b := residuePowerBasis P hP
  let a : AdjoinRoot p := ∑ l, residue O (r l) • b l
  have ha : a ≠ 0 := by
    obtain ⟨l, hl⟩ := hr
    intro h
    exact hl (Fintype.linearIndependent_iff.mp b.linearIndependent _ h l)
  apply exists_unit_of_injective_layers
  intro i
  let f := layerRootHom 𝓒 P z hz i
  have heq : f a = residueLayerHom 𝓒 i (integralPowerSum 𝓒 z r) := by
    simp only [a, b, integralPowerSum, map_sum, map_mul, map_pow,
      residuePowerBasis_apply, layerRootHom_root, AlgHom.commutes, Algebra.smul_def, f]
    rfl
  rw [← heq]
  let u := Units.map f.toMonoidHom (Units.mk0 a ha)
  exact (LinearMap.GeneralLinearGroup.toLinearEquiv u).injective

end PolynomialAction

end Langlands.BushnellKutzko.CriticalDerived
