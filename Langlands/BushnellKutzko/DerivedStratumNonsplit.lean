import Langlands.BushnellKutzko.PureStratumTopNonsplitProof
import Langlands.BushnellKutzko.NonsplitFundamentalSimpleStatement
import Langlands.BushnellKutzko.LatticeChainShifts
import Langlands.BushnellKutzko.LatticeChainLayerCommutation

/-! # Nonsplit derived strata from a residue field image -/

open Polynomial

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV

namespace LatticeChain

section DVR

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- An endomorphism preserving `L₀`, on which `P(Y)^e` takes values in `ϖ L₀`, has reduced
characteristic polynomial a positive power of `P mod 𝔭`, provided the latter is monic
irreducible. The integer ring is any discrete valuation ring with fraction field `K`. -/
theorem reduceIntegralPolynomial_charpoly_eq_pow_of_dvr [FiniteDimensional K V] {ϖ : O}
    (hϖ : Irreducible ϖ) (Y : Module.End K V) (hY : ∀ v ∈ 𝓛.lattice 0, Y v ∈ 𝓛.lattice 0)
    {P : O[X]}
    (hPm : (P.map (Ideal.Quotient.mk (Ring.jacobson O))).Monic)
    (hPirr : Irreducible (P.map (Ideal.Quotient.mk (Ring.jacobson O)))) (e : ℕ)
    (hQ : ∀ v ∈ 𝓛.lattice 0, ∃ w ∈ 𝓛.lattice 0,
      aeval Y ((P ^ e).map (algebraMap O K)) v = (algebraMap O K ϖ) • w) :
    ∃ m : ℕ, 0 < m ∧ reduceIntegralPolynomial O K Y.charpoly =
      (P.map (Ideal.Quotient.mk (Ring.jacobson O))) ^ m := by
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hJ : Ring.jacobson O = IsLocalRing.maximalIdeal O :=
    IsLocalRing.ringJacobson_eq_maximalIdeal O
  have : (Ring.jacobson O).IsMaximal := by
    rw [hJ]
    infer_instance
  let : Field (O ⧸ Ring.jacobson O) := Ideal.Quotient.field _
  let L := 𝓛.lattice 0
  have : L.IsLattice K := 𝓛.isLattice 0
  let b₀ := Module.Free.chooseBasis O L
  let b := b₀.extendOfIsLattice K
  have hrepr : ∀ (x : L) i, b.repr (x : V) i = algebraMap O K (b₀.repr x i) := by
    intro x i
    have hx : (x : V) = ∑ j, algebraMap O K (b₀.repr x j) • b j := by
      have h := congrArg Subtype.val (b₀.sum_repr x)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Module.Basis.extendOfIsLattice_apply K b₀, algebraMap_smul]
    rw [hx, b.repr_sum_self]
  let A₀ : Matrix _ _ O := fun i j => b₀.repr ⟨Y (b₀ j), hY _ (b₀ j).2⟩ i
  have hA : LinearMap.toMatrixAlgEquiv b Y = A₀.map (algebraMap O K) := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.map_apply,
      Module.Basis.extendOfIsLattice_apply K b₀]
    exact hrepr ⟨Y (b₀ j), hY _ (b₀ j).2⟩ i
  have hchar : Y.charpoly = A₀.charpoly.map (algebraMap O K) := by
    rw [← LinearMap.charpoly_toMatrix Y b, ← Matrix.charpoly_map, ← hA]
    congr 1
  have hred : reduceIntegralPolynomial O K Y.charpoly =
      (A₀.map (Ideal.Quotient.mk (Ring.jacobson O))).charpoly := by
    rw [hchar, reduceIntegralPolynomial_map hinj, Matrix.charpoly_map]
  let M := aeval A₀ (P ^ e)
  have hM : M.map (algebraMap O K) =
      LinearMap.toMatrixAlgEquiv b (aeval Y ((P ^ e).map (algebraMap O K))) := by
    have h1 := aeval_matrix_map_map (algebraMap O K) A₀ (P ^ e)
    rw [← hA] at h1
    have h2 := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom Y
      ((P ^ e).map (algebraMap O K))
    exact h1.symm.trans h2
  have hMJ : ∀ i j, M i j ∈ Ring.jacobson O := by
    intro i j
    obtain ⟨w, hw, hZ⟩ := hQ (b₀ j) (b₀ j).2
    have h1 := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
      Module.Basis.extendOfIsLattice_apply K b₀, hZ,
      map_smul, Finsupp.smul_apply, smul_eq_mul,
      show w = ((⟨w, hw⟩ : L) : V) from rfl, hrepr] at h1
    have : M i j = ϖ * b₀.repr ⟨w, hw⟩ i := hinj (by rw [h1, map_mul])
    rw [this, hJ, hϖ.maximalIdeal_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have hzero : aeval (A₀.map (Ideal.Quotient.mk (Ring.jacobson O)))
      ((P.map (Ideal.Quotient.mk (Ring.jacobson O))) ^ e) = 0 := by
    rw [← Polynomial.map_pow, aeval_matrix_map_map]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hMJ i j)
  have : Nontrivial V := 𝓛.nontrivialSpace
  have : Nonempty (Module.Free.ChooseBasisIndex O L) := b.index_nonempty
  obtain ⟨m, hm, h⟩ := charpoly_eq_pow_of_aeval_pow_eq_zero _ hPm hPirr hzero
  exact ⟨m, hm, hred.trans h⟩

/-- An endomorphism preserving `L₀` has characteristic polynomial with integral coefficients:
it is the image of a monic polynomial over the integer ring. -/
theorem exists_monic_charpoly_eq_map [FiniteDimensional K V] (Y : Module.End K V)
    (hY : ∀ v ∈ 𝓛.lattice 0, Y v ∈ 𝓛.lattice 0) :
    ∃ Q : O[X], Q.Monic ∧ Y.charpoly = Q.map (algebraMap O K) := by
  classical
  let L := 𝓛.lattice 0
  have : L.IsLattice K := 𝓛.isLattice 0
  let b₀ := Module.Free.chooseBasis O L
  let b := b₀.extendOfIsLattice K
  have hrepr : ∀ (x : L) i, b.repr (x : V) i = algebraMap O K (b₀.repr x i) := by
    intro x i
    have hx : (x : V) = ∑ j, algebraMap O K (b₀.repr x j) • b j := by
      have h := congrArg Subtype.val (b₀.sum_repr x)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Module.Basis.extendOfIsLattice_apply K b₀, algebraMap_smul]
    rw [hx, b.repr_sum_self]
  let A₀ : Matrix _ _ O := fun i j => b₀.repr ⟨Y (b₀ j), hY _ (b₀ j).2⟩ i
  have hA : LinearMap.toMatrixAlgEquiv b Y = A₀.map (algebraMap O K) := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.map_apply,
      Module.Basis.extendOfIsLattice_apply K b₀]
    exact hrepr ⟨Y (b₀ j), hY _ (b₀ j).2⟩ i
  refine ⟨A₀.charpoly, A₀.charpoly_monic, ?_⟩
  rw [← LinearMap.charpoly_toMatrix Y b, ← Matrix.charpoly_map, ← hA]
  congr 1

end DVR

/-! ### Filtration arithmetic and shifting units -/

section Filtration

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

theorem pow_mem_endFiltration_mul {x : Module.End K V} {s : ℤ} (hx : x ∈ 𝓛.endFiltration s)
    (k : ℕ) : x ^ k ∈ 𝓛.endFiltration (k * s) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    exact 𝓛.order.one_mem
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact 𝓛.mul_mem_endFiltration ih hx

/-- Powers of congruent elements are congruent one step deeper. -/
theorem pow_sub_pow_mem_endFiltration {x x' : Module.End K V} {s : ℤ}
    (hx : x ∈ 𝓛.endFiltration s) (hx' : x' ∈ 𝓛.endFiltration s)
    (hd : x - x' ∈ 𝓛.endFiltration (s + 1)) (k : ℕ) :
    x ^ k - x' ^ k ∈ 𝓛.endFiltration (k * s + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, show x ^ k * x - x' ^ k * x' =
        x ^ k * (x - x') + (x ^ k - x' ^ k) * x' by noncomm_ring]
    refine add_mem ?_ ?_
    · have h := 𝓛.mul_mem_endFiltration (𝓛.pow_mem_endFiltration_mul hx k) hd
      rwa [show (k : ℤ) * s + (s + 1) = ((k + 1 : ℕ) : ℤ) * s + 1 by push_cast; ring] at h
    · have h := 𝓛.mul_mem_endFiltration ih hx'
      rwa [show (k : ℤ) * s + 1 + s = ((k + 1 : ℕ) : ℤ) * s + 1 by push_cast; ring] at h

/-- Products of congruent elements are congruent one step deeper. -/
theorem mul_sub_mul_mem_endFiltration {x x' y y' : Module.End K V} {s t : ℤ}
    (hx : x ∈ 𝓛.endFiltration s) (hy' : y' ∈ 𝓛.endFiltration t)
    (hdx : x - x' ∈ 𝓛.endFiltration (s + 1)) (hdy : y - y' ∈ 𝓛.endFiltration (t + 1)) :
    x * y - x' * y' ∈ 𝓛.endFiltration (s + t + 1) := by
  rw [show x * y - x' * y' = x * (y - y') + (x - x') * y' by noncomm_ring]
  refine add_mem ?_ ?_
  · have h := 𝓛.mul_mem_endFiltration hx hdy
    rwa [show s + (t + 1) = s + t + 1 by ring] at h
  · have h := 𝓛.mul_mem_endFiltration hdx hy'
    rwa [show s + 1 + t = s + t + 1 by ring] at h

/-- A unit of `𝔎(𝔄)` lies in `𝔓^n` exactly when `n` is at most its shift. -/
theorem mem_endFiltration_stabilizer_iff (g : 𝓛.stabilizer) (n : ℤ) :
    ((g : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.endFiltration n ↔
      n ≤ 𝓛.stabilizerValuation g := by
  change (∀ i, ∀ v ∈ 𝓛.lattice i, (g.val : Module.End K V) v ∈ 𝓛.lattice (i + n)) ↔
    n ≤ 𝓛.stabilizerValuation g
  constructor
  · intro hn
    have hmap : (𝓛.lattice 0).map ((g.val : Module.End K V).restrictScalars O) ≤
        𝓛.lattice (0 + n) := Submodule.map_le_iff_le_comap.mpr (hn 0)
    rw [𝓛.map_lattice_stabilizer g, 𝓛.strictAnti.le_iff_ge] at hmap
    simpa using hmap
  · intro hn i v hv
    have hm := Submodule.mem_map_of_mem (f := (g.val : Module.End K V).restrictScalars O) hv
    rw [𝓛.map_lattice_stabilizer g] at hm
    exact 𝓛.antitone (by omega) hm

/-- A unit of `𝔎(𝔄)` in `𝔄` but not in `𝔓` has its inverse in `𝔄`. -/
theorem inv_mem_order_of_not_mem (g : 𝓛.stabilizer)
    (h0 : ((g : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.order)
    (h1 : ((g : (Module.End K V)ˣ) : Module.End K V) ∉ 𝓛.endFiltration 1) :
    (((g⁻¹ : 𝓛.stabilizer) : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.order := by
  have hd0 := (𝓛.mem_endFiltration_stabilizer_iff g 0).mp h0
  have hd1 : ¬ 1 ≤ 𝓛.stabilizerValuation g :=
    fun h => h1 ((𝓛.mem_endFiltration_stabilizer_iff g 1).mpr h)
  have hsum := 𝓛.stabilizerValuation_mul g g⁻¹
  rw [mul_inv_cancel, 𝓛.stabilizerValuation_one] at hsum
  exact (𝓛.mem_endFiltration_stabilizer_iff g⁻¹ 0).mpr (by omega)

/-- The image in `𝔄/𝔓` of a subring of `A` whose nonzero elements lie in `𝔎(𝔄)` has no zero
divisors. -/
theorem residue_mul_eq_zero {R : Subring (Module.End K V)}
    (hR : ∀ x ∈ R, x ≠ 0 → ∃ g ∈ 𝓛.stabilizer, (g : Module.End K V) = x) :
    ∀ a ∈ (R.comap 𝓛.order.val.toRingHom).map (Ideal.Quotient.mk 𝓛.firstFiltrationIdeal),
    ∀ b ∈ (R.comap 𝓛.order.val.toRingHom).map (Ideal.Quotient.mk 𝓛.firstFiltrationIdeal),
      a * b = 0 → a = 0 ∨ b = 0 := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, -, rfl⟩ hxy
  by_cases hx0 : Ideal.Quotient.mk 𝓛.firstFiltrationIdeal x = 0
  · exact Or.inl hx0
  right
  have hx1 : (x : Module.End K V) ∉ 𝓛.endFiltration 1 :=
    fun h => hx0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hxne : (x : Module.End K V) ≠ 0 := fun h => hx1 (h ▸ zero_mem _)
  obtain ⟨g, hg, hgx⟩ := hR _ hx hxne
  replace hgx : (g : Module.End K V) = (x : Module.End K V) := hgx
  have hginv := 𝓛.inv_mem_order_of_not_mem ⟨g, hg⟩ (hgx ▸ x.2) (hgx ▸ hx1)
  let z : 𝓛.order := ⟨_, hginv⟩
  have hzx : z * x = 1 := by
    apply Subtype.ext
    change ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) * (x : Module.End K V) = 1
    rw [← hgx, Units.inv_mul]
  calc Ideal.Quotient.mk 𝓛.firstFiltrationIdeal y
      = Ideal.Quotient.mk 𝓛.firstFiltrationIdeal (z * x * y) := by rw [hzx, one_mul]
    _ = Ideal.Quotient.mk 𝓛.firstFiltrationIdeal z *
          (Ideal.Quotient.mk 𝓛.firstFiltrationIdeal x *
            Ideal.Quotient.mk 𝓛.firstFiltrationIdeal y) := by rw [map_mul, map_mul, mul_assoc]
    _ = 0 := by rw [hxy, mul_zero]

end Filtration

end LatticeChain

namespace Stratum

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/-- Scalars from the maximal ideal lie in the first filtration ideal. -/
theorem algebraMap_mem_firstFiltrationIdeal (C : LatticeChain O K V) {o : O}
    (ho : o ∈ Ring.jacobson O) :
    algebraMap O C.order o ∈ C.firstFiltrationIdeal := by
  change algebraMap O (Module.End K V) o ∈ C.endFiltration 1
  apply C.endFiltration_antitone (b := (C.period : ℤ)) (by exact_mod_cast C.period_pos)
  intro i v hv
  rw [C.lattice_add_period]
  simpa only [Module.algebraMap_end_apply] using Submodule.smul_mem_smul ho hv

/-- **Nonsplitness from a residue domain.** Let `D` be a fundamental stratum over a discrete
valuation ring, and `π` a prime element whose element `y_b` lies in the order. Suppose a ring
homomorphism from the order with kernel `𝔓` sends the scalars and `y_b` into a subring without
zero divisors. Then `D` is nonsplit. -/
theorem isNonsplit_of_residue_domain [FiniteDimensional K V] (D : Stratum O K V)
    (hfund : D.IsFundamental) (π : RingPrimeElement O)
    (hy : D.fundamentalElement π ∈ D.chain.order)
    {R : Type*} [Ring R] [Nontrivial R] (f : D.chain.order →+* R)
    (hf : ∀ x, f x = 0 ↔ x ∈ D.chain.firstFiltrationIdeal)
    (S : Subring R) (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = 0 → a = 0 ∨ b = 0)
    (hscal : ∀ o : O, f (algebraMap O D.chain.order o) ∈ S)
    (hyS : f ⟨D.fundamentalElement π, hy⟩ ∈ S) : D.IsNonsplit := by
  classical
  refine ⟨hfund, π, ?_⟩
  set y : D.chain.order := ⟨D.fundamentalElement π, hy⟩ with hydef
  set J := Ring.jacobson O with hJdef
  have hJ : J = IsLocalRing.maximalIdeal O := IsLocalRing.ringJacobson_eq_maximalIdeal O
  have hπirr : Irreducible π.1 := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hJ, π.2.2]
  have : J.IsMaximal := by
    rw [hJ]
    infer_instance
  let : Field (O ⧸ J) := Ideal.Quotient.field J
  have hfJ : ∀ o ∈ J, (f.comp (algebraMap O D.chain.order)) o = 0 := by
    intro o ho
    exact (hf _).mpr (algebraMap_mem_firstFiltrationIdeal D.chain ho)
  let ι : O ⧸ J →+* R := Ideal.Quotient.lift J (f.comp (algebraMap O D.chain.order)) hfJ
  have hι : ∀ o, ι (Ideal.Quotient.mk J o) = f (algebraMap O D.chain.order o) := fun _ => rfl
  have hcomm : ∀ a, Commute (ι a) (f y) := by
    intro a
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hι]
    exact (Algebra.commute_algebraMap_left o y).map f
  let φ : (O ⧸ J)[X] →+* R := eval₂RingHom' ι (f y) hcomm
  have hφ : ∀ q : O[X], φ (q.map (Ideal.Quotient.mk J)) = f (aeval y q) := by
    intro q
    change eval₂ ι (f y) (q.map (Ideal.Quotient.mk J)) = f (aeval y q)
    rw [eval₂_map, aeval_def, hom_eval₂]
    rfl
  have hφS : ∀ q, φ q ∈ S := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | monomial n a =>
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
      change eval₂ ι (f y) (monomial n (Ideal.Quotient.mk J o)) ∈ S
      rw [eval₂_monomial, hι]
      exact mul_mem (hscal o) (pow_mem hyS n)
  have hprime : (RingHom.ker φ).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
      exact one_ne_zero
    · intro a b hab
      rw [RingHom.mem_ker, map_mul] at hab
      rcases hS _ (hφS a) _ (hφS b) hab with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨Q, hQm, hQ⟩ := D.chain.exists_monic_charpoly_eq_map (D.fundamentalElement π)
    (fun v hv => by simpa using (D.chain.mem_order.mp hy) 0 v hv)
  have hQker : Q.map (Ideal.Quotient.mk J) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, hφ, (hf _)]
    have h0 : aeval y Q = 0 := by
      apply Subtype.ext
      have hval : ((aeval y Q : D.chain.order) : Module.End K V) =
          aeval (D.fundamentalElement π) Q :=
        (aeval_algHom_apply D.chain.order.val y Q).symm
      rw [hval, ZeroMemClass.coe_zero, ← aeval_map_algebraMap K, ← hQ]
      exact LinearMap.aeval_self_charpoly _
    rw [h0]
    exact zero_mem _
  have hne : RingHom.ker φ ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hQker
    exact (hQm.map (Ideal.Quotient.mk J)).ne_zero hQker
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (RingHom.ker φ)).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [hg]
    simp
  have hgprime : Prime g := by
    rw [← Ideal.span_singleton_prime hg0]
    have hg' : RingHom.ker φ = Ideal.span {g} := hg
    rw [← hg']
    exact hprime
  let p := g * C g.leadingCoeff⁻¹
  have hpm : p.Monic := monic_mul_leadingCoeff_inv hg0
  have hpirr : Irreducible p := by
    have hu : IsUnit (C g.leadingCoeff⁻¹) :=
      isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)))
    exact (irreducible_mul_isUnit hu).mpr hgprime.irreducible
  have hpker : p ∈ RingHom.ker φ := by
    have hgmem : g ∈ RingHom.ker φ := by
      rw [hg]
      exact Submodule.mem_span_singleton_self g
    exact Ideal.mul_mem_right _ _ hgmem
  obtain ⟨P, hPmap, -, -⟩ :=
    lifts_and_degree_eq_and_monic (mem_lifts_of_surjective Ideal.Quotient.mk_surjective p) hpm
  have hPmem : aeval y P ∈ D.chain.firstFiltrationIdeal := by
    rw [← hf, ← hφ, hPmap]
    exact hpker
  set Z := aeval (D.fundamentalElement π) P with hZdef
  have hZ : Z ∈ D.chain.endFiltration 1 := by
    have h : ((aeval y P : D.chain.order) : Module.End K V) ∈ D.chain.endFiltration 1 := hPmem
    rwa [show ((aeval y P : D.chain.order) : Module.End K V) = Z from
      (aeval_algHom_apply D.chain.order.val y P).symm] at h
  have hpow : ∀ k : ℕ, Z ^ k ∈ D.chain.endFiltration k := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Nat.cast_zero]
      exact D.chain.order.one_mem
    | succ k ih =>
      rw [pow_succ, Nat.cast_succ]
      exact D.chain.mul_mem_endFiltration ih hZ
  have hspan : Ring.jacobson O = Ideal.span {π.1} := π.2.2.symm
  have hQ' : ∀ v ∈ D.chain.lattice 0, ∃ w ∈ D.chain.lattice 0,
      aeval (D.fundamentalElement π) ((P ^ D.chain.period).map (algebraMap O K)) v =
        (algebraMap O K π.1) • w := by
    intro v hv
    have hmem := hpow D.chain.period 0 v hv
    rw [D.chain.lattice_add_period 0, hspan, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨w, hw, hwv⟩ := hmem
    refine ⟨w, hw, ?_⟩
    rw [Polynomial.map_pow, map_pow, aeval_map_algebraMap, ← hZdef, ← hwv, algebraMap_smul]
  have hpm' : (P.map (Ideal.Quotient.mk (Ring.jacobson O))).Monic := hPmap ▸ hpm
  have hpirr' : Irreducible (P.map (Ideal.Quotient.mk (Ring.jacobson O))) := hPmap ▸ hpirr
  obtain ⟨m, hm, h⟩ := D.chain.reduceIntegralPolynomial_charpoly_eq_pow_of_dvr hπirr
    (D.fundamentalElement π) (fun v hv => by simpa using (D.chain.mem_order.mp hy) 0 v hv)
    hpm' hpirr' D.chain.period hQ'
  exact ⟨P.map (Ideal.Quotient.mk (Ring.jacobson O)), m, hpm', hpirr', hm, h⟩

end Stratum

end Langlands.BushnellKutzko
