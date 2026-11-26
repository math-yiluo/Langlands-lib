import Langlands.BushnellKutzko.PureStratumApproximationSeed
import Langlands.BushnellKutzko.SubfieldValuationShifts
import Langlands.BushnellKutzko.AdjointLatticeBounds

/-! # The top stratum of a pure stratum is nonsplit fundamental (BK93 (2.3.11))

This module proves `Langlands.BushnellKutzko.PureApproximation.TopNonsplitPremise`: for a pure
stratum `[𝔄, n, r, β]`, the stratum `[𝔄, n, n - 1, β]` is nonsplit fundamental
(Bushnell–Kutzko 1993, (2.3.11), printed p. 60).

* Fundamentality is (2.3.2): `LatticeChain.not_isNilpotent_of_fieldShift` shows that no element
  of `β + 𝔓^{1-n}` kills a nonzero vector, because `β` carries `L_i` onto `L_{i-n}`.
* For nonsplitness, `y = ϖ^{n/g} β^{e/g}` is a unit of `F[β]` that shifts the chain by `0`, so
  it is a unit of the integer ring `𝔬_E` of `E = F[β]`. If `p` is the minimal polynomial of
  its residue class over the residue field `k_F` and `P` is a monic lift of `p`, then `P(y)` lies
  in the maximal ideal of `𝔬_E`, so `P(y)^e` maps `L_0` into `ϖ L_0`
  (`LatticeChain.exists_reduceIntegralPolynomial_charpoly_eq_pow`).
* The integral matrix of `y` on a basis of `L_0` then reduces to a matrix killed by `p^e`, and
  `charpoly_eq_pow_of_aeval_pow_eq_zero` makes its characteristic polynomial a positive power of
  `p` (`LatticeChain.reduceIntegralPolynomial_charpoly_eq_pow`).
-/

open Polynomial

namespace Langlands.BushnellKutzko

universe uF uV

/-! ### Characteristic polynomials of matrices killed by a polynomial -/

section Matrix

/-- Evaluation of polynomials at matrices commutes with a coefficient ring homomorphism. -/
theorem aeval_matrix_map_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (Q : R[X]) :
    aeval (A.map f) (Q.map f) = f.mapMatrix (aeval A Q) := by
  rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
  congr 1
  ext r i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

/-- If `q(A) = 0` then the characteristic polynomial of `A` divides `q ^ card`. -/
theorem charpoly_dvd_pow_card_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) (q : R[X]) (hq : aeval A q = 0) :
    A.charpoly ∣ q ^ Fintype.card n := by
  -- In `R[X][Y]`, `Y - C X` divides `q.map C - C q`.
  let Q : R[X][X] := q.map C
  have hdvd : (X - C (X : R[X])) ∣ Q - C q := by
    have h := X_sub_C_dvd_sub_C_eval (a := (X : R[X])) (p := Q)
    have heval : Q.eval (X : R[X]) = q := by
      simp only [Q, eval_map]
      exact eval₂_C_X
    rwa [heval] at h
  have hmap := map_dvd (aeval (A.map (C : R →+* R[X]))) hdvd
  have hA : aeval (A.map (C : R →+* R[X])) Q = 0 := by
    rw [aeval_matrix_map_map, hq, map_zero]
  rw [map_sub, map_sub, hA, aeval_X, aeval_C, aeval_C, zero_sub] at hmap
  have hchar : Matrix.charmatrix A =
      -(A.map (C : R →+* R[X]) - algebraMap R[X] (Matrix n n R[X]) X) := by
    rw [neg_sub, Matrix.charmatrix, Matrix.algebraMap_eq_diagonal]
    rfl
  have h2 : Matrix.charmatrix A ∣ algebraMap R[X] (Matrix n n R[X]) q := by
    rw [hchar]
    exact neg_dvd.mpr (dvd_neg.mp hmap)
  have hdet := map_dvd (Matrix.detMonoidHom (n := n) (R := R[X])) h2
  simp only [Matrix.coe_detMonoidHom, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Finset.prod_const,
    Finset.card_univ] at hdet
  exact hdet

/-- Over a field, a matrix killed by a power of a monic irreducible polynomial `p` has
characteristic polynomial a positive power of `p`. -/
theorem charpoly_eq_pow_of_aeval_pow_eq_zero {k : Type*} [Field k] {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (A : Matrix n n k) {p : k[X]} (hm : p.Monic)
    (hp : Irreducible p) {e : ℕ} (he : aeval A (p ^ e) = 0) :
    ∃ m : ℕ, 0 < m ∧ A.charpoly = p ^ m := by
  have hdvd := charpoly_dvd_pow_card_of_aeval_eq_zero A _ he
  rw [← pow_mul] at hdvd
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp.prime _).mp hdvd
  have heq : A.charpoly = p ^ i := eq_of_monic_of_associated A.charpoly_monic (hm.pow i) hi
  refine ⟨i, Nat.pos_of_ne_zero fun h0 => ?_, heq⟩
  have hdeg := A.charpoly_natDegree_eq_dim
  rw [heq, h0, pow_zero, natDegree_one] at hdeg
  exact (Fintype.card_ne_zero (α := n)) hdeg.symm

end Matrix

/-- Coefficientwise reduction of a polynomial with coefficients in the image of `O` is the
reduction of its preimage. -/
theorem reduceIntegralPolynomial_map {O K : Type*} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (q : O[X]) :
    reduceIntegralPolynomial O K (q.map (algebraMap O K)) =
      q.map (Ideal.Quotient.mk (Ring.jacobson O)) := by
  classical
  ext i
  rw [reduceIntegralPolynomial, finsetSum_coeff, coeff_map]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem h
  · have : Classical.choose h = q.coeff i :=
      hinj ((Classical.choose_spec h).trans (coeff_map _ _))
    rw [this]
  · exact absurd ⟨q.coeff i, (coeff_map _ _).symm⟩ h
  · have : q.coeff i = 0 := by
      rw [mem_support_iff, not_not, coeff_map] at hmem
      exact hinj (hmem.trans (map_zero _).symm)
    rw [this, map_zero]


namespace LatticeChain

open ValuativeRel

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type*} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

/-- An endomorphism preserving the lattice `L₀` of a chain, on which `P(Y)^e` takes values in
`ϖ L₀`, has reduced characteristic polynomial a positive power of `P mod 𝔭`, provided the latter
is monic irreducible. -/
theorem reduceIntegralPolynomial_charpoly_eq_pow [FiniteDimensional F V] {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (Y : Module.End F V) (hY : ∀ v ∈ 𝓛.lattice 0, Y v ∈ 𝓛.lattice 0)
    {P : 𝒪[F][X]}
    (hPm : (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))).Monic)
    (hPirr : Irreducible (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])))) (e : ℕ)
    (hQ : ∀ v ∈ 𝓛.lattice 0, ∃ w ∈ 𝓛.lattice 0,
      aeval Y ((P ^ e).map (algebraMap 𝒪[F] F)) v = (ϖ : F) • w) :
    ∃ m : ℕ, 0 < m ∧ reduceIntegralPolynomial 𝒪[F] F Y.charpoly =
      (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))) ^ m := by
  classical
  have hinj : Function.Injective (algebraMap 𝒪[F] F) := fun a b h => Subtype.ext h
  have : (Ring.jacobson 𝒪[F]).IsMaximal := by
    rw [jacobson_integer_eq_maximalIdeal]
    infer_instance
  let : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := Ideal.Quotient.field _
  let L := 𝓛.lattice 0
  have : L.IsLattice F := 𝓛.isLattice 0
  let b₀ := Module.Free.chooseBasis 𝒪[F] L
  let b := b₀.extendOfIsLattice F
  have hrepr : ∀ (x : L) i, b.repr (x : V) i = algebraMap 𝒪[F] F (b₀.repr x i) := by
    intro x i
    have hx : (x : V) = ∑ j, algebraMap 𝒪[F] F (b₀.repr x j) • b j := by
      have h := congrArg Subtype.val (b₀.sum_repr x)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Module.Basis.extendOfIsLattice_apply F b₀, algebraMap_smul]
    rw [hx, b.repr_sum_self]
  let A₀ : Matrix _ _ 𝒪[F] := fun i j => b₀.repr ⟨Y (b₀ j), hY _ (b₀ j).2⟩ i
  have hA : LinearMap.toMatrixAlgEquiv b Y = A₀.map (algebraMap 𝒪[F] F) := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.map_apply,
      Module.Basis.extendOfIsLattice_apply F b₀]
    exact hrepr ⟨Y (b₀ j), hY _ (b₀ j).2⟩ i
  have hchar : Y.charpoly = A₀.charpoly.map (algebraMap 𝒪[F] F) := by
    rw [← LinearMap.charpoly_toMatrix Y b, ← Matrix.charpoly_map, ← hA]
    congr 1
  have hred : reduceIntegralPolynomial 𝒪[F] F Y.charpoly =
      (A₀.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))).charpoly := by
    rw [hchar, reduceIntegralPolynomial_map hinj, Matrix.charpoly_map]
  let M := aeval A₀ (P ^ e)
  have hM : M.map (algebraMap 𝒪[F] F) =
      LinearMap.toMatrixAlgEquiv b (aeval Y ((P ^ e).map (algebraMap 𝒪[F] F))) := by
    have h1 := aeval_matrix_map_map (algebraMap 𝒪[F] F) A₀ (P ^ e)
    rw [← hA] at h1
    have h2 := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom Y
      ((P ^ e).map (algebraMap 𝒪[F] F))
    exact h1.symm.trans h2
  have hMJ : ∀ i j, M i j ∈ Ring.jacobson 𝒪[F] := by
    intro i j
    obtain ⟨w, hw, hZ⟩ := hQ (b₀ j) (b₀ j).2
    have h1 := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
      Module.Basis.extendOfIsLattice_apply F b₀, hZ,
      map_smul, Finsupp.smul_apply, smul_eq_mul,
      show w = ((⟨w, hw⟩ : L) : V) from rfl, hrepr] at h1
    have : M i j = ϖ * b₀.repr ⟨w, hw⟩ i := hinj (by rw [h1, map_mul]; rfl)
    rw [this, jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have hzero : aeval (A₀.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])))
      ((P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))) ^ e) = 0 := by
    rw [← Polynomial.map_pow, aeval_matrix_map_map]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hMJ i j)
  have : Nontrivial V := 𝓛.nontrivialSpace
  have : Nonempty (Module.Free.ChooseBasisIndex 𝒪[F] L) := b.index_nonempty
  obtain ⟨m, hm, h⟩ := charpoly_eq_pow_of_aeval_pow_eq_zero _ hPm hPirr hzero
  exact ⟨m, hm, hred.trans h⟩

end Local

section Field

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type*} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  (E : Type*) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)

/-- BK93 (2.3.2): if a normalizing field unit `u` shifts the chain by `-n`, then no element of
`u + 𝔓^{1-n}` is nilpotent. -/
theorem not_isNilpotent_of_fieldShift (u : Eˣ) {n : ℤ}
    (hu : (𝓛.fieldShift E hE u).toAdd = -n) {x : Module.End F V}
    (hx : x - subfieldEmbedding F E V u ∈ 𝓛.endFiltration (-(n - 1))) : ¬ IsNilpotent x := by
  have hmem : ∀ i (v : V), (u : E) • v ∈ 𝓛.lattice (i + -n) ↔ v ∈ 𝓛.lattice i := by
    intro i v
    have h := 𝓛.mem_lattice_fieldShift E hE u i (v := v)
    rwa [hu] at h
  have hker : ∀ v, x v = 0 → v = 0 := by
    intro v hxv
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨i₀, hi₀⟩ := 𝓛.exists_lattice_depth hϖ v
    have hstep : ∀ i, v ∈ 𝓛.lattice i → v ∈ 𝓛.lattice (i + 1) := by
      intro i hi
      have hd := hx i v hi
      have hb : (u : E) • v ∈ 𝓛.lattice (i + 1 + -n) := by
        have heq : (u : E) • v = -((x - subfieldEmbedding F E V u) v) := by
          rw [LinearMap.sub_apply, hxv, subfieldEmbedding_apply, zero_sub, neg_neg]
        rw [heq, show i + 1 + -n = i + -(n - 1) by ring]
        exact neg_mem hd
      exact (hmem (i + 1) v).mp hb
    have hall : ∀ k : ℕ, v ∈ 𝓛.lattice (i₀ + k) := by
      intro k
      induction k with
      | zero => simpa using hi₀
      | succ k ih =>
        have h := hstep _ ih
        rwa [Nat.cast_succ, ← add_assoc]
    apply 𝓛.lattice_eq_zero_of_forall
    intro j
    by_cases hj : j ≤ i₀
    · exact 𝓛.antitone hj hi₀
    · have h := hall (j - i₀).toNat
      rwa [show i₀ + ((j - i₀).toNat : ℤ) = j by omega] at h
  have hinj : Function.Injective x := by
    intro v w hvw
    have h := hker (v - w) (by rw [map_sub, hvw, sub_self])
    exact sub_eq_zero.mp h
  rintro ⟨k, hk⟩
  have := 𝓛.nontrivialSpace
  obtain ⟨v, hv0⟩ := exists_ne (0 : V)
  have h1 : (x ^ k) v = (x ^ k) 0 := by rw [hk]; rfl
  rw [Module.End.coe_pow] at h1
  exact hv0 (hinj.iterate k h1)

open IsLocalRing in
/-- A normalizing field unit of shift zero has reduced characteristic polynomial a positive power
of a monic irreducible polynomial over the residue field. -/
theorem exists_reduceIntegralPolynomial_charpoly_eq_pow [FiniteDimensional F V] (yE : Eˣ)
    (hy : (𝓛.fieldShift E hE yE).toAdd = 0) :
    ∃ (P : 𝒪[F][X]) (m : ℕ), (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))).Monic ∧
      Irreducible (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))) ∧ 0 < m ∧
      reduceIntegralPolynomial 𝒪[F] F (subfieldEmbedding F E V (yE : E)).charpoly =
        (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))) ^ m := by
  classical
  have : FiniteDimensional F E := 𝓛.finiteDimensional_subfield E
  have : IsDiscreteValuationRing (subfieldIntegers F E) :=
    subfieldIntegers_isDiscreteValuationRing F E
  have : IsFractionRing (subfieldIntegers F E) E := subfieldIntegers_isFractionRing F E
  obtain ⟨w, hw⟩ := 𝓛.exists_integerUnit_of_fieldShift_zero E hE hy
  have hyE : (yE : E) = algebraMap (subfieldIntegers F E) E (w : subfieldIntegers F E) := by
    rw [hw]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  -- The base maximal ideal maps into the maximal ideal of the integral closure.
  have hJ : ∀ a ∈ Ring.jacobson 𝒪[F],
      ((residue (subfieldIntegers F E)).comp (algebraMap 𝒪[F] (subfieldIntegers F E))) a = 0 := by
    intro a ha
    rw [jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have hmax : algebraMap 𝒪[F] (subfieldIntegers F E) ϖ ∈
        maximalIdeal (subfieldIntegers F E) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨U, hU⟩
      have h0 := 𝓛.fieldShift_integerUnit E hE U
      have h1 := 𝓛.fieldShift_baseUniformizer E hE hϖ
      have hUe : Units.map (algebraMap (subfieldIntegers F E) E).toMonoidHom U =
          Units.mk0 (algebraMap F E (ϖ : F)) (by
            intro h
            exact hϖ.ne_zero
              (Subtype.ext ((algebraMap F E).injective (h.trans (map_zero _).symm)))) := by
        apply Units.ext
        change ((U : subfieldIntegers F E) : E) = algebraMap F E (ϖ : F)
        rw [hU]
        rfl
      rw [hUe, h1] at h0
      exact 𝓛.period_pos.ne' (by exact_mod_cast h0)
    rw [RingHom.comp_apply, map_mul, map_mul, (residue_eq_zero_iff _).mpr hmax, mul_zero]
  have : (Ring.jacobson 𝒪[F]).IsMaximal := by
    rw [jacobson_integer_eq_maximalIdeal]
    infer_instance
  let : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := Ideal.Quotient.field _
  let : Algebra (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) (ResidueField (subfieldIntegers F E)) :=
    (Ideal.Quotient.lift (Ring.jacobson 𝒪[F])
      ((residue (subfieldIntegers F E)).comp (algebraMap 𝒪[F] (subfieldIntegers F E))) hJ).toAlgebra
  have hcomp : (algebraMap (𝒪[F] ⧸ Ring.jacobson 𝒪[F])
      (ResidueField (subfieldIntegers F E))).comp (Ideal.Quotient.mk _) =
      (residue (subfieldIntegers F E)).comp (algebraMap 𝒪[F] (subfieldIntegers F E)) :=
    RingHom.ext fun a => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.lift_mk _ _ _
  have : Algebra.IsIntegral 𝒪[F] (subfieldIntegers F E) := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  have hint := (Algebra.IsIntegral.isIntegral (R := 𝒪[F]) (w : subfieldIntegers F E)).map_of_comp_eq
    (Ideal.Quotient.mk (Ring.jacobson 𝒪[F])) (residue (subfieldIntegers F E)) hcomp
  obtain ⟨P, hPmap, -, -⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective Ideal.Quotient.mk_surjective _) (minpoly.monic hint)
  have hz : residue (subfieldIntegers F E) (aeval (w : subfieldIntegers F E) P) = 0 := by
    have h := minpoly.aeval (𝒪[F] ⧸ Ring.jacobson 𝒪[F])
      (residue (subfieldIntegers F E) (w : subfieldIntegers F E))
    rw [← hPmap, aeval_def, eval₂_map, hcomp, ← hom_eval₂, ← aeval_def] at h
    exact h
  have hzm := (residue_eq_zero_iff _).mp hz
  obtain ⟨ϖE, hϖE⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  rw [hϖE.maximalIdeal_eq, Ideal.mem_span_singleton'] at hzm
  obtain ⟨c, hc⟩ := hzm
  have hstep : ∀ i (v : V), v ∈ 𝓛.lattice i →
      ((aeval (w : subfieldIntegers F E) P : subfieldIntegers F E) : E) • v ∈
        𝓛.lattice (i + 1) := by
    intro i v hv
    rw [← hc]
    have hs := 𝓛.fieldShift_uniformizer_pos E hE hϖE
    have h1 : ((ϖE : subfieldIntegers F E) : E) • v ∈ 𝓛.lattice (i + 1) :=
      𝓛.antitone (by omega) ((𝓛.mem_lattice_fieldShift E hE
        (Units.mk0 (ϖE : E) (fun h => hϖE.ne_zero (Subtype.ext h))) i).mpr hv)
    have h2 := 𝓛.subfieldInteger_smul_mem E hE (i + 1) c h1
    rwa [Subalgebra.coe_mul, mul_smul]
  have hpow : ∀ t : ℕ, ∀ i (v : V), v ∈ 𝓛.lattice i →
      (((aeval (w : subfieldIntegers F E) P) ^ t : subfieldIntegers F E) : E) • v ∈
        𝓛.lattice (i + t) := by
    intro t
    induction t with
    | zero =>
      intro i v hv
      simpa using hv
    | succ t ih =>
      intro i v hv
      rw [pow_succ', Subalgebra.coe_mul, mul_smul, Nat.cast_succ, ← add_assoc]
      exact hstep _ _ (ih i v hv)
  have hYeval : ∀ (Q : 𝒪[F][X]) (v : V),
      aeval (subfieldEmbedding F E V (yE : E)) (Q.map (algebraMap 𝒪[F] F)) v =
        ((aeval (w : subfieldIntegers F E) Q : subfieldIntegers F E) : E) • v := by
    intro Q v
    rw [aeval_algHom_apply, subfieldEmbedding_apply, aeval_map_algebraMap, hyE,
      aeval_algebraMap_apply]
    rfl
  have hQ : ∀ v ∈ 𝓛.lattice 0, ∃ w' ∈ 𝓛.lattice 0,
      aeval (subfieldEmbedding F E V (yE : E)) ((P ^ 𝓛.period).map (algebraMap 𝒪[F] F)) v =
        (ϖ : F) • w' := by
    intro v hv
    rw [hYeval, map_pow]
    have hx := hpow 𝓛.period 0 v hv
    refine ⟨(ϖ : F)⁻¹ •
      ((((aeval (w : subfieldIntegers F E) P) ^ 𝓛.period : subfieldIntegers F E) : E) • v),
      ?_, ?_⟩
    · apply (𝓛.uniformizer_lattice_mem_iff hϖ 0 _).mp
      rw [smul_inv_smul₀ hϖ0]
      exact hx
    · rw [smul_inv_smul₀ hϖ0]
  have hYL : ∀ v ∈ 𝓛.lattice 0, subfieldEmbedding F E V (yE : E) v ∈ 𝓛.lattice 0 := by
    intro v hv
    rw [subfieldEmbedding_apply, hyE]
    exact 𝓛.subfieldInteger_smul_mem E hE 0 w hv
  have hPm : (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))).Monic := by
    rw [hPmap]
    exact minpoly.monic hint
  have hPirr : Irreducible (P.map (Ideal.Quotient.mk (Ring.jacobson 𝒪[F]))) := by
    rw [hPmap]
    exact minpoly.irreducible hint
  obtain ⟨m, hm, h⟩ := 𝓛.reduceIntegralPolynomial_charpoly_eq_pow hϖ _ hYL hPm hPirr 𝓛.period hQ
  exact ⟨P, m, hPm, hPirr, hm, h⟩

end Field

end LatticeChain

namespace PureApproximation

open ValuativeRel

/-- BK93 (2.3.11), printed p. 60: for every pure stratum `[𝔄, n, r, β]`, the stratum
`[𝔄, n, n - 1, β]` is nonsplit fundamental. -/
theorem topNonsplitPremise : TopNonsplitPremise.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S hS
  obtain ⟨⟨hF, hE⟩, hv⟩ := hS
  let := hF.toField
  let β : elementAlgebra S.b := ⟨S.b, Algebra.self_mem_adjoin_singleton F S.b⟩
  have hβ : subfieldEmbedding F (elementAlgebra S.b) V β = S.b := by
    ext v
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    have h' : S.b = 0 := congrArg Subtype.val h
    rw [h', S.chain.valuation_zero, ← WithTop.LinearOrderedAddCommGroup.coe_neg] at hv
    exact WithTop.top_ne_coe hv
  let u : (elementAlgebra S.b)ˣ := Units.mk0 β hβ0
  have hshift : (S.chain.fieldShift (elementAlgebra S.b) hE u).toAdd = -S.n := by
    have h := S.chain.valuation_eq_shift ⟨subfieldUnits F (elementAlgebra S.b) V u, hE u⟩
    change S.chain.valuation (subfieldEmbedding F (elementAlgebra S.b) V β) = _ at h
    rw [hβ, hv] at h
    change S.chain.stabilizerValuation ⟨subfieldUnits F (elementAlgebra S.b) V u, hE u⟩ = -S.n
    exact_mod_cast h.symm
  refine ⟨⟨rfl, fun x hx => S.chain.not_isNilpotent_of_fieldShift (elementAlgebra S.b) hE u
    hshift (by rw [show subfieldEmbedding F (elementAlgebra S.b) V (u : elementAlgebra S.b) = S.b
      from hβ]; exact hx)⟩, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let π : RingPrimeElement 𝒪[F] := ⟨ϖ, hϖ.ne_zero, by
    rw [jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq]⟩
  obtain ⟨e', he'⟩ := Nat.gcd_dvd_left S.chain.period S.n.natAbs
  obtain ⟨n', hn'⟩ : ((Nat.gcd S.chain.period S.n.natAbs : ℕ) : ℤ) ∣ S.n :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hg : 0 < Nat.gcd S.chain.period S.n.natAbs := Nat.gcd_pos_of_pos_left _ S.chain.period_pos
  let yE : (elementAlgebra S.b)ˣ :=
    (baseIntegerUnit (elementAlgebra S.b) hϖ.ne_zero) ^
      (S.n / ((Nat.gcd S.chain.period S.n.natAbs : ℕ) : ℤ)) *
      u ^ (S.chain.period / Nat.gcd S.chain.period S.n.natAbs)
  have hy : (S.chain.fieldShift (elementAlgebra S.b) hE yE).toAdd = 0 := by
    have hb := S.chain.fieldShift_baseUniformizer (elementAlgebra S.b) hE hϖ
    simp only [yE, map_mul, map_zpow, map_pow, toAdd_mul, toAdd_zpow, toAdd_pow, hshift]
    rw [show (S.chain.fieldShift (elementAlgebra S.b) hE
      (baseIntegerUnit (elementAlgebra S.b) hϖ.ne_zero)).toAdd = S.chain.period from hb]
    generalize S.chain.period.gcd S.n.natAbs = g at he' hn' hg ⊢
    rw [smul_eq_mul, nsmul_eq_mul, hn', he', Int.mul_ediv_cancel_left _ (by exact_mod_cast hg.ne'),
      Nat.mul_div_cancel_left _ hg]
    push_cast
    ring
  obtain ⟨P, m, hPm, hPirr, hm, h⟩ :=
    S.chain.exists_reduceIntegralPolynomial_charpoly_eq_pow (elementAlgebra S.b) hE yE hy
  refine ⟨π, _, m, hPm, hPirr, hm, ?_⟩
  have hY : subfieldEmbedding F (elementAlgebra S.b) V (yE : elementAlgebra S.b) =
      (⟨S.chain, S.n, S.n - 1, S.b, by omega, S.valuation_ge⟩ :
        Stratum 𝒪[F] F V).fundamentalElement π := by
    simp only [yE, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      baseIntegerUnit_val, ← map_zpow₀, map_mul, map_pow, AlgHom.commutes, Units.val_mk0, u, hβ]
    rw [← Algebra.smul_def]
    rfl
  change reduceIntegralPolynomial 𝒪[F] F (LinearMap.charpoly (Stratum.fundamentalElement _ π)) = _
  rw [← hY]
  exact h

end PureApproximation

end Langlands.BushnellKutzko
