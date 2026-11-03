import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Finite-index restriction of rational characters to a central split torus

Let `G` be an affine group scheme of finite type over a field `k` and let `i : A ⟶ G` be a central
split torus (`IsCentralSplitTorus`). Restriction `X^*(G)_k → X^*(A)` then has finite-index range
(`finiteIndex_range_characterRestrict`). In particular this holds for every split component of
a connected reductive group (`IsSplitComponent.finiteIndex_range_characterRestrict`), the
finite-index half of Renard V.2.6.

The proof uses points only. Fix `A ≅ 𝔾_m^I`, `j : 𝔾_m^I ⟶ G`, and a matrix representation
`ρ : G ⟶ GL_N` that is a closed immersion (`affineLinearEmbeddingStatement`).

* The matrix of `ρ ∘ j` at the universal point of the torus over `k[ℤ^I]` is `∑ₘ P_m · m`, with
  weight matrices `P_m` over `k` (`universalMatrix`, `weight`). At the torus point with unit
  coordinates `t` over a `k`-algebra, the matrix of `ρ ∘ j` is `∑ₘ P_m tᵐ`
  (`affinePointsEquiv_eval`).
* The `P_m` sum to `1` and are orthogonal idempotents (`sum_weight`, `weight_mul_weight`). By
  centrality of `j` they commute with the matrix of every point of `G` (`weight_commute_affine`,
  `weight_commute_points`).
* Write `P_m = U V` with `V U = 1` (`exists_factor_of_mul_self`). Then `g ↦ V ρ(g) U` is a
  representation of `G` of size `d = rank P_m` (`blockRepresentation`). Its determinant
  `blockCharacter` restricts to the torus as `d • m` (`characterRestrict_blockCharacter`).
* The exponents `m` with `P_m ≠ 0` generate `ℤ^I`, because `ρ ∘ j` is a monomorphism
  (`closure_weights_eq_top`). Hence the product `D` of the block sizes satisfies
  `D • X^*(A) ⊆ range`, and the range has finite index (`exists_nsmul_mem_range`,
  `finiteIndex_of_nsmul_mem`).
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CharacterRestrictionFiniteIndex

open splitTorus

set_option backward.isDefEq.respectTransparency false

/-! ### Monomials in group algebras -/

section Monomials

variable {B : Type u} [CommRing B] {M : Type u} [AddCommGroup M]

/-- The invertible monomial of `B[M]` indexed by `x`. -/
abbrev monomialUnit (x : M) : (AddMonoidAlgebra B M)ˣ :=
  (AddMonoidAlgebra.of B M).toHomUnits (Multiplicative.ofAdd x)

/-- The underlying element of a monomial unit is the monomial with coefficient `1`. -/
theorem monomialUnit_val (x : M) :
    ((monomialUnit (B := B) x : (AddMonoidAlgebra B M)ˣ) : AddMonoidAlgebra B M) =
      AddMonoidAlgebra.single x 1 := rfl

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The exponent monomial at the monomial coordinates `φ (eᵢ)` is the monomial at `φ m`. -/
theorem exponentValue_monomialUnit (φ : (I → ℤ) →+ M) (m : I → ℤ) :
    exponentValue I (fun i => monomialUnit (B := B) (φ (Pi.single i 1)))
      (Multiplicative.ofAdd m) = monomialUnit (φ m) := by
  let f := (AddMonoidAlgebra.of B M).toHomUnits
  have hm : (∑ i : I, m i • Pi.single i (1 : ℤ)) = m := by
    ext j
    simp [Pi.single_apply]
  change (∏ i, f (Multiplicative.ofAdd (φ (Pi.single i 1))) ^ m i) = f (Multiplicative.ofAdd (φ m))
  conv_rhs => rw [← hm, map_sum]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, ofAdd_zsmul, map_zpow]

/-- The exponent monomial at the monomial coordinates `eᵢ` is the monomial at `m`. -/
theorem exponentValue_monomialUnit_id (m : I → ℤ) :
    exponentValue I (fun i => monomialUnit (B := B) (Pi.single i (1 : ℤ)))
      (Multiplicative.ofAdd m) = monomialUnit m :=
  exponentValue_monomialUnit (AddMonoidHom.id (I → ℤ)) m

end Monomials


/-! ### Compression of matrices commuting with an idempotent -/

section Compress

variable {S : Type*} [CommRing S] {n d : Type} [Fintype n] [DecidableEq n] [Fintype d]
  [DecidableEq d] (U : Matrix n d S) (V : Matrix d n S) (hVU : V * U = 1)

omit [DecidableEq n] in
include hVU in
/-- Compression is multiplicative on matrices commuting with the idempotent `U V`. -/
theorem compress_mul_compress {M₁ M₂ : Matrix n n S} (h₂ : M₂ * (U * V) = U * V * M₂) :
    V * M₁ * U * (V * M₂ * U) = V * (M₁ * M₂) * U := by
  calc V * M₁ * U * (V * M₂ * U) = V * M₁ * ((U * V) * M₂) * U := by
        simp only [Matrix.mul_assoc]
    _ = V * M₁ * (M₂ * (U * V)) * U := by rw [h₂]
    _ = V * (M₁ * M₂) * (U * (V * U)) := by simp only [Matrix.mul_assoc]
    _ = V * (M₁ * M₂) * U := by rw [hVU, Matrix.mul_one]

omit [DecidableEq d] in
/-- A matrix commuting with `U V` has its inverse commuting with `U V`. -/
theorem inv_commute_of_commute (M : Matrix.GeneralLinearGroup n S)
    (hM : M.val * (U * V) = U * V * M.val) :
    (M⁻¹).val * (U * V) = U * V * (M⁻¹).val := by
  calc (M⁻¹).val * (U * V)
      = (M⁻¹).val * (U * V) * (M.val * (M⁻¹).val) := by
        rw [Units.mul_inv, Matrix.mul_one]
    _ = (M⁻¹).val * ((U * V) * M.val) * (M⁻¹).val := by simp only [Matrix.mul_assoc]
    _ = (M⁻¹).val * (M.val * (U * V)) * (M⁻¹).val := by rw [hM]
    _ = U * V * (M⁻¹).val := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- The compression `M ↦ V M U` of an invertible matrix commuting with the idempotent `U V`,
an invertible matrix of the smaller size. -/
def compress (M : Matrix.GeneralLinearGroup n S)
    (hM : M.val * (U * V) = U * V * M.val) : Matrix.GeneralLinearGroup d S where
  val := V * M.val * U
  inv := V * (M⁻¹).val * U
  val_inv := by
    rw [compress_mul_compress U V hVU (inv_commute_of_commute U V M hM), Units.mul_inv,
      Matrix.mul_one, hVU]
  inv_val := by
    rw [compress_mul_compress U V hVU hM, Units.inv_mul, Matrix.mul_one, hVU]

omit [Fintype d] [DecidableEq d] in
/-- The underlying matrix of the image of an invertible matrix under a ring homomorphism. -/
theorem val_map {S' : Type*} [CommRing S'] (f : S →+* S') (M : Matrix.GeneralLinearGroup n S) :
    (Matrix.GeneralLinearGroup.map f M).val = M.val.map f := rfl

/-- The underlying matrix of a compression is `V M U`. -/
theorem compress_val (M : Matrix.GeneralLinearGroup n S)
    (hM : M.val * (U * V) = U * V * M.val) :
    (compress U V hVU M hM).val = V * M.val * U := rfl

end Compress

/-! ### Rank factorization of idempotent matrices and finite index -/

section Factor

variable {k : Type u} [Field k]

/-- An idempotent matrix over a field factors as `P = U V` with `V U = 1`, through its image. -/
theorem exists_factor_of_mul_self {N : ℕ} (P : Matrix (Fin N) (Fin N) k) (hP : P * P = P) :
    ∃ (d : ℕ) (U : Matrix (Fin N) (Fin d) k) (V : Matrix (Fin d) (Fin N) k),
      U * V = P ∧ V * U = 1 := by
  classical
  let f := Matrix.toLin' P
  have hf : f ∘ₗ f = f := by rw [← Matrix.toLin'_mul, hP]
  let b := Module.finBasis k (LinearMap.range f)
  have h₁ : (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f := LinearMap.ext fun _ => rfl
  have h₂ : f.rangeRestrict ∘ₗ (LinearMap.range f).subtype = LinearMap.id := by
    ext ⟨w, v, rfl⟩ : 1
    exact Subtype.ext (LinearMap.congr_fun hf v)
  refine ⟨Module.finrank k (LinearMap.range f),
    LinearMap.toMatrix b (Pi.basisFun k (Fin N)) (LinearMap.range f).subtype,
    LinearMap.toMatrix (Pi.basisFun k (Fin N)) b f.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, h₁, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix_comp, h₂, LinearMap.toMatrix_id]

/-- A factorization `P = U V` through `Fin 0` forces `P = 0`. -/
theorem ne_zero_of_factor {N d : ℕ} {P : Matrix (Fin N) (Fin N) k} {U : Matrix (Fin N) (Fin d) k}
    {V : Matrix (Fin d) (Fin N) k} (hUV : U * V = P) (hP : P ≠ 0) : d ≠ 0 := by
  rintro rfl
  apply hP
  rw [← hUV]
  ext a b
  simp [Matrix.mul_apply]

/-- In a finitely generated abelian group, a subgroup containing all `D`-th multiples, `D ≠ 0`,
has finite index. -/
theorem finiteIndex_of_nsmul_mem {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    (H : AddSubgroup M) {D : ℕ} (hD : D ≠ 0) (h : ∀ x : M, D • x ∈ H) : H.FiniteIndex := by
  have : Module.Finite ℤ (M ⧸ H) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' H).toIntLinearMap
      (QuotientAddGroup.mk'_surjective H)
  have : Finite (M ⧸ H) := by
    apply Module.finite_of_fg_torsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      refine ⟨⟨(D : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hD)⟩, ?_⟩
      change ((D : ℤ) • (x : M ⧸ H)) = 0
      rw [natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact h x
  exact AddSubgroup.finiteIndex_of_finite_quotient

end Factor

/-! ### The weight matrices of a representation restricted to a split torus -/

section Weights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- The matrix of `ρ` at the image under `j` of the universal point of the split torus, an
invertible matrix over the group algebra `k[ℤ^I]`. -/
def universalMatrix : Matrix.GeneralLinearGroup (Fin N) (AddMonoidAlgebra k (I → ℤ)) :=
  GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (I → ℤ)))
    (universalPoint (R := CommRingCat.of k) I ≫ j.hom.hom ≫ ρ.hom.hom)

/-- The weight matrix `P_m`: the coefficient of the monomial `m` in the universal matrix. -/
def weight (m : I → ℤ) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun a b =>
    ((universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b).coeff m

/-- A finite set of exponents outside which all weight matrices vanish. -/
def weightSupport : Finset (I → ℤ) :=
  Finset.univ.biUnion fun ab : Fin N × Fin N =>
    ((universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ)))
      ab.1 ab.2).coeff.support

/-- Outside the weight support the weight matrices vanish. -/
theorem weight_eq_zero {m : I → ℤ} (hm : m ∉ weightSupport ρ I j) : weight ρ I j m = 0 := by
  ext a b
  by_contra h
  exact hm (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)

/-- The universal matrix is the sum of its weight matrices times the monomials. -/
theorem universalMatrix_apply (a b : Fin N) :
    (universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b =
      ∑ m ∈ weightSupport ρ I j, weight ρ I j m a b • AddMonoidAlgebra.single m 1 := by
  apply AddMonoidAlgebra.coeff_injective
  ext n
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · change weight ρ I j n a b = 0
    rw [weight_eq_zero ρ I j hn]
    rfl

/-- **Evaluation formula.** At the point of the split torus with unit coordinates `t` over a
`k`-algebra `A`, the matrix of `ρ ∘ j` is `∑ₘ P_m · tᵐ`. -/
theorem affinePointsEquiv_eval {A : Type u} [CommRing A] [Algebra k A] (t : I → Aˣ) (a b : Fin N) :
    (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k) (CommAlgCat.of (CommRingCat.of k) A)
      ((algebraPointsEquiv I A).symm t ≫ j.hom.hom ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) A) a b =
      ∑ m ∈ weightSupport ρ I j,
        weight ρ I j m a b • ((exponentValue I t (Multiplicative.ofAdd m) : Aˣ) : A) := by
  rw [← universalPoint_evaluateUnits (R := CommRingCat.of k) I t, Lie.affineMap_apply,
    Category.assoc, GeneralLinear.affinePointsEquiv_naturality]
  change evaluateUnits (R := CommRingCat.of k) I t
    ((universalMatrix ρ I j : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) a b) = _
  rw [universalMatrix_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, evaluateUnits_single, map_one, one_mul]

/-- A function of exponents that vanishes outside the weight support is recovered from its
sum against a Kronecker delta over the weight support. -/
theorem sum_ite_eq_of_weightSupport {X : Type*} [AddCommMonoid X] (f : (I → ℤ) → X)
    (hf : ∀ m ∉ weightSupport ρ I j, f m = 0) (m₀ : I → ℤ) :
    ∑ m ∈ weightSupport ρ I j, (if m = m₀ then f m else 0) = f m₀ := by
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hf m₀ h).symm

/-- The weight matrices sum to the identity: evaluate at the identity point. -/
theorem sum_weight : ∑ m ∈ weightSupport ρ I j, weight ρ I j m = 1 := by
  ext a b
  have h := affinePointsEquiv_eval ρ I j (A := k) 1 a b
  rw [map_one, MonObj.one_comp, map_one] at h
  simp only [exponentValue, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply, one_zpow,
    Finset.prod_const_one, Units.val_one, smul_eq_mul, mul_one] at h
  rw [Matrix.sum_apply]
  exact h.symm

/-- The entries of the weight matrices vanish outside the weight support. -/
theorem weight_apply_eq_zero {m : I → ℤ} (hm : m ∉ weightSupport ρ I j) (a b : Fin N) :
    weight ρ I j m a b = 0 := by
  rw [weight_eq_zero ρ I j hm]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The coefficient of a scaled monomial. -/
theorem coeff_smul_single_one {M : Type u} [AddCommGroup M] [DecidableEq M] (c : k) (x y : M) :
    (c • AddMonoidAlgebra.single x (1 : k)).coeff y = if x = y then c else 0 := by
  rw [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- The group algebra `k[ℤ^I × ℤ^I]` of pairs of exponents. -/
local notation "K₂" => AddMonoidAlgebra k ((I → ℤ) × (I → ℤ))

/-- The weight matrices are orthogonal idempotents: multiply two independent universal points. -/
theorem weight_mul_weight (m₀ n₀ : I → ℤ) :
    weight ρ I j m₀ * weight ρ I j n₀ = if m₀ = n₀ then weight ρ I j m₀ else 0 := by
  classical
  let t₁ : I → K₂ˣ := fun i => monomialUnit (AddMonoidHom.inl (I → ℤ) (I → ℤ) (Pi.single i 1))
  let t₂ : I → K₂ˣ := fun i => monomialUnit (AddMonoidHom.inr (I → ℤ) (I → ℤ) (Pi.single i 1))
  let δ : (I → ℤ) →+ (I → ℤ) × (I → ℤ) := (AddMonoidHom.id _).prod (AddMonoidHom.id _)
  have ht : t₁ * t₂ = fun i => monomialUnit (δ (Pi.single i 1)) := by
    funext i
    simp only [Pi.mul_apply, t₁, t₂, δ, monomialUnit, ← map_mul, ← ofAdd_add]
    congr 2
    rw [AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hpt : (algebraPointsEquiv I K₂).symm (t₁ * t₂) ≫ j.hom.hom ≫ ρ.hom.hom =
      ((algebraPointsEquiv I K₂).symm t₁ ≫ j.hom.hom ≫ ρ.hom.hom) *
        ((algebraPointsEquiv I K₂).symm t₂ ≫ j.hom.hom ≫ ρ.hom.hom) := by
    rw [map_mul, MonObj.mul_comp]
  have h12 : ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) K₂)
        ((algebraPointsEquiv I K₂).symm (t₁ * t₂) ≫ j.hom.hom ≫ ρ.hom.hom) :
          Matrix.GeneralLinearGroup (Fin N) K₂) : Matrix (Fin N) (Fin N) K₂) =
      ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
        (CommAlgCat.of (CommRingCat.of k) K₂)
          ((algebraPointsEquiv I K₂).symm t₁ ≫ j.hom.hom ≫ ρ.hom.hom) :
            Matrix.GeneralLinearGroup (Fin N) K₂) : Matrix (Fin N) (Fin N) K₂) *
      ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
        (CommAlgCat.of (CommRingCat.of k) K₂)
          ((algebraPointsEquiv I K₂).symm t₂ ≫ j.hom.hom ≫ ρ.hom.hom) :
            Matrix.GeneralLinearGroup (Fin N) K₂) : Matrix (Fin N) (Fin N) K₂) := by
    rw [hpt, map_mul, Units.val_mul]
  ext a b
  have hab := congrArg (fun z : K₂ => z.coeff (m₀, n₀)) (congrFun (congrFun h12 a) b)
  simp only [Matrix.mul_apply] at hab
  rw [affinePointsEquiv_eval ρ I j (A := K₂) (t₁ * t₂) a b, ht] at hab
  simp only [affinePointsEquiv_eval ρ I j (A := K₂)] at hab
  simp only [t₁, t₂, exponentValue_monomialUnit, monomialUnit_val] at hab
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm, AddMonoidAlgebra.single_mul_single, mul_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_smul_single_one] at hab
  simp only [δ, AddMonoidHom.prod_apply, AddMonoidHom.id_apply, AddMonoidHom.inl_apply,
    AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add] at hab
  have hR : ∀ l, (∑ m ∈ weightSupport ρ I j, ∑ n ∈ weightSupport ρ I j,
      if (m, n) = (m₀, n₀) then weight ρ I j m a l * weight ρ I j n l b else 0) =
        weight ρ I j m₀ a l * weight ρ I j n₀ l b := by
    intro l
    have hm : ∀ m, (∑ n ∈ weightSupport ρ I j,
        if (m, n) = (m₀, n₀) then weight ρ I j m a l * weight ρ I j n l b else 0) =
          if m = m₀ then weight ρ I j m a l * weight ρ I j n₀ l b else 0 := by
      intro m
      by_cases h : m = m₀
      · subst h
        simp only [Prod.mk.injEq, true_and, ite_true]
        exact sum_ite_eq_of_weightSupport ρ I j (fun n => weight ρ I j m a l * weight ρ I j n l b)
          (fun n hn => by rw [weight_apply_eq_zero ρ I j hn, mul_zero]) n₀
      · simp [Prod.mk.injEq, h]
    rw [Finset.sum_congr rfl fun m _ => hm m]
    exact sum_ite_eq_of_weightSupport ρ I j (fun m => weight ρ I j m a l * weight ρ I j n₀ l b)
      (fun m hm => by rw [weight_apply_eq_zero ρ I j hm, zero_mul]) m₀
  have hL : (∑ m ∈ weightSupport ρ I j, if (m, m) = (m₀, n₀) then weight ρ I j m a b else 0) =
      if m₀ = n₀ then weight ρ I j m₀ a b else 0 := by
    by_cases h : m₀ = n₀
    · subst h
      simp only [Prod.mk.injEq, and_self, ite_true]
      exact sum_ite_eq_of_weightSupport ρ I j (fun m => weight ρ I j m a b)
        (fun m hm => weight_apply_eq_zero ρ I j hm a b) m₀
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun m _ => ite_eq_right ?_
      rintro ⟨⟩
      exact h rfl
  calc (weight ρ I j m₀ * weight ρ I j n₀) a b
      = ∑ l, ∑ m ∈ weightSupport ρ I j, ∑ n ∈ weightSupport ρ I j,
          if (m, n) = (m₀, n₀) then weight ρ I j m a l * weight ρ I j n l b else 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun l _ => (hR l).symm
    _ = ∑ m ∈ weightSupport ρ I j, if (m, m) = (m₀, n₀) then weight ρ I j m a b else 0 :=
        hab.symm
    _ = if m₀ = n₀ then weight ρ I j m₀ a b else 0 := hL
    _ = (if m₀ = n₀ then weight ρ I j m₀ else 0) a b := by split_ifs <;> rfl

omit [Fintype I] [DecidableEq I] in
/-- The coefficient of a scaled monomial with coefficients in an algebra. -/
theorem coeff_smul_single {B M : Type u} [CommRing B] [Algebra k B] [AddCommGroup M]
    [DecidableEq M] (c : k) (x y : M) (b : B) :
    (c • AddMonoidAlgebra.single x b).coeff y = if x = y then c • b else 0 := by
  rw [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- **Centrality.** The weight matrices commute with the matrix of every point of `G` over a
`k`-algebra: test the centrality of `j` on the universal torus point over `B[ℤ^I]`. -/
theorem weight_commute_affine (hc : IsCentral j) {B : Type u} [CommRing B] [Algebra k B]
    (y : Lie.AffinePoints G B) (m₀ : I → ℤ) :
    (weight ρ I j m₀).map (algebraMap k B) *
        (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
          (CommAlgCat.of (CommRingCat.of k) B) (y ≫ ρ.hom.hom) : Matrix (Fin N) (Fin N) B) =
      (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
          (CommAlgCat.of (CommRingCat.of k) B) (y ≫ ρ.hom.hom) : Matrix (Fin N) (Fin N) B) *
        (weight ρ I j m₀).map (algebraMap k B) := by
  classical
  by_cases hm₀ : m₀ ∉ weightSupport ρ I j
  · rw [weight_eq_zero ρ I j hm₀]
    simp
  rw [not_not] at hm₀
  let t : I → (AddMonoidAlgebra B (I → ℤ))ˣ := fun i => monomialUnit (Pi.single i 1)
  let y' : Lie.AffinePoints G (AddMonoidAlgebra B (I → ℤ)) :=
    Lie.affineMap G (AddMonoidAlgebra.singleZeroAlgHom (R := k) (A := B) (M := I → ℤ)) y
  have hcomm : Commute ((algebraPointsEquiv I (AddMonoidAlgebra B (I → ℤ))).symm t ≫ j.hom.hom)
      y' := commute_of_mem_center (hc _ _) y'
  have hρ : ((algebraPointsEquiv I (AddMonoidAlgebra B (I → ℤ))).symm t ≫ j.hom.hom ≫ ρ.hom.hom) *
      (y' ≫ ρ.hom.hom) =
      (y' ≫ ρ.hom.hom) *
        ((algebraPointsEquiv I (AddMonoidAlgebra B (I → ℤ))).symm t ≫ j.hom.hom ≫ ρ.hom.hom) := by
    rw [← Category.assoc, ← MonObj.mul_comp, hcomm.eq, MonObj.mul_comp, Category.assoc]
  have hy' : ∀ a b, (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra B (I → ℤ))) (y' ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra B (I → ℤ))) a b =
      AddMonoidAlgebra.single 0
        ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
          (CommAlgCat.of (CommRingCat.of k) B) (y ≫ ρ.hom.hom) :
            Matrix (Fin N) (Fin N) B) a b) := by
    intro a b
    rw [show y' ≫ ρ.hom.hom = (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
        (AddMonoidAlgebra.singleZeroAlgHom (R := k) (A := B) (M := I → ℤ))).op ≫
          (y ≫ ρ.hom.hom) from Category.assoc _ _ _,
      GeneralLinear.affinePointsEquiv_naturality, Matrix.GeneralLinearGroup.map_apply]
    exact AddMonoidAlgebra.singleZeroAlgHom_apply (R := k) (A := B) (M := I → ℤ) _
  let Ma : Matrix (Fin N) (Fin N) (AddMonoidAlgebra B (I → ℤ)) :=
    GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra B (I → ℤ)))
        ((algebraPointsEquiv I (AddMonoidAlgebra B (I → ℤ))).symm t ≫ j.hom.hom ≫ ρ.hom.hom)
  let My' : Matrix (Fin N) (Fin N) (AddMonoidAlgebra B (I → ℤ)) :=
    GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra B (I → ℤ))) (y' ≫ ρ.hom.hom)
  have hmat : Ma * My' = My' * Ma := by
    have := congrArg (fun x => ((GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra B (I → ℤ))) x :
        Matrix.GeneralLinearGroup (Fin N) (AddMonoidAlgebra B (I → ℤ))) :
          Matrix (Fin N) (Fin N) (AddMonoidAlgebra B (I → ℤ)))) hρ
    simpa only [map_mul, Units.val_mul] using this
  ext a b
  have h := congrArg (fun z : AddMonoidAlgebra B (I → ℤ) => z.coeff m₀)
    (congrFun (congrFun hmat a) b)
  simp only [Matrix.mul_apply, Ma, My', hy'] at h
  simp only [affinePointsEquiv_eval ρ I j (A := AddMonoidAlgebra B (I → ℤ))] at h
  simp only [t, exponentValue_monomialUnit_id, monomialUnit_val] at h
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    AddMonoidAlgebra.single_mul_single, add_zero, zero_add, one_mul, mul_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_smul_single, Finset.sum_ite_eq',
    hm₀, ite_true] at h
  simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.smul_def] at h ⊢
  rw [h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The group algebra `k[ℤ^I/Λ]` of a quotient of the exponents. -/
local notation "KΛ" Λ:max => AddMonoidAlgebra k ((I → ℤ) ⧸ Λ)

/-- **The weights generate the characters.** If `ρ ∘ j` is a monomorphism, the exponents of the
nonzero weight matrices generate `ℤ^I`: otherwise the torus point over `k[ℤ^I/Λ]` with
coordinates the classes of the `eᵢ` is nontrivial but has trivial matrix. -/
theorem closure_weights_eq_top (hmono : Mono (j.hom.hom ≫ ρ.hom.hom).left) :
    AddSubgroup.closure {m : I → ℤ | weight ρ I j m ≠ 0} = ⊤ := by
  classical
  have : Mono (j.hom.hom ≫ ρ.hom.hom) := Over.mono_of_mono_left _
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : AddSubgroup (I → ℤ),
      Λ = AddSubgroup.closure {m : I → ℤ | weight ρ I j m ≠ 0} := ⟨_, rfl⟩
  rw [← hΛ]
  let t : I → (KΛ Λ)ˣ :=
    fun i => monomialUnit (QuotientAddGroup.mk' Λ (Pi.single i 1))
  have hmat : GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (KΛ Λ))
        ((algebraPointsEquiv (R := CommRingCat.of k) I (KΛ Λ)).symm t ≫ j.hom.hom ≫
          ρ.hom.hom) = 1 := by
    apply Units.ext
    ext a b
    rw [affinePointsEquiv_eval]
    simp only [t, exponentValue_monomialUnit, monomialUnit_val]
    have hterm : ∀ n ∈ weightSupport ρ I j,
        weight ρ I j n a b • AddMonoidAlgebra.single (QuotientAddGroup.mk' Λ n) (1 : k) =
          weight ρ I j n a b • (1 : KΛ Λ) := by
      intro n _
      by_cases h : weight ρ I j n = 0
      · rw [h]
        simp
      · have hn : QuotientAddGroup.mk' Λ n = 0 :=
          (QuotientAddGroup.eq_zero_iff n).mpr (hΛ ▸ AddSubgroup.subset_closure h)
        rw [hn, AddMonoidAlgebra.one_def]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← Matrix.sum_apply, sum_weight,
      Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hpt : (algebraPointsEquiv (R := CommRingCat.of k) I (KΛ Λ)).symm t = 1 := by
    apply (cancel_mono (j.hom.hom ≫ ρ.hom.hom)).mp
    rw [MonObj.one_comp]
    apply (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) (KΛ Λ))).injective
    rw [hmat, map_one]
  have ht : t = 1 := by
    have := congrArg (algebraPointsEquiv (R := CommRingCat.of k) I (KΛ Λ)) hpt
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have he : ∀ i, Pi.single i (1 : ℤ) ∈ Λ := by
    intro i
    have h := congrArg (fun u : I → (KΛ Λ)ˣ =>
      ((u i : (KΛ Λ)ˣ) : KΛ Λ).coeff) ht
    simp only [t, monomialUnit_val, Pi.one_apply, Units.val_one, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single] at h
    exact (QuotientAddGroup.eq_zero_iff _).mp (Finsupp.single_left_injective one_ne_zero h)
  rw [eq_top_iff]
  intro m _
  have hm : m = ∑ i, m i • Pi.single i (1 : ℤ) := by
    ext i
    simp [Pi.single_apply]
  rw [hm]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (he i) _

end Weights

/-! ### Points over arbitrary test schemes -/

section Points

variable {k : Type u} [Field k]

/-- The structure map `k → Γ(T, 𝒪_T)` of a scheme over `Spec k`. -/
def scalars (T : Over (Spec (CommRingCat.of k))) : k →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.hom.appTop).hom

/-- Pullback of global sections is compatible with the structure maps. -/
theorem scalars_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    a.left.appTop.hom.comp (scalars T) = scalars T' := by
  rw [scalars, scalars, ← Over.w a]
  rfl

/-- On an affine test scheme, the structure map is the algebra map followed by the inverse of
`Γ(Spec B) ≅ B`. -/
theorem scalars_algSpec (B : CommAlgCat (CommRingCat.of k)) :
    scalars ((algSpec (CommRingCat.of k)).obj (op B)) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.comp (algebraMap k B) := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (CommRingCat.of k) B))
  ext r
  exact (congrArg (fun φ => φ.hom r) h).symm

variable {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- **Centrality on all points.** For affine `G`, the weight matrices commute with the matrix
of every point of `G`: every point factors through an affine presentation of `G`. -/
theorem weight_commute_points (hc : IsCentral j) [IsAffine G.X.left]
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (m : I → ℤ) :
    (weight ρ I j m).map (scalars T) *
        (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) =
      (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom) :
          Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) * (weight ρ I j m).map (scalars T) := by
  obtain ⟨⟨B⟩, ⟨ψ⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  let F : B →+* Γ(T.left, ⊤) :=
    (g ≫ ψ.inv).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have h := weight_commute_affine ρ I j hc (B := B) ψ.hom m
  have e₁ : (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom) :
      Matrix (Fin N) (Fin N) Γ(T.left, ⊤)) =
      (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k) B (ψ.hom ≫ ρ.hom.hom) :
        Matrix (Fin N) (Fin N) B).map F := by
    have hg : g ≫ ρ.hom.hom = (g ≫ ψ.inv) ≫ (ψ.hom ≫ ρ.hom.hom) := by simp
    rw [hg, GeneralLinear.pointsEquiv_naturality, GeneralLinear.pointsEquiv_eq_affinePointsEquiv]
    rfl
  have e₂ : (weight ρ I j m).map (scalars T) = ((weight ρ I j m).map (algebraMap k B)).map F := by
    rw [← scalars_naturality (g ≫ ψ.inv), scalars_algSpec, Matrix.map_map]
    rfl
  rw [e₁, e₂, ← Matrix.map_mul, ← Matrix.map_mul, h]

/-! ### The block characters -/

variable (hc : IsCentral j) [IsAffine G.X.left] (m : I → ℤ) {d : ℕ}
  (U : Matrix (Fin N) (Fin d) k) (V : Matrix (Fin d) (Fin N) k)
  (hUV : U * V = weight ρ I j m) (hVU : V * U = 1)

include hVU in
/-- The identity `V U = 1` survives the passage to global sections. -/
theorem map_mul_map_eq_one (T : Over (Spec (CommRingCat.of k))) :
    V.map (scalars T) * U.map (scalars T) = 1 := by
  rw [← Matrix.map_mul, hVU, Matrix.map_one _ (map_zero _) (map_one _)]

include hc hUV in
/-- The matrix of every point of `G` commutes with the idempotent `U V = P_m`, over global
sections. -/
theorem commute_blockIdempotent (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom)).val *
        (U.map (scalars T) * V.map (scalars T)) =
      U.map (scalars T) * V.map (scalars T) *
        (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom)).val := by
  rw [← Matrix.map_mul, hUV]
  exact (weight_commute_points ρ I j hc T g m).symm

/-- The block of `ρ` on the image of the weight idempotent `P_m = U V`, on points over every
test scheme: `g ↦ V ρ(g) U`. -/
def blockPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ G.X) →* Matrix.GeneralLinearGroup (Fin d) Γ(T.left, ⊤) where
  toFun g := compress (U.map (scalars T)) (V.map (scalars T)) (map_mul_map_eq_one U V hVU T)
    (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom))
    (commute_blockIdempotent ρ I j hc m U V hUV T g)
  map_one' := by
    apply Units.ext
    rw [compress_val, MonObj.one_comp, map_one, Units.val_one, Units.val_one, Matrix.mul_one,
      map_mul_map_eq_one U V hVU T]
  map_mul' g h := by
    apply Units.ext
    rw [Units.val_mul, compress_val, compress_val, compress_val, MonObj.mul_comp, map_mul,
      Units.val_mul, compress_mul_compress _ _ (map_mul_map_eq_one U V hVU T)
        (commute_blockIdempotent ρ I j hc m U V hUV T h)]

/-- The underlying matrix of the block points is `V ρ(g) U`. -/
theorem blockPoints_val (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    (blockPoints ρ I j hc m U V hUV hVU T g).val =
      V.map (scalars T) *
        (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) T (g ≫ ρ.hom.hom)).val *
          U.map (scalars T) := rfl

/-- The block points are natural in the test scheme. -/
theorem blockPoints_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (g : T ⟶ G.X) :
    blockPoints ρ I j hc m U V hUV hVU T' (a ≫ g) =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (blockPoints ρ I j hc m U V hUV hVU T g) := by
  apply Units.ext
  rw [val_map, blockPoints_val, blockPoints_val, Category.assoc,
    GeneralLinear.pointsEquiv_naturality, val_map, ← scalars_naturality a,
    Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map]
  rfl

/-- Naturality of the block points, valued in points of `GL_d`. -/
theorem blockPointsSymm_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    ((GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T').symm.toMonoidHom.comp
        (blockPoints ρ I j hc m U V hUV hVU T')) (a ≫ x) =
      a ≫ ((GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T).symm.toMonoidHom.comp
        (blockPoints ρ I j hc m U V hUV hVU T)) x := by
  apply (GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T').injective
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply, GeneralLinear.pointsEquiv_naturality]
  exact blockPoints_naturality ρ I j hc m U V hUV hVU a x

/-- The block representation `g ↦ V ρ(g) U` of `G` on the image of `P_m`. -/
def blockRepresentation : MatrixRepresentation G (Fin d) :=
  homOfPoints
    (fun T => (GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T).symm.toMonoidHom.comp
      (blockPoints ρ I j hc m U V hUV hVU T))
    (blockPointsSymm_naturality ρ I j hc m U V hUV hVU)

/-- On points, the block representation is the block points. -/
theorem pointsEquiv_blockRepresentation (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    GeneralLinear.pointsEquiv (Fin d) (CommRingCat.of k) T
        (g ≫ (blockRepresentation ρ I j hc m U V hUV hVU).hom.hom) =
      blockPoints ρ I j hc m U V hUV hVU T g := by
  rw [blockRepresentation, comp_homOfPoints _ (blockPointsSymm_naturality ρ I j hc m U V hUV hVU)]
  exact MulEquiv.apply_symm_apply _ _

/-- The block character `det (V ρ U)` of `G`. -/
def blockCharacter : rationalCharacters G :=
  characterRestrict (blockRepresentation ρ I j hc m U V hUV hVU)
    (GeneralLinear.determinantCharacter (Fin d) (CommRingCat.of k))

/-- On points, the block character is the determinant of the block points. -/
theorem characterEval_blockCharacter (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    characterEval (blockCharacter ρ I j hc m U V hUV hVU) T g =
      Matrix.GeneralLinearGroup.det (blockPoints ρ I j hc m U V hUV hVU T g) := by
  rw [blockCharacter, characterEval_characterRestrict,
    GeneralLinear.characterEval_determinantCharacter, pointsEquiv_blockRepresentation]

/-! ### Restriction of the block characters to the split torus -/

omit [IsAffine G.X.left] in
include hUV hVU in
/-- The compressions of the weight matrices: `V P_n U` is `1` for `n = m` and `0` otherwise. -/
theorem compress_weight (n : I → ℤ) :
    V * weight ρ I j n * U = if n = m then 1 else 0 := by
  have hV : V = V * weight ρ I j m := by rw [← hUV, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  by_cases h : n = m
  · subst h
    rw [ite_eq_left rfl, ← hUV, ← Matrix.mul_assoc, hVU, Matrix.one_mul, hVU]
  · rw [ite_eq_right h, hV, Matrix.mul_assoc V, weight_mul_weight, ite_eq_right (Ne.symm h),
      Matrix.mul_zero,
      Matrix.zero_mul]

variable (k) in
/-- The comparison `Γ(Spec B) ≅ B` for the relative spectrum of a `k`-algebra `B`. -/
def sectionsHom (B : Type u) [CommRing B] [Algebra k B] :
    Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) B))).left, ⊤) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom

/-- The comparison `Γ(Spec B) ≅ B` inverts `(ΓSpecIso B).inv`. -/
theorem sectionsHom_inv {B : Type u} [CommRing B] [Algebra k B] (x : B) :
    sectionsHom k B ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom x) = x := by
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom x = x
  rw [Iso.inv_hom_id]
  rfl

/-- On the relative spectrum of `B`, the structure map read in `B` is the algebra map. -/
theorem sectionsHom_comp_scalars (B : Type u) [CommRing B] [Algebra k B] :
    (sectionsHom k B).comp
      (scalars ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) B)))) =
      algebraMap k B := by
  rw [scalars_algSpec]
  ext x
  exact sectionsHom_inv _

/-- Matrix points over the relative spectrum of `B`, read in `B`, are the affine matrix points. -/
theorem map_sectionsHom_pointsEquiv {B : Type u} [CommRing B] [Algebra k B] {n : Type}
    [Fintype n] [DecidableEq n]
    (x : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) B)) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X) :
    (GeneralLinear.pointsEquiv n (CommRingCat.of k) _ x).val.map (sectionsHom k B) =
      (GeneralLinear.affinePointsEquiv n (CommRingCat.of k)
        (CommAlgCat.of (CommRingCat.of k) B) x).val := by
  rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv, val_map, Matrix.map_map]
  ext a b
  exact sectionsHom_inv _

/-- On the torus point with unit coordinates `t` over a `k`-algebra `B`, the block matrix is the
scalar `tᵐ`. -/
theorem blockPoints_torus {B : Type u} [CommRing B] [Algebra k B] (t : I → Bˣ) :
    (blockPoints ρ I j hc m U V hUV hVU
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) B)))
        ((algebraPointsEquiv I B).symm t ≫ j.hom.hom)).val.map (sectionsHom k B) =
      ((exponentValue I t (Multiplicative.ofAdd m) : Bˣ) : B) • (1 : Matrix (Fin d) (Fin d) B) := by
  classical
  have hM : (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) B)
        (((algebraPointsEquiv I B).symm t ≫ j.hom.hom) ≫ ρ.hom.hom)).val =
      ∑ n ∈ weightSupport ρ I j,
        ((exponentValue I t (Multiplicative.ofAdd n) : Bˣ) : B) •
          (weight ρ I j n).map (algebraMap k B) := by
    ext a b
    rw [Matrix.sum_apply, Category.assoc, affinePointsEquiv_eval]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, smul_eq_mul, mul_comm]
  rw [blockPoints_val, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    ← RingHom.coe_comp, sectionsHom_comp_scalars,
    map_sectionsHom_pointsEquiv, hM, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hc' : ∀ n, V.map (algebraMap k B) * (weight ρ I j n).map (algebraMap k B) *
      U.map (algebraMap k B) = (if n = m then (1 : Matrix (Fin d) (Fin d) k) else 0).map
        (algebraMap k B) := fun n => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, compress_weight ρ I j m U V hUV hVU]
  simp only [hc']
  by_cases hm : m ∈ weightSupport ρ I j
  · rw [Finset.sum_eq_single m]
    · rw [ite_eq_left rfl, Matrix.map_one _ (map_zero _) (map_one _)]
    · intro n _ hn
      rw [ite_eq_right hn, Matrix.map_zero _ (map_zero _), smul_zero]
    · intro h
      exact absurd hm h
  · -- the block is empty: `1 = V P_m U = 0` in size `d`
    have h1 : (1 : Matrix (Fin d) (Fin d) k) = 0 := by
      have h := compress_weight ρ I j m U V hUV hVU m
      rw [ite_eq_left rfl, weight_eq_zero ρ I j hm, Matrix.mul_zero, Matrix.zero_mul] at h
      exact h.symm
    have hd : d = 0 := by
      by_contra hd
      have := congrFun (congrFun h1 ⟨0, Nat.pos_of_ne_zero hd⟩) ⟨0, Nat.pos_of_ne_zero hd⟩
      simp at this
    subst hd
    exact Subsingleton.elim _ _

variable (k) in
/-- The characters of the split torus: `X^*(𝔾_m^I) ≃ ℤ^I`. -/
def torusCharacterEquiv : rationalCharacters (splitTorus (Spec (CommRingCat.of k)) I) ≃+ (I → ℤ) :=
  (rationalCharacters.equivCharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)).trans
    (characterLatticeEquiv k I)

omit [DecidableEq I] in
/-- The value of a torus character on a point over a `k`-algebra `B`, read in `B`, is the
exponent monomial in the unit coordinates of the point. -/
theorem sectionsHom_characterEval_torus {B : Type u} [CommRing B] [Algebra k B] (n : I → ℤ)
    (y : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) B) :
    sectionsHom k B (characterEval ((torusCharacterEquiv k I).symm n) _ y : _) =
      (exponentValue I (algebraPointsEquiv I B y) (Multiplicative.ofAdd n) : Bˣ) := by
  rw [← characterValue_characterLatticeEquiv_symm k I n y]
  rfl

/-- The value of a natural multiple of a character is the power of the value. -/
theorem characterEval_nsmul {H : GroupScheme (Spec (CommRingCat.of k))} (n : ℕ)
    (χ : rationalCharacters H) (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) :
    characterEval (n • χ) T x = characterEval χ T x ^ n := by
  rw [← natCast_zsmul, characterEval_zsmul, zpow_natCast]

/-- Rational characters of an affine group scheme are determined by their values on points over
`k`-algebras. -/
theorem rationalCharacters_ext_affine {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine H.X.left] {χ ψ : rationalCharacters H}
    (h : ∀ (B : CommAlgCat (CommRingCat.of k))
      (y : (algSpec (CommRingCat.of k)).obj (op B) ⟶ H.X),
      characterEval χ _ y = characterEval ψ _ y) : χ = ψ := by
  apply rationalCharacters.ext_characterEval
  intro T x
  obtain ⟨⟨B⟩, ⟨e⟩⟩ := (essImage_algSpec (G := H.X)).mpr inferInstance
  have hx : x = (x ≫ e.inv) ≫ e.hom := by simp
  rw [hx, characterEval_naturality, characterEval_naturality, h B e.hom]

/-- **Restriction of a block character.** The block character `det (V ρ U)` restricts to the
split torus as `d` times the character `m`. -/
theorem characterRestrict_blockCharacter :
    characterRestrict j (blockCharacter ρ I j hc m U V hUV hVU) =
      d • (torusCharacterEquiv k I).symm m := by
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus _ I
  have : IsAffine (splitTorus (Spec (CommRingCat.of k)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom
  apply rationalCharacters_ext_affine
  intro B y
  obtain ⟨t, rfl⟩ := (algebraPointsEquiv I B).symm.surjective y
  have hinj : Function.Injective (sectionsHom k B) := by
    intro a b hab
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom hab
    change ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv).hom b at this
    rwa [Iso.hom_inv_id] at this
  apply Units.ext
  apply hinj
  rw [characterEval_characterRestrict, characterEval_blockCharacter, characterEval_nsmul,
    Units.val_pow_eq_pow_val, map_pow]
  erw [sectionsHom_characterEval_torus]
  rw [MulEquiv.apply_symm_apply]
  change sectionsHom k B (blockPoints ρ I j hc m U V hUV hVU _ _).val.det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, blockPoints_torus, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]

end Points

/-! ### Finite index -/

section FiniteIndex

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- For a central `j : 𝔾_m^I ⟶ G` of an affine `G` and a representation `ρ` with `ρ ∘ j` a
monomorphism, some nonzero multiple of every character of the torus is a restriction from `G`:
the product `D` of the block sizes works, since the block characters restrict to the block sizes
times the weights, and the weights generate. -/
theorem exists_nsmul_mem_range (hc : IsCentral j) [IsAffine G.X.left]
    (hmono : Mono (j.hom.hom ≫ ρ.hom.hom).left) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ χ : rationalCharacters (splitTorus (Spec (CommRingCat.of k)) I),
      D • χ ∈ (characterRestrict j).range := by
  classical
  let W := (weightSupport ρ I j).filter fun m => weight ρ I j m ≠ 0
  have hfac : ∀ m, ∃ (d : ℕ) (U : Matrix (Fin N) (Fin d) k) (V : Matrix (Fin d) (Fin N) k),
      U * V = weight ρ I j m ∧ V * U = 1 := fun m =>
    exists_factor_of_mul_self _ (by rw [weight_mul_weight, ite_eq_left rfl])
  choose d U V hUV hVU using hfac
  let D := ∏ m ∈ W, d m
  have hD : D ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro m hm
    exact ne_zero_of_factor (hUV m) (Finset.mem_filter.mp hm).2
  let S : AddSubgroup (I → ℤ) :=
    { carrier := {n | D • (torusCharacterEquiv k I).symm n ∈ (characterRestrict j).range}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, nsmul_add] at ha hb ⊢
        exact AddSubgroup.add_mem _ ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, smul_zero]
        exact AddSubgroup.zero_mem _
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_neg, smul_neg] at ha ⊢
        exact AddSubgroup.neg_mem _ ha }
  have hW : {m : I → ℤ | weight ρ I j m ≠ 0} ⊆ S := by
    intro m hm
    have hmW : m ∈ W := Finset.mem_filter.mpr
      ⟨by by_contra h; exact hm (weight_eq_zero ρ I j h), hm⟩
    obtain ⟨c, hcD⟩ := Finset.dvd_prod_of_mem d hmW
    refine ⟨c • blockCharacter ρ I j hc m (U m) (V m) (hUV m) (hVU m), ?_⟩
    change characterRestrict j (c • blockCharacter ρ I j hc m (U m) (V m) (hUV m) (hVU m)) =
      D • (torusCharacterEquiv k I).symm m
    rw [map_nsmul, characterRestrict_blockCharacter, ← mul_smul, mul_comm, ← hcD]
  have hS : S = ⊤ := top_unique (by
    rw [← closure_weights_eq_top ρ I j hmono]
    exact (AddSubgroup.closure_le S).mpr hW)
  refine ⟨D, hD, fun χ => ?_⟩
  have h : D • (torusCharacterEquiv k I).symm (torusCharacterEquiv k I χ) ∈
      (characterRestrict j).range := (hS ▸ AddSubgroup.mem_top _ : torusCharacterEquiv k I χ ∈ S)
  rwa [AddEquiv.symm_apply_apply] at h

/-- **Finite index for central split tori.** For an affine group `G` of finite type over a
field and a central split torus `i : A ⟶ G`, the restriction `X^*(G)_k → X^*(A)` has
finite-index range. -/
theorem finiteIndex_range_characterRestrict [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (i : A.toGrp ⟶ G)
    (hi : IsCentralSplitTorus i) : (characterRestrict i).range.FiniteIndex := by
  classical
  obtain ⟨⟨⟨J, hJ, ⟨e⟩⟩, hclosed⟩, hcentral⟩ := hi
  let _ : Fintype J := Fintype.ofFinite J
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hcj : IsCentral (e.inv ≫ i) := hcentral.comp e.inv
  have hmono : Mono ((e.inv ≫ i).hom.hom ≫ ρ.hom.hom).left := by
    have : IsClosedImmersion i.hom.hom.left := hclosed
    have : IsClosedImmersion ρ.hom.hom.left := hρ
    have : IsIso e.inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map e.inv)))
    change Mono (e.inv.hom.hom.left ≫ i.hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  obtain ⟨D, hD, hDj⟩ := exists_nsmul_mem_range ρ J (e.inv ≫ i) hcj hmono
  have hres : ∀ ψ : rationalCharacters A.toGrp,
      characterRestrict e.hom (characterRestrict e.inv ψ) = ψ := fun ψ => by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.hom_inv_id, characterRestrict_id]
    rfl
  have hres' : ∀ ψ : rationalCharacters (splitTorus (Spec (CommRingCat.of k)) J),
      characterRestrict e.inv (characterRestrict e.hom ψ) = ψ := fun ψ => by
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, e.inv_hom_id, characterRestrict_id]
    rfl
  let Ψ : rationalCharacters A.toGrp ≃+
      rationalCharacters (splitTorus (Spec (CommRingCat.of k)) J) :=
    { toFun := characterRestrict e.inv
      invFun := characterRestrict e.hom
      left_inv := hres
      right_inv := hres'
      map_add' := map_add _ }
  have : Module.Finite ℤ (rationalCharacters A.toGrp) :=
    Module.Finite.equiv (Ψ.trans (torusCharacterEquiv k J)).symm.toIntLinearEquiv
  refine finiteIndex_of_nsmul_mem _ hD fun ψ => ?_
  obtain ⟨φ, hφ⟩ := hDj (characterRestrict e.inv ψ)
  refine ⟨φ, ?_⟩
  rw [← hres (D • ψ), map_nsmul, ← hφ, characterRestrict_comp, AddMonoidHom.comp_apply, hres]

end FiniteIndex

end Langlands.GroupScheme.CharacterRestrictionFiniteIndex

namespace Langlands.GroupScheme

/-- **Renard V.2.6, finite index.** For a split component `i : A ⟶ G` of a connected reductive
group `G` over a field, the restriction `X^*(G)_k → X^*(A)` has finite-index range. -/
theorem IsSplitComponent.finiteIndex_range_characterRestrict {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G}
    (hi : IsSplitComponent i) : (characterRestrict i).range.FiniteIndex := by
  have := hG.isAffineHom
  have := hG.smooth
  exact CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict i
    hi.isCentralSplitTorus

end Langlands.GroupScheme
