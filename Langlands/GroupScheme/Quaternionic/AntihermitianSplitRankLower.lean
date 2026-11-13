import Langlands.GroupScheme.Quaternionic.AntihermitianWittBasis
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankLower
import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion

/-!
# Lower bound for the split rank of the symplectic group of an antihermitian form

For weights `w : n → ℤ^I` and a Gram matrix `G ∈ M_n(D)` supported where the weights add up to
zero, with weights adding up to zero, the diagonal torus `t ↦ diag(t^{w i})` is a split torus of
the symplectic group of `G`; it is closed when every standard basis vector of `ℤ^I` is a weight.
A Witt basis of an invertible trace-valued antihermitian `H` of Witt index `r` puts `H` in such a
form with `I = Fin r`, so the Witt index is at most the split rank.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.AntihermitianSplitRank

open Quaternionic CentralSimpleUnits.MatrixDiagonalTorus FiniteAlgebraUnits.MatrixPoints

/-! ### Monomials -/

section Monomial

variable {I : Type*} [Fintype I] {R : Type*} [CommRing R]

/-- The monomial `t ↦ tᵃ = ∏ₖ t_k^{a_k}` on families of units. -/
def monomial (a : I → ℤ) : (I → Rˣ) →* Rˣ where
  toFun t := ∏ k, t k ^ a k
  map_one' := by simp
  map_mul' t s := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem monomial_apply (a : I → ℤ) (t : I → Rˣ) : monomial a t = ∏ k, t k ^ a k := rfl

theorem monomial_add (a b : I → ℤ) (t : I → Rˣ) :
    monomial (a + b) t = monomial a t * monomial b t := by
  simp only [monomial_apply, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem monomial_zero (t : I → Rˣ) : monomial (0 : I → ℤ) t = 1 := by
  simp [monomial_apply]

theorem monomial_single [DecidableEq I] (k : I) (t : I → Rˣ) :
    monomial (Pi.single k 1) t = t k := by
  rw [monomial_apply, Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem monomial_sum {J : Type*} (s : Finset J) (a : J → I → ℤ) (t : I → Rˣ) :
    monomial (∑ i ∈ s, a i) t = ∏ i ∈ s, monomial (a i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, monomial_add, ih]

theorem map_monomial {S : Type*} [CommRing S] (φ : Rˣ →* Sˣ) (a : I → ℤ) (t : I → Rˣ) :
    φ (monomial a t) = monomial a (fun k => φ (t k)) := by
  simp [monomial_apply, map_prod, map_zpow]

end Monomial

/-! ### Weighted diagonal units -/

section Units

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  {n : Type} [Fintype n] [DecidableEq n] {I : Type u} [Fintype I] (w : n → I → ℤ)
  (R : Type u) [CommRing R] [Algebra K R]

/-- The weighted diagonal torus on coefficient points: `t ↦ diag(t^{w i})`. -/
def weightUnits : (I → Rˣ) →* (R ⊗[K] Matrix n n D)ˣ where
  toFun t := diagUnit K D R fun i => monomial (w i) t
  map_one' := by
    apply Units.ext
    change diagRingHom K D R (fun i => ((monomial (w i) 1 : Rˣ) : R)) = 1
    rw [← map_one (diagRingHom K D R (J := n))]
    congr 1
    funext i
    simp
  map_mul' t s := by
    apply Units.ext
    change diagRingHom K D R (fun i => ((monomial (w i) (t * s) : Rˣ) : R)) =
      diagRingHom K D R (fun i => ((monomial (w i) t : Rˣ) : R)) *
        diagRingHom K D R (fun i => ((monomial (w i) s : Rˣ) : R))
    rw [← map_mul]
    congr 1
    funext i
    simp

theorem weightUnits_val (t : I → Rˣ) :
    (weightUnits K D w R t : R ⊗[K] Matrix n n D) =
      diagRingHom K D R (fun i => ((monomial (w i) t : Rˣ) : R)) :=
  rfl

theorem coefficientEquiv_weightUnits (t : I → Rˣ) :
    coefficientEquiv K D R (weightUnits K D w R t : R ⊗[K] Matrix n n D) =
      Matrix.diagonal fun i => ((monomial (w i) t : Rˣ) : R) ⊗ₜ[K] (1 : D) := by
  rw [weightUnits_val, coefficientEquiv_diagRingHom]

variable {R} in
/-- The weighted diagonal torus commutes with every coefficient-algebra homomorphism. -/
theorem weightUnits_map {S : Type u} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (t : I → Rˣ) :
    Units.map (Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n D))).toMonoidHom
        (weightUnits K D w R t) =
      weightUnits K D w S (fun k => Units.map f.toMonoidHom (t k)) := by
  apply Units.ext
  change Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n D))
      (weightUnits K D w R t : R ⊗[K] Matrix n n D) = _
  rw [weightUnits_val, weightUnits_val, diagRingHom_map]
  congr 1
  funext i
  rw [← map_monomial (Units.map f.toMonoidHom) (w i) t]
  rfl

/-- The weighted diagonal torus is injective when every standard basis vector is a weight. -/
theorem weightUnits_injective [DecidableEq I] (hsep : ∀ k, ∃ i, w i = Pi.single k 1) :
    Function.Injective (weightUnits K D w R) := by
  intro t s h
  have h1 := congrArg (fun x : (R ⊗[K] Matrix n n D)ˣ => (x : R ⊗[K] Matrix n n D)) h
  simp only [weightUnits_val] at h1
  have h2 := diagRingHom_injective K D R h1
  funext k
  obtain ⟨i, hi⟩ := hsep k
  have h3 := congrFun h2 i
  simp only [hi, monomial_single] at h3
  exact Units.ext h3

/-- The weighted diagonal torus consists of isometries of a Gram matrix supported where the
weights add up to zero. -/
theorem weightUnits_isometry (σ : FirstKindInvolution K D) (G : Matrix n n D)
    (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0) (t : I → Rˣ) :
    coefficientEquiv K D R (weightUnits K D w R t : R ⊗[K] Matrix n n D) *
        G.map (Algebra.TensorProduct.includeRight : D →ₐ[K] R ⊗[K] D) *
        (σ.baseChange R).matrix n
          (coefficientEquiv K D R (weightUnits K D w R t : R ⊗[K] Matrix n n D)) =
      G.map (Algebra.TensorProduct.includeRight : D →ₐ[K] R ⊗[K] D) := by
  rw [coefficientEquiv_weightUnits]
  have hd : (σ.baseChange R).matrix n
      (Matrix.diagonal fun i => ((monomial (w i) t : Rˣ) : R) ⊗ₜ[K] (1 : D)) =
      Matrix.diagonal fun i => ((monomial (w i) t : Rˣ) : R) ⊗ₜ[K] (1 : D) := by
    ext i j
    rw [FirstKindInvolution.matrix_apply]
    by_cases h : i = j
    · subst h
      simp [FirstKindInvolution.baseChange_tmul]
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h,
        FirstKindInvolution.map_zero]
  rw [hd]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
    Algebra.TensorProduct.includeRight_apply]
  by_cases h : G i j = 0
  · simp [h]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one, one_mul]
    rw [← Units.val_mul, ← monomial_add, hG i j h, monomial_zero, Units.val_one]

/-- The weighted diagonal torus has reduced norm one when the weights add up to zero. -/
theorem reducedNorm_weightUnits [FiniteDimensional K D] [Algebra.IsCentral K D] [Nonempty n]
    (hsum : ∑ i, w i = 0) (t : I → Rˣ) :
    Langlands.CentralSimple.reducedNorm K (Matrix n n D) R
      (weightUnits K D w R t : R ⊗[K] Matrix n n D) = 1 := by
  rw [weightUnits_val]
  apply reducedNorm_diagRingHom_eq_one
  rw [← Units.coe_prod, ← monomial_sum, hsum, monomial_zero, Units.val_one]

end Units

/-! ### The weighted diagonal torus of the symplectic group -/

section Scheme

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
  {I : Type u} [Fintype I] (w : n → I → ℤ)

local notation "𝕊" => splitTorus (Spec (CommRingCat.of K)) I

local notation "𝔸" => FirstKindInvolution.ambientUnits K D n

local notation "𝔟" => Module.finBasis K (Matrix n n D)

/-- The weighted diagonal torus on actual points. -/
def weightPoints (T : Over (Spec (CommRingCat.of K))) : (T ⟶ (𝕊).X) →* (T ⟶ (𝔸).X) :=
  (FiniteAlgebraUnits.pointsEquiv 𝔟 T).symm.toMonoidHom.comp
    ((weightUnits K D w ((algΓ (CommRingCat.of K)).obj T).unop).comp
      (splitTorus.pointsEquiv I T).toMonoidHom)

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem pointsEquiv_weightPoints (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕊).X) :
    FiniteAlgebraUnits.pointsEquiv 𝔟 T (weightPoints (K := K) (D := D) w T x) =
      weightUnits K D w ((algΓ (CommRingCat.of K)).obj T).unop (splitTorus.pointsEquiv I T x) :=
  (FiniteAlgebraUnits.pointsEquiv 𝔟 T).apply_symm_apply _

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem weightPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (𝕊).X) :
    weightPoints (K := K) (D := D) w T' (a ≫ x) = a ≫ weightPoints (K := K) (D := D) w T x := by
  apply (FiniteAlgebraUnits.pointsEquiv 𝔟 T').injective
  rw [FiniteAlgebraUnits.pointsEquiv_naturality, pointsEquiv_weightPoints,
    pointsEquiv_weightPoints, splitTorus.pointsEquiv_naturality]
  exact (weightUnits_map K D w (((algΓ (CommRingCat.of K)).map a).unop.hom) _).symm

/-- The weighted diagonal torus of the unit group of `M_n(D)`. -/
def weightHom : 𝕊 ⟶ 𝔸 :=
  homOfPoints (weightPoints (K := K) (D := D) w) (weightPoints_naturality w)

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem pointsEquiv_comp_weightHom (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕊).X) :
    FiniteAlgebraUnits.pointsEquiv 𝔟 T (x ≫ (weightHom (K := K) (D := D) w).hom.hom) =
      weightUnits K D w ((algΓ (CommRingCat.of K)).obj T).unop (splitTorus.pointsEquiv I T x) := by
  rw [weightHom, comp_homOfPoints, pointsEquiv_weightPoints]

omit [Algebra.IsCentral K D] [Nonempty n] in
theorem mono_weightHom [DecidableEq I] (hsep : ∀ k, ∃ i, w i = Pi.single k 1) :
    Mono (weightHom (K := K) (D := D) w).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv I Z).injective
  have h1 := congrArg (FiniteAlgebraUnits.pointsEquiv 𝔟 Z) hgh
  rw [pointsEquiv_comp_weightHom, pointsEquiv_comp_weightHom] at h1
  exact weightUnits_injective K D w ((algΓ (CommRingCat.of K)).obj Z).unop hsep h1

/-- The weighted diagonal torus lies in the symplectic group of a Gram matrix supported where
the weights add up to zero, when the weights add up to zero. -/
theorem range_weightHom_le (G : Matrix n n D) (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0)
    (hsum : ∑ i, w i = 0) :
    SubgroupFunctor.range (weightHom (K := K) (D := D) w) ≤
      SubgroupFunctor.range (σ.symplecticAmbientι G) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  rw [σ.mem_range_symplecticAmbientι_iff]
  constructor
  · rw [σ.mem_range_unitaryGroupι_iff, pointsEquiv_comp_weightHom,
      FirstKindInvolution.isometry_iff_coefficientEquiv]
    exact weightUnits_isometry K D w _ σ G hG _
  · apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).injective
    rw [CentralSimpleUnits.reducedNormHom_points, pointsEquiv_comp_weightHom, map_one]
    apply Units.ext
    rw [Langlands.CentralSimple.reducedNormUnits_val, Units.val_one]
    exact reducedNorm_weightUnits K D w _ hsum _

/-- The weighted diagonal torus of the symplectic group. -/
def symplecticTorus (G : Matrix n n D) (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0)
    (hsum : ∑ i, w i = 0) : 𝕊 ⟶ σ.symplecticGroup G :=
  (σ.isRepresentedBy_symplecticAmbientι G).liftOfLE (weightHom (K := K) (D := D) w)
    (range_weightHom_le σ w G hG hsum)

theorem symplecticTorus_comp (G : Matrix n n D) (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0)
    (hsum : ∑ i, w i = 0) :
    symplecticTorus σ w G hG hsum ≫ σ.symplecticAmbientι G = weightHom (K := K) (D := D) w :=
  SubgroupFunctor.IsRepresentedBy.liftOfLE_comp _ _ _

/-- The weighted diagonal torus is a closed split torus of the symplectic group. -/
theorem isClosedSubgroup_symplecticTorus [DecidableEq I] (G : Matrix n n D)
    (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0) (hsum : ∑ i, w i = 0)
    (hsep : ∀ k, ∃ i, w i = Pi.single k 1) :
    IsClosedSubgroup (symplecticTorus σ w G hG hsum) := by
  have hm : Mono (symplecticTorus σ w G hG hsum).hom.hom := by
    have := mono_weightHom (K := K) (D := D) w hsep
    rw [← symplecticTorus_comp σ w G hG hsum, Grp.comp_hom_hom] at this
    exact mono_of_mono _ (σ.symplecticAmbientι G).hom.hom
  have := isAffineHom_splitTorus (Spec (CommRingCat.of K)) I
  have hc : IsClosedImmersion (σ.symplecticAmbientι G).hom.hom.left :=
    σ.isClosedSubgroup_symplecticAmbientι G
  have : IsAffineHom (σ.symplecticGroup G).X.hom := by
    rw [← (σ.symplecticAmbientι G).hom.hom.w]
    infer_instance
  have : LocallyOfFiniteType (σ.symplecticGroup G).X.hom := by
    rw [← (σ.symplecticAmbientι G).hom.hom.w]
    infer_instance
  exact IsTorus.isClosedSubgroup_of_mono (IsSplitTorus.isTorus (isSplitTorus_splitTorus _)) _

/-- **Split tori from weights.** -/
theorem card_le_splitRank_of_weights [DecidableEq I] (G : Matrix n n D)
    (hG : ∀ i j, G i j ≠ 0 → w i + w j = 0) (hsum : ∑ i, w i = 0)
    (hsep : ∀ k, ∃ i, w i = Pi.single k 1) :
    (Fintype.card I : ℕ∞) ≤ splitRank (σ.symplecticGroup G) := by
  have h := card_le_splitRank I (symplecticTorus σ w G hG hsum)
    (isClosedSubgroup_symplecticTorus σ w G hG hsum hsep)
  rwa [Nat.card_eq_fintype_card] at h

end Scheme

/-! ### The lower bound -/

section Main

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (σ : FirstKindInvolution K D) {m : ℕ} [NeZero m]
  (H : Matrix (Fin m) (Fin m) D)

/-- **Lower bound.** The Witt index of an invertible trace-valued antihermitian `H` is at most
the split rank of its symplectic group. -/
theorem wittIndex_le_splitRank (hH : σ.IsAntihermitian H) (hu : IsUnit H) :
    (σ.wittIndex H : ℕ∞) ≤ splitRank (σ.symplecticGroup H) := by
  obtain ⟨P, w, hP, hG, hsum, hsep⟩ := exists_wittBasis hH hu
  have e := σ.symplecticGroupCongr hP.unit H
  rw [IsUnit.unit_spec] at e
  rw [splitRank_eq_of_iso e]
  let w' : Fin m → ULift.{u} (Fin (σ.wittIndex H)) → ℤ := fun i k => w i k.down
  have hG' : ∀ i j, (P * H * σ.matrix (Fin m) P) i j ≠ 0 → w' i + w' j = 0 := by
    intro i j h
    funext k
    exact congrFun (hG i j h) k.down
  have hsum' : ∑ i, w' i = 0 := by
    funext k
    have := congrFun hsum k.down
    simpa [w', Finset.sum_apply] using this
  have hsep' : ∀ k, ∃ i, w' i = Pi.single k 1 := by
    intro k
    obtain ⟨i, hi⟩ := hsep k.down
    refine ⟨i, funext fun l => ?_⟩
    simp only [w', hi, Pi.single_apply, ULift.ext_iff]
  have h := card_le_splitRank_of_weights σ w' _ hG' hsum' hsep'
  simpa using h

end Main

end Langlands.GroupScheme.AntihermitianSplitRank
