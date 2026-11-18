import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Smooth
import Langlands.GroupScheme.Torus.SelfCentralizingFromLie
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Reductive.RootDatum

/-! # The rank-two torus of the split Cayley automorphism group scheme and its weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme

namespace SplitCayley

/-! ### Weights of the coordinates and of the roots -/

/-- The torus weights of the eight coordinates, in the coordinates `(s, t)` of the torus:
the torus element with parameters `(s, t)` scales coordinate `i` by `s ^ w(i)₀ * t ^ w(i)₁`. -/
def weightCoord : Fin 8 → Fin 2 → ℤ :=
  ![0, ![1, 0], ![0, 1], ![-1, -1], ![-1, 0], ![0, -1], ![1, 1], 0]

/-- The weight of each root, in the coordinates `(s, t)` of the torus. -/
def rootWeight : Root → Fin 2 → ℤ
  | .u1 => ![1, 0]
  | .u2 => ![0, 1]
  | .u3 => ![-1, -1]
  | .v1 => ![-1, 0]
  | .v2 => ![0, -1]
  | .v3 => ![1, 1]
  | .l12 => ![1, -1]
  | .l13 => ![2, 1]
  | .l21 => ![-1, 1]
  | .l23 => ![1, 2]
  | .l31 => ![-2, -1]
  | .l32 => ![-1, -2]

theorem rootWeight_ne_zero (α : Root) : rootWeight α ≠ 0 := by
  cases α <;> decide

section Units

variable {A : Type*} [CommRing A]

theorem torusEntries_eq_prod (τ : ULift.{u} (Fin 2) → Aˣ) (i : Fin 8) :
    torusEntries (τ ⟨0⟩) (τ ⟨1⟩) i = ∏ c : ULift.{u} (Fin 2), τ c ^ weightCoord i c.down := by
  rw [Fintype.prod_equiv Equiv.ulift (fun c => τ c ^ weightCoord i c.down)
    (fun c => τ ⟨c⟩ ^ weightCoord i c) (fun _ => rfl), Fin.prod_univ_two]
  fin_cases i <;> simp [torusEntries, weightCoord]

theorem prod_zpow_weightCoord_sub (τ : ULift.{u} (Fin 2) → Aˣ) (p q : Fin 8) :
    ∏ c : ULift.{u} (Fin 2), τ c ^ ((weightCoord p - weightCoord q) c.down) =
      torusEntries (τ ⟨0⟩) (τ ⟨1⟩) p * (torusEntries (τ ⟨0⟩) (τ ⟨1⟩) q)⁻¹ := by
  rw [torusEntries_eq_prod, torusEntries_eq_prod, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Pi.sub_apply, _root_.zpow_sub]

theorem torusEntries_mulSingle (c : ULift.{u} (Fin 2)) (U : Aˣ) (i : Fin 8) :
    torusEntries ((Pi.mulSingle c U : ULift.{u} (Fin 2) → Aˣ) ⟨0⟩)
        ((Pi.mulSingle c U : ULift.{u} (Fin 2) → Aˣ) ⟨1⟩) i =
      U ^ weightCoord i c.down := by
  rw [torusEntries_eq_prod, GeneralLinear.prod_mulSingle_zpow]

theorem torusGL_inv_val (s t : Aˣ) :
    (((torusGL s t)⁻¹ : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A) =
      Matrix.diagonal fun i => (((torusEntries s t i)⁻¹ : Aˣ) : A) :=
  rfl

end Units

/-! ### Integer support of the root derivations -/

section Support

theorem map_rootDerFun' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (α : Root)
    (x : Fin 8 → A) :
    (fun i => f (rootDerFun α x i)) = rootDerFun α (fun i => f (x i)) := by
  cases α <;> funext i <;> fin_cases i <;>
    simp only [rootDerFun, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, map_sub, map_neg, map_zero]

theorem rootDer_int_support (α : Root) :
    ∀ p q : Fin 8, rootDerFun (A := ℤ) α (Pi.single q 1) p ≠ 0 →
      weightCoord p - weightCoord q = rootWeight α := by
  cases α <;> decide

/-- Every nonzero entry `(p, q)` of the root derivation `X_α` has weight `w(p) - w(q) = α`. -/
theorem rootDer_support {A : Type u} [CommRing A] (α : Root) (p q : Fin 8)
    (h : rootDer (A := A) α p q ≠ 0) : weightCoord p - weightCoord q = rootWeight α := by
  apply rootDer_int_support α p q
  intro h0
  apply h
  have hs : (Pi.single q (1 : A) : Fin 8 → A) =
      fun k => Int.castRingHom A ((Pi.single q (1 : ℤ) : Fin 8 → ℤ) k) := by
    funext k
    by_cases hk : k = q
    · subst hk
      simp
    · simp [hk]
  rw [rootDer_apply, hs, ← congrFun (map_rootDerFun' (Int.castRingHom A) α _) p, h0, map_zero]

theorem rootDerFun_unit {A : Type u} [CommRing A] (α : Root) :
    rootDerFun α (unit A) = 0 := by
  cases α <;> funext i <;> fin_cases i <;>
    simp [rootDerFun, unit]

theorem torusDerFun_unit {A : Type u} [CommRing A] (a b : A) :
    torusDerFun a b (unit A) = 0 := by
  funext i
  fin_cases i <;> simp [torusDerFun, unit]

theorem torusDer_zero {A : Type u} [CommRing A] : torusDer (0 : A) 0 = 0 := by
  rw [torusDer, ← Matrix.diagonal_zero]
  congr 1
  funext i
  fin_cases i <;> simp

/-- A derivation matrix whose pivot entries and first two diagonal entries vanish is zero. -/
theorem eq_zero_of_pivots {A : Type u} [CommRing A] {D : Matrix (Fin 8) (Fin 8) A}
    (hD : IsDerivation D.mulVec)
    (h10 : D 1 0 = 0) (h20 : D 2 0 = 0) (h30 : D 3 0 = 0) (h35 : D 3 5 = 0)
    (h16 : D 1 6 = 0) (h24 : D 2 4 = 0) (h12 : D 1 2 = 0) (h13 : D 1 3 = 0)
    (h21 : D 2 1 = 0) (h23 : D 2 3 = 0) (h31 : D 3 1 = 0) (h32 : D 3 2 = 0)
    (h11 : D 1 1 = 0) (h22 : D 2 2 = 0) : D = 0 := by
  have h := eq_derivCombination hD
  rw [derivCombination, h10, h20, h30, h35, h16, h24, h12, h13, h21, h23, h31, h32, h11, h22,
    torusDer_zero] at h
  simpa only [zero_smul, add_zero] using h

end Support

variable {K : Type u} [Field K]

attribute [local instance] isAffineHom_generalLinear

set_option hygiene false in
local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))

/-! ### The torus as a closed split torus -/

instance isAffineHom_torusSource : IsAffineHom (𝕋).X.hom :=
  isAffineHom_splitTorus _ _

variable (K) in
theorem isSplitTorus_torus : IsSplitTorus (𝕋).toGrp :=
  isSplitTorus_splitTorus _

variable (K) in
theorem isClosedSubgroup_torusMap : IsClosedSubgroup (torusMap K) :=
  IsTorus.isClosedSubgroup_of_mono (IsSplitTorus.isTorus (isSplitTorus_torus K)) _

/-! ### Weight spaces -/

/-- The value of a character on an affine point of the torus, in coordinates. -/
theorem characterValue_eq_prod (χ : characterLattice 𝕋) {A : Type u} [CommRing A] [Algebra K A]
    (t : Lie.AffinePoints (𝕋).toGrp A) :
    Lie.characterValue χ t =
      ∏ c : ULift.{u} (Fin 2), GeneralLinear.torusCoords t c ^
        GeneralLinear.characterCoordEquiv (Fin 2) K χ c.down := by
  have h := GeneralLinear.characterValue_characterLatticeEquiv_symm
    (splitTorus.characterLatticeEquiv K (ULift.{u} (Fin 2)) χ) t
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- Membership in a weight space of the torus, entrywise in the matrix coordinates. -/
theorem mem_weightSpace_torusMap_iff
    (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K))
    (χ : characterLattice 𝕋) :
    X ∈ weightSpace (torusMap K) χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra K A] (t : Lie.AffinePoints (𝕋).toGrp A)
        (p q : Fin 8),
        (torusEntries (GeneralLinear.torusCoords t ⟨0⟩) (GeneralLinear.torusCoords t ⟨1⟩) p : A) *
            algebraMap K A (lieMatrix X p q) *
            (((torusEntries (GeneralLinear.torusCoords t ⟨0⟩)
              (GeneralLinear.torusCoords t ⟨1⟩) q)⁻¹ : Aˣ) : A) =
          (Lie.characterValue χ t : A) * algebraMap K A (lieMatrix X p q) := by
  rw [← lieKernelHomLinear_mem_weightSpace_iff (CayleyDatum.split K).automorphismInclusion,
    ← pointKernelLinearEquiv_lieMatrix, mem_weightSpace]
  refine forall_congr' fun A => ?_
  refine ⟨fun h _ _ t a b => ?_, fun h _ _ t => ?_⟩
  · have h1 := h t
    rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      EmbeddingLike.apply_eq_iff_eq, affinePointsEquiv_torusMap] at h1
    have h2 := congrFun (congrFun h1 a) b
    simpa only [torusGL_val, torusGL_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Algebra.ofId_apply] using h2
  · rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      affinePointsEquiv_torusMap]
    congr 1
    ext a b
    simpa only [torusGL_val, torusGL_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Algebra.ofId_apply] using h t a b

/-- **Weights of the torus.** An element of the Lie algebra of the automorphism group lies in
the weight space of `χ` exactly when every nonzero entry of its matrix at `(p, q)` has weight
`χ = w(p) - w(q)`. -/
theorem mem_weightSpace_torusMap_iff_support
    (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K))
    (χ : characterLattice 𝕋) :
    X ∈ weightSpace (torusMap K) χ ↔
      ∀ p q : Fin 8, lieMatrix X p q ≠ 0 →
        GeneralLinear.characterCoordEquiv (Fin 2) K χ = weightCoord p - weightCoord q := by
  rw [mem_weightSpace_torusMap_iff]
  constructor
  · intro hX x y hxy
    funext c
    have h1 := hX K[T;T⁻¹] (GeneralLinear.affineTorusPoint (R := CommRingCat.of K)
      (Pi.mulSingle ⟨c⟩ (Gm.relativeCoordUnit K))) x y
    rw [characterValue_eq_prod, GeneralLinear.torusCoords_affineTorusPoint,
      GeneralLinear.prod_mulSingle_zpow, torusEntries_mulSingle, torusEntries_mulSingle,
      ← _root_.zpow_neg, Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val,
      Gm.relativeCoordUnit_zpow_val, ← LaurentPolynomial.C_eq_algebraMap] at h1
    refine (GeneralLinear.exponent_eq_of_C_mul_T hxy ?_).symm
    have h1' : LaurentPolynomial.T (weightCoord x c) * LaurentPolynomial.C (lieMatrix X x y) *
        LaurentPolynomial.T (-weightCoord y c) =
        LaurentPolynomial.T (GeneralLinear.characterCoordEquiv (Fin 2) K χ c) *
          LaurentPolynomial.C (lieMatrix X x y) := h1
    rw [Pi.sub_apply, sub_eq_add_neg, LaurentPolynomial.T_add]
    linear_combination -h1'
  · intro hsupp A _ _ t x y
    by_cases hxy : lieMatrix X x y = 0
    · rw [hxy, map_zero, mul_zero, zero_mul, mul_zero]
    · have hχ := characterValue_eq_prod χ t
      rw [hsupp x y hxy, prod_zpow_weightCoord_sub] at hχ
      rw [hχ, Units.val_mul]
      ring

/-! ### The zero weight space and maximality -/

theorem mem_weightSpace_zero_iff
    (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K)) :
    X ∈ weightSpace (torusMap K) 0 ↔
      ∀ p q : Fin 8, lieMatrix X p q ≠ 0 → weightCoord p = weightCoord q := by
  rw [mem_weightSpace_torusMap_iff_support, map_zero]
  refine forall_congr' fun p => forall_congr' fun q => forall_congr' fun _ => ?_
  rw [eq_comm, sub_eq_zero]

/-- An element of the zero weight space is a diagonal torus derivation. -/
theorem lieMatrix_eq_torusDer_of_mem_zero
    {X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K)}
    (hX : X ∈ weightSpace (torusMap K) 0) :
    lieMatrix X = torusDer (lieMatrix X 1 1) (lieMatrix X 2 2) := by
  have hz := (mem_weightSpace_zero_iff X).mp hX
  have hD := (lieMatrix_mulVec_unit_and_isDerivation X).2
  have hp : ∀ p q : Fin 8, weightCoord p ≠ weightCoord q → lieMatrix X p q = 0 :=
    fun p q hpq => by
      by_contra h
      exact hpq (hz p q h)
  have h := eq_derivCombination hD
  rw [derivCombination, hp 1 0 (by decide), hp 2 0 (by decide), hp 3 0 (by decide),
    hp 3 5 (by decide), hp 1 6 (by decide), hp 2 4 (by decide), hp 1 2 (by decide),
    hp 1 3 (by decide), hp 2 1 (by decide), hp 2 3 (by decide), hp 3 1 (by decide),
    hp 3 2 (by decide)] at h
  simpa only [zero_smul, zero_add] using h

/-- The two diagonal coordinates `1, 2` read off on the zero weight space. -/
def zeroIdx : Fin 2 → Fin 8 := ![1, 2]

variable (K) in
/-- The entries `X₁₁, X₂₂` of an element of the zero weight space. -/
def zeroWeightCoord : weightSpace (torusMap K) 0 →ₗ[K] (Fin 2 → K) where
  toFun X c := lieMatrix (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K))
    (zeroIdx c) (zeroIdx c)
  map_add' X Y := by
    funext c
    simp only [Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext a
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      RingHom.id_apply]

theorem zeroWeightCoord_apply (X : weightSpace (torusMap K) 0) (c : Fin 2) :
    zeroWeightCoord K X c =
      lieMatrix (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K))
        (zeroIdx c) (zeroIdx c) :=
  rfl

theorem zeroWeightCoord_bijective : Function.Bijective (zeroWeightCoord K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    apply lieMatrix_injective (K := K) (A := K)
    have h1 : lieMatrix (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K))
        1 1 = 0 := congrFun hX 0
    have h2 : lieMatrix (X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K))
        2 2 = 0 := congrFun hX 1
    rw [lieMatrix_eq_torusDer_of_mem_zero X.2, Submodule.coe_zero, map_zero, h1, h2,
      torusDer_zero]
  · intro d
    obtain ⟨X, hX⟩ := exists_lieMatrix_eq (K := K) (torusDer (d 0) (d 1))
      (by rw [torusDer_mulVec, torusDerFun_unit])
      (by
        have h := isDerivation_torusDerFun (d 0) (d 1)
        intro x y
        simp only [torusDer_mulVec]
        exact h x y)
    have hmem : X ∈ weightSpace (torusMap K) 0 := by
      rw [mem_weightSpace_zero_iff, hX]
      intro p q hpq
      rw [torusDer_apply] at hpq
      by_cases h : p = q
      · rw [h]
      · exact absurd (ite_eq_right_of_eq_false _ _ (eq_false h)) hpq
    refine ⟨⟨X, hmem⟩, ?_⟩
    funext c
    rw [zeroWeightCoord_apply]
    change lieMatrix X (zeroIdx c) (zeroIdx c) = d c
    rw [hX, torusDer_apply, ite_eq_left_of_eq_true _ _ (eq_self _)]
    fin_cases c <;> rfl

/-- The zero weight space of the torus has dimension two. -/
theorem finrank_weightSpace_zero :
    Module.finrank K (weightSpace (torusMap K) 0) = 2 := by
  rw [(LinearEquiv.ofBijective (zeroWeightCoord K) zeroWeightCoord_bijective).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

variable (K) in
/-- **Maximality.** If the automorphism group scheme is connected, the rank-two torus is a
maximal torus. -/
theorem isMaximalTorus_torusMap
    [ConnectedSpace (CayleyDatum.split K).automorphismGroup.X.left] :
    IsMaximalTorus (torusMap K) := by
  have : Smooth (CayleyDatum.split K).automorphismGroup.X.hom := smooth_automorphismGroup
  refine isMaximalTorus_of_finrank_zeroWeight _ (isSplitTorus_torus K)
    (isClosedSubgroup_torusMap K) ?_
  rw [finrank_weightSpace_zero]
  have h := splitTorus.finrank_lieKernel (ULift.{u} (Fin 2)) K
  rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h.symm

/-! ### Roots -/

variable (K) in
/-- The character of the torus with coordinates `rootWeight α`. -/
def rootChar (α : Root) : characterLattice 𝕋 :=
  (GeneralLinear.characterCoordEquiv (Fin 2) K).symm (rootWeight α)

theorem characterCoordEquiv_rootChar (α : Root) :
    GeneralLinear.characterCoordEquiv (Fin 2) K (rootChar K α) = rootWeight α :=
  LinearEquiv.apply_symm_apply _ _

theorem rootChar_injective : Function.Injective (rootChar K) := by
  intro α β h
  have h' := congrArg (GeneralLinear.characterCoordEquiv (Fin 2) K) h
  rw [characterCoordEquiv_rootChar, characterCoordEquiv_rootChar] at h'
  cases α <;> cases β <;> first | rfl | (exfalso; revert h'; decide)

/-- The root-vector Lie element of the root `α`. -/
theorem exists_lieMatrix_eq_rootDer (α : Root) :
    ∃ X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K),
      lieMatrix X = rootDer α :=
  exists_lieMatrix_eq (K := K) (rootDer α) (by rw [rootDer_mulVec, rootDerFun_unit])
    (by
      have h := isDerivation_rootDerFun (A := K) α
      intro x y
      simp only [rootDer_mulVec]
      exact h x y)

theorem mem_weightSpace_rootChar_of_lieMatrix_eq (α : Root)
    {X : Additive (lieKernel (CayleyDatum.split K).automorphismGroup K)}
    (hX : lieMatrix X = rootDer α) : X ∈ weightSpace (torusMap K) (rootChar K α) := by
  rw [mem_weightSpace_torusMap_iff_support, characterCoordEquiv_rootChar, hX]
  intro p q hpq
  exact (rootDer_support α p q hpq).symm

/-- The pivot entry of the root derivation `X_α`. -/
def pivot : Root → Fin 8 × Fin 8
  | .u1 => (1, 0)
  | .u2 => (2, 0)
  | .u3 => (3, 0)
  | .v1 => (3, 5)
  | .v2 => (1, 6)
  | .v3 => (2, 4)
  | .l12 => (1, 2)
  | .l13 => (1, 3)
  | .l21 => (2, 1)
  | .l23 => (2, 3)
  | .l31 => (3, 1)
  | .l32 => (3, 2)

theorem rootDer_pivot {A : Type u} [CommRing A] (α : Root) :
    rootDer (A := A) α (pivot α).1 (pivot α).2 = 1 := by
  rw [rootDer_apply]
  cases α <;> simp [rootDerFun, pivot]

theorem rootDer_ne_zero {A : Type u} [CommRing A] [Nontrivial A] (α : Root) :
    rootDer (A := A) α ≠ 0 := by
  intro h
  have h1 := rootDer_pivot (A := A) α
  rw [h, Matrix.zero_apply] at h1
  exact zero_ne_one h1

theorem rootChar_mem_roots (α : Root) : rootChar K α ∈ roots (torusMap K) := by
  refine ⟨fun h => rootWeight_ne_zero α ?_, fun h => ?_⟩
  · rw [← characterCoordEquiv_rootChar (K := K), h, map_zero]
  · obtain ⟨X, hX⟩ := exists_lieMatrix_eq_rootDer (K := K) α
    have hmem := mem_weightSpace_rootChar_of_lieMatrix_eq α hX
    rw [h, Submodule.mem_bot] at hmem
    apply rootDer_ne_zero (A := K) α
    rw [← hX, hmem, map_zero]

theorem mem_range_rootChar_of_entry {χ : characterLattice 𝕋} (α : Root) {p q : Fin 8}
    (hpq : weightCoord p - weightCoord q = rootWeight α)
    (hχ : GeneralLinear.characterCoordEquiv (Fin 2) K χ = weightCoord p - weightCoord q) :
    χ ∈ Set.range (rootChar K) :=
  ⟨α, by rw [rootChar, ← hpq, ← hχ, LinearEquiv.symm_apply_apply]⟩

/-- **The roots of the torus.** The roots of the rank-two torus in the automorphism group are
exactly the twelve characters `rootChar α`. -/
theorem roots_torusMap : roots (torusMap K) = Set.range (rootChar K) := by
  apply Set.Subset.antisymm
  · intro χ hχ
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
    have hs := (mem_weightSpace_torusMap_iff_support X χ).mp hX
    have hD := (lieMatrix_mulVec_unit_and_isDerivation X).2
    by_contra hne
    apply hX0
    apply lieMatrix_injective (K := K) (A := K)
    rw [map_zero]
    have hdiag : ∀ p : Fin 8, lieMatrix X p p = 0 := fun p => by
      by_contra h
      apply hχ.1
      apply (GeneralLinear.characterCoordEquiv (Fin 2) K).injective
      rw [hs p p h, sub_self, map_zero]
    have hpiv : ∀ α : Root, lieMatrix X (pivot α).1 (pivot α).2 = 0 := fun α => by
      by_contra h
      exact hne (mem_range_rootChar_of_entry α (by cases α <;> decide) (hs _ _ h))
    exact eq_zero_of_pivots hD (hpiv .u1) (hpiv .u2) (hpiv .u3) (hpiv .v1) (hpiv .v2)
      (hpiv .v3) (hpiv .l12) (hpiv .l13) (hpiv .l21) (hpiv .l23) (hpiv .l31) (hpiv .l32)
      (hdiag 1) (hdiag 2)
  · rintro _ ⟨α, rfl⟩
    exact rootChar_mem_roots α

end SplitCayley

end Langlands.GroupScheme
