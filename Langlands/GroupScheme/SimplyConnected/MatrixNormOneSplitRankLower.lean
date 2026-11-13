import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankStatement
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.Lattice

/-!
# The diagonal split torus of `SL_m(D)`

For a finite-dimensional central division algebra `D` over a field `K`, this module
constructs a closed split torus of dimension `m - 1` in the actual reduced-norm-one
group of `M_m(D)`, namely `t ↦ diag((t₁ ⋯ t_{m-1})⁻¹, t₁, …, t_{m-1})`, and deduces the
lower bound `m - 1 ≤ splitRank`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits

namespace MatrixDiagonalTorus

open FiniteAlgebraUnits.MatrixPoints

/-! ### Diagonal elements of a coefficient extension of a matrix algebra -/

section Diagonal

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  {J : Type} [Fintype J] [DecidableEq J]
  (R : Type u) [CommRing R] [Algebra K R]

/-- The diagonal embedding `R^J → R ⊗ M_J(D)`, sending `x` to the diagonal matrix with
entries `x i ⊗ 1`. -/
def diagRingHom : (J → R) →+* R ⊗[K] Matrix J J D :=
  (coefficientEquiv K D R (m := J)).symm.toRingEquiv.toRingHom.comp
    ((Matrix.diagonalRingHom J (R ⊗[K] D)).comp
      ((Algebra.TensorProduct.includeLeftRingHom (R := K) (A := R) (B := D)).compLeft J))

theorem coefficientEquiv_diagRingHom (x : J → R) :
    coefficientEquiv K D R (diagRingHom K D R x) =
      Matrix.diagonal fun i => x i ⊗ₜ[K] (1 : D) := by
  simp [diagRingHom]

variable {R} in
/-- The diagonal embedding commutes with every coefficient-algebra homomorphism. -/
theorem diagRingHom_map {S : Type u} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x : J → R) :
    Algebra.TensorProduct.map f (AlgHom.id K (Matrix J J D)) (diagRingHom K D R x) =
      diagRingHom K D S (fun i => f (x i)) := by
  apply (coefficientEquiv K D S (m := J)).injective
  rw [coefficientEquiv_naturality, coefficientEquiv_diagRingHom,
    coefficientEquiv_diagRingHom, Matrix.diagonal_map (map_zero _)]
  simp

/-- The diagonal embedding is injective. -/
theorem diagRingHom_injective : Function.Injective (diagRingHom K D R (J := J)) := by
  intro x y h
  have h1 := congrArg (coefficientEquiv K D R (m := J)) h
  rw [coefficientEquiv_diagRingHom, coefficientEquiv_diagRingHom] at h1
  funext i
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.diagonal_apply_eq] at h2
  exact Algebra.TensorProduct.includeLeft_injective (R := K) (S := K)
    (algebraMap K D).injective h2

/-- The unit of `R ⊗ M_J(D)` given by a family of diagonal units. -/
def diagUnit (x : J → Rˣ) : (R ⊗[K] Matrix J J D)ˣ where
  val := diagRingHom K D R fun k => (x k : R)
  inv := diagRingHom K D R fun k => ((x k)⁻¹ : Rˣ)
  val_inv := by
    rw [← map_mul, ← map_one (diagRingHom K D R (J := J))]
    congr 1
    funext k
    simp
  inv_val := by
    rw [← map_mul, ← map_one (diagRingHom K D R (J := J))]
    congr 1
    funext k
    simp

@[simp] theorem diagUnit_val (x : J → Rˣ) :
    (diagUnit K D R x : R ⊗[K] Matrix J J D) = diagRingHom K D R fun k => (x k : R) := rfl

end Diagonal

/-! ### Reduced norms of diagonal elements -/

section ReducedNorm

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
  (R : Type u) [CommRing R] [Algebra K R]

local notation "Nrd" => Langlands.CentralSimple.reducedNorm K (Matrix J J D) R

/-- The reduced norm is invariant under conjugation by a pair of mutually inverse elements. -/
theorem reducedNorm_conj (X Y Z : R ⊗[K] Matrix J J D) (h : Y * Z = 1) :
    Nrd (Y * X * Z) = Nrd X := by
  have h1 := congrArg Nrd h
  rw [map_mul, map_one] at h1
  rw [map_mul, map_mul]
  calc Nrd Y * Nrd X * Nrd Z = Nrd X * (Nrd Y * Nrd Z) := by ring
    _ = Nrd X := by rw [h1, mul_one]

/-- The reduced norm of a diagonal element is invariant under permuting the entries. -/
theorem reducedNorm_diagRingHom_perm (σ : Equiv.Perm J) (x : J → R) :
    Nrd (diagRingHom K D R (x ∘ σ)) = Nrd (diagRingHom K D R x) := by
  let c := coefficientEquiv K D R (m := J)
  let P : Matrix J J (R ⊗[K] D) := σ.toPEquiv.toMatrix
  let Q : Matrix J J (R ⊗[K] D) := σ.symm.toPEquiv.toMatrix
  have hPQ : P * Q = 1 := by
    simp only [P, Q]
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hconj : P * c (diagRingHom K D R x) * Q = c (diagRingHom K D R (x ∘ σ)) := by
    simp only [P, Q, c, coefficientEquiv_diagRingHom]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      Matrix.submatrix_submatrix, Equiv.symm_symm]
    exact Matrix.submatrix_diagonal_equiv _ σ
  have hconj' : c.symm P * diagRingHom K D R x * c.symm Q = diagRingHom K D R (x ∘ σ) := by
    apply c.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hconj]
  have hPQ' : c.symm P * c.symm Q = 1 := by
    rw [← map_mul, hPQ, map_one]
  rw [← hconj']
  exact reducedNorm_conj K D R _ _ _ hPQ'

/-- The reduced norm of diagonal elements, as a monoid homomorphism on `R^J`. -/
def diagNorm : (J → R) →* R :=
  (Langlands.CentralSimple.reducedNorm K (Matrix J J D) R).toMonoidHom.comp
    (diagRingHom K D R).toMonoidHom

theorem diagNorm_apply (x : J → R) : diagNorm K D R x = Nrd (diagRingHom K D R x) := rfl

theorem diagNorm_mulSingle (i j : J) (r : R) :
    diagNorm K D R (Pi.mulSingle i r) = diagNorm K D R (Pi.mulSingle j r) := by
  have h : (Pi.mulSingle i r : J → R) ∘ (Equiv.swap i j) = Pi.mulSingle j r := by
    funext k
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left]
  rw [diagNorm_apply, diagNorm_apply, ← h, reducedNorm_diagRingHom_perm]

/-- The reduced norm of a diagonal element depends only on the product of its entries. -/
theorem diagNorm_eq_mulSingle_prod (i₀ : J) (x : J → R) :
    diagNorm K D R x = diagNorm K D R (Pi.mulSingle i₀ (∏ k, x k)) := by
  have hx : (Pi.mulSingle i₀ (∏ k, x k) : J → R) = ∏ k, (Pi.mulSingle i₀ (x k) : J → R) :=
    map_prod (MonoidHom.mulSingle (fun _ : J => R) i₀) x Finset.univ
  conv_lhs => rw [← Finset.univ_prod_mulSingle x]
  rw [hx, map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => diagNorm_mulSingle K D R k i₀ (x k)

/-- A diagonal element whose entries have product one has reduced norm one. -/
theorem reducedNorm_diagRingHom_eq_one (x : J → R) (hx : ∏ k, x k = 1) :
    Nrd (diagRingHom K D R x) = 1 := by
  rw [← diagNorm_apply, diagNorm_eq_mulSingle_prod K D R (Classical.arbitrary J), hx,
    Pi.mulSingle_one, map_one]

end ReducedNorm

/-! ### The diagonal torus on coefficient points -/

section Units

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] (n : ℕ)
  (R : Type u) [CommRing R] [Algebra K R]

/-- The diagonal entries `((t₁ ⋯ tₙ)⁻¹, t₁, …, tₙ)`. -/
def cocharVector (t : ULift.{u} (Fin n) → Rˣ) : Fin (n + 1) → Rˣ :=
  Fin.cons (∏ j : Fin n, t ⟨j⟩)⁻¹ fun j => t ⟨j⟩

variable {n R}

@[simp] theorem cocharVector_zero (t : ULift.{u} (Fin n) → Rˣ) :
    cocharVector n R t 0 = (∏ j : Fin n, t ⟨j⟩)⁻¹ := rfl

@[simp] theorem cocharVector_succ (t : ULift.{u} (Fin n) → Rˣ) (j : Fin n) :
    cocharVector n R t j.succ = t ⟨j⟩ := rfl

theorem prod_cocharVector (t : ULift.{u} (Fin n) → Rˣ) : ∏ k, cocharVector n R t k = 1 := by
  rw [Fin.prod_univ_succ, cocharVector_zero]
  simp only [cocharVector_succ, inv_mul_cancel]

theorem cocharVector_map {S : Type u} [CommRing S] (φ : Rˣ →* Sˣ)
    (t : ULift.{u} (Fin n) → Rˣ) (k : Fin (n + 1)) :
    φ (cocharVector n R t k) = cocharVector n S (fun j => φ (t j)) k := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [map_prod]
  · simp

variable (n R)

/-- The diagonal unit homomorphism `(Rˣ)ⁿ → (R ⊗ M_{n+1}(D))ˣ`. -/
def diagUnits : (ULift.{u} (Fin n) → Rˣ) →* (R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ where
  toFun t := diagUnit K D R (cocharVector n R t)
  map_one' := by
    apply Units.ext
    change diagRingHom K D R (fun k => ((cocharVector n R 1 k : Rˣ) : R)) = 1
    rw [← map_one (diagRingHom K D R (J := Fin (n + 1)))]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k <;> simp
  map_mul' t s := by
    apply Units.ext
    change diagRingHom K D R (fun k => ((cocharVector n R (t * s) k : Rˣ) : R)) =
      diagRingHom K D R (fun k => ((cocharVector n R t k : Rˣ) : R)) *
        diagRingHom K D R (fun k => ((cocharVector n R s k : Rˣ) : R))
    rw [← map_mul]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [Finset.prod_mul_distrib, mul_comm]
    · simp

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem diagUnits_val (t : ULift.{u} (Fin n) → Rˣ) :
    (diagUnits K D n R t : R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D) =
      diagRingHom K D R (fun k => ((cocharVector n R t k : Rˣ) : R)) := rfl

theorem diagUnits_mem (t : ULift.{u} (Fin n) → Rˣ) :
    diagUnits K D n R t ∈
      Langlands.CentralSimple.reducedNormOne K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) R := by
  rw [Langlands.CentralSimple.mem_reducedNormOne, diagUnits_val]
  apply reducedNorm_diagRingHom_eq_one
  rw [← Units.coe_prod, prod_cocharVector, Units.val_one]

/-- The diagonal torus on coefficient points, landing in reduced norm one. -/
def torusUnits : (ULift.{u} (Fin n) → Rˣ) →*
    Langlands.CentralSimple.reducedNormOne K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) R :=
  (diagUnits K D n R).codRestrict _ (diagUnits_mem K D n R)

theorem torusUnits_val (t : ULift.{u} (Fin n) → Rˣ) :
    ((torusUnits K D n R t : (R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ) :
        R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D) =
      diagRingHom K D R (fun k => ((cocharVector n R t k : Rˣ) : R)) := rfl

theorem torusUnits_injective : Function.Injective (torusUnits K D n R) := by
  intro t s h
  have h1 := congrArg (fun x : Langlands.CentralSimple.reducedNormOne K
      (Matrix (Fin (n + 1)) (Fin (n + 1)) D) R =>
    ((x : (R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ) :
      R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)) h
  simp only [torusUnits_val] at h1
  have h2 := diagRingHom_injective K D R h1
  funext j
  apply Units.ext
  have h3 := congrFun h2 j.down.succ
  simpa only [cocharVector_succ] using h3

variable {R} in
/-- The diagonal torus commutes with every coefficient-algebra homomorphism. -/
theorem torusUnits_map {S : Type u} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (t : ULift.{u} (Fin n) → Rˣ) :
    Units.map (Algebra.TensorProduct.map f
        (AlgHom.id K (Matrix (Fin (n + 1)) (Fin (n + 1)) D))).toMonoidHom
        (torusUnits K D n R t : (R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ) =
      (torusUnits K D n S (fun j => Units.map f.toMonoidHom (t j)) :
        (S ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ) := by
  apply Units.ext
  change Algebra.TensorProduct.map f (AlgHom.id K (Matrix (Fin (n + 1)) (Fin (n + 1)) D))
      ((torusUnits K D n R t : (R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ) :
        R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) D) = _
  rw [torusUnits_val, torusUnits_val, diagRingHom_map]
  congr 1
  funext k
  rw [← cocharVector_map (Units.map f.toMonoidHom) t k]
  rfl

end Units

/-! ### The actual diagonal torus -/

section Scheme

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] (n : ℕ)

local notation "𝕊" => splitTorus (Spec (CommRingCat.of K)) (ULift (Fin n))
local notation "𝔾" => normOne K (Matrix (Fin (n + 1)) (Fin (n + 1)) D)

/-- The diagonal torus on actual points. -/
def torusPoints (T : Over (Spec (CommRingCat.of K))) : (T ⟶ (𝕊).X) →* (T ⟶ (𝔾).X) :=
  (normOnePointsEquiv K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) T).symm.toMonoidHom.comp
    ((torusUnits K D n ((algΓ (CommRingCat.of K)).obj T).unop).comp
      (splitTorus.pointsEquiv (ULift.{u} (Fin n)) T).toMonoidHom)

theorem normOnePointsEquiv_torusPoints (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕊).X) :
    normOnePointsEquiv K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) T (torusPoints K D n T x) =
      torusUnits K D n ((algΓ (CommRingCat.of K)).obj T).unop
        (splitTorus.pointsEquiv (ULift.{u} (Fin n)) T x) :=
  (normOnePointsEquiv K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) T).apply_symm_apply _

theorem torusPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (𝕊).X) :
    torusPoints K D n T' (a ≫ x) = a ≫ torusPoints K D n T x := by
  apply (normOnePointsEquiv K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) T').injective
  rw [normOnePointsEquiv_naturality, normOnePointsEquiv_torusPoints,
    normOnePointsEquiv_torusPoints, splitTorus.pointsEquiv_naturality]
  apply Subtype.ext
  exact (torusUnits_map K D n (((algΓ (CommRingCat.of K)).map a).unop.hom) _).symm

/-- The actual diagonal split torus `diag((t₁ ⋯ tₙ)⁻¹, t₁, …, tₙ)` of `SL_{n+1}(D)`. -/
def torusHom : 𝕊 ⟶ 𝔾 :=
  homOfPoints (torusPoints K D n) (torusPoints_naturality K D n)

instance mono_torusHom : Mono (torusHom K D n).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} (Fin n)) Z).injective
  have h1 := congrArg (normOnePointsEquiv K (Matrix (Fin (n + 1)) (Fin (n + 1)) D) Z) hgh
  rw [torusHom, comp_homOfPoints, comp_homOfPoints, normOnePointsEquiv_torusPoints,
    normOnePointsEquiv_torusPoints] at h1
  exact torusUnits_injective K D n ((algΓ (CommRingCat.of K)).obj Z).unop h1

/-- The diagonal torus is a closed subgroup of the actual reduced-norm-one group. -/
theorem isClosedSubgroup_torusHom : IsClosedSubgroup (torusHom K D n) := by
  have := isAffineHom_splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin n))
  exact IsTorus.isClosedSubgroup_of_mono
    (IsSplitTorus.isTorus (isSplitTorus_splitTorus _)) _

end Scheme

end MatrixDiagonalTorus

/-- **Lower bound.** The actual reduced-norm-one group of `M_m(D)` contains a closed split
torus of dimension `m - 1`. -/
theorem sub_one_le_splitRank_normOne (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D] (m : ℕ) [NeZero m] :
    ((m - 1 : ℕ) : ℕ∞) ≤ splitRank (normOne K (Matrix (Fin m) (Fin m) D)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne m)).symm⟩
  have h := card_le_splitRank (ULift.{u} (Fin n)) (MatrixDiagonalTorus.torusHom K D n)
    (MatrixDiagonalTorus.isClosedSubgroup_torusHom K D n)
  simpa using h

end Langlands.GroupScheme.CentralSimpleUnits
