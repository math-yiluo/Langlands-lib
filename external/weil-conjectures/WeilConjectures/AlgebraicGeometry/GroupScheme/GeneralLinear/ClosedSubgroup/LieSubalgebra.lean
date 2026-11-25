/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.IdentityComponent
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.Stabilizer

/-!
# The Lie algebra of a closed subgroup of `GL_n`, in matrices

For a Hopf ideal `I` of the coordinate ring of `GL_n` over a field `k`, the *matrix Lie algebra*
of the closed subgroup `G = V(I)` is

$$
\mathfrak g = \{X \in \mathfrak{gl}_n \mid 1 + \varepsilon X \in G(k[\varepsilon])\},
$$

a Lie subalgebra of `gl_n` (`AlgebraicGeometry.GeneralLinearGroup.lieSubalgebra`): the bracket is
the mixed term of the commutator `(1 + εX)(1 + δY)(1 - εX)(1 - δY) = 1 + εδ⁅X, Y⁆` over the
iterated dual numbers `k[ε][δ]`. It is the tangent space of `G` at the identity, in matrix form,
and its dimension is the dimension of `G` in characteristic zero (Cartier).

The main result is the *group–Lie comparison for linear conditions*: let `E` be a family of
equations on `GL_n` whose solutions in `G(R)` form a subgroup for every `k`-algebra `R` (for
instance the linear equations of the stabilizer of a subspace, or of the centralizer of a set of
matrices). If `G` is connected, `k` algebraically closed of characteristic zero, then every point
of `G(k)` satisfies `E` if and only if every tangent vector `1 + εX`, `X ∈ 𝔤`, does
(`AlgebraicGeometry.GeneralLinearGroup.forall_mem_zeroLocus_iff_forall_mem_lieSubalgebra`): the
closed subgroup cut out by `E` has the Lie algebra of `G`, hence the dimension of `G`, hence is
`G`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.lieSubalgebra`: the Lie algebra `𝔤 ⊆ gl_n` of `V(I)`.

## Main results

- `AlgebraicGeometry.GeneralLinearGroup.lie_mem_lieSubalgebra_of_commutator_mem`: if the
  commutators of `V(I)` lie in `V(J)`, then the brackets of `Lie V(I)` lie in `Lie V(J)`.
- `AlgebraicGeometry.GeneralLinearGroup.lieSubalgebra_identityComponent`: in characteristic zero,
  `Lie G° = Lie G`.
- `AlgebraicGeometry.GeneralLinearGroup.finrank_lieSubalgebra`: `dim Lie G = dim G` in
  characteristic zero.
- `AlgebraicGeometry.GeneralLinearGroup.eq_of_le_of_lieSubalgebra_eq`: a closed subgroup of a
  connected group with the same Lie algebra is the whole group.
- `AlgebraicGeometry.GeneralLinearGroup.forall_mem_zeroLocus_iff_forall_mem_lieSubalgebra`: the
  group–Lie comparison for linear conditions.
- `AlgebraicGeometry.GeneralLinearGroup.forall_mulVec_mem_iff_forall_lieSubalgebra`: a subspace
  of `kⁿ` is stable under a connected `G(k)` if and only if it is stable under `𝔤`.
- `AlgebraicGeometry.GeneralLinearGroup.forall_commute_iff_forall_lieSubalgebra`: a matrix
  commutes with a connected `G(k)` if and only if it commutes with `𝔤`.
- `AlgebraicGeometry.GeneralLinearGroup.mem_lieSubalgebra_center_iff`: the Lie algebra of the
  centre of a connected `G` is the centre of its Lie algebra.

## Blueprint

- `lemma-stable-subspaces-center--1`: group-invariant and Lie-invariant subspaces agree.
- `lemma-stable-subspaces-center--2`: the Lie algebra of the centre.
-/

@[expose] public section

universe u

open TrivSqZeroExt
open scoped Matrix commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

open Matrix.GeneralLinearGroup

section DualUnit

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

@[simp]
theorem dualUnit_zero : dualUnit (0 : Matrix n n R) = 1 := by
  ext1
  simp [coe_dualUnit]

/-- `(1 + εX)(1 + εY) = 1 + ε(X + Y)`. -/
theorem dualUnit_add (X Y : Matrix n n R) : dualUnit (X + Y) = dualUnit X * dualUnit Y := by
  have h : (X + Y).map (inr : R → DualNumber R) = X.map inr + Y.map inr := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply,
      inr_add]
  ext1
  rw [Units.val_mul, coe_dualUnit, coe_dualUnit, coe_dualUnit, h, add_mul, one_mul,
    mul_add, mul_one, Matrix.map_inr_mul_map_inr]
  abel

/-- Scaling `ε ↦ cε` sends `1 + εX` to `1 + ε(cX)`. -/
theorem map_scale_dualUnit (c : R) (X : Matrix n n R) :
    Matrix.GeneralLinearGroup.map (DualNumber.scale c).toRingHom (dualUnit X) =
      dualUnit (c • X) := by
  ext i j : 2
  rw [Matrix.GeneralLinearGroup.map_apply, coe_dualUnit, coe_dualUnit, Matrix.add_apply,
    Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, DualNumber.scale_inr]
  congr 1
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end DualUnit

/-! ### The commutator of two tangent vectors -/

section Commutator

/-- In a ring, if `u² = v² = 0` and `uvu = vuv = 0`, then the commutator of `1 + u` and `1 + v`
is `1 + (uv - vu)`. -/
theorem one_add_mul_one_add_mul_one_sub_mul_one_sub {A : Type*} [Ring A] {u v : A}
    (hu : u * u = 0) (hv : v * v = 0) (huvu : u * v * u = 0) (hvuv : v * u * v = 0) :
    (1 + u) * (1 + v) * (1 - u) * (1 - v) = 1 + (u * v - v * u) := by
  have hv' (x : A) : x * v * v = 0 := by rw [mul_assoc, hv, mul_zero]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, hu, hv, huvu, hvuv, hv',
    add_zero]
  noncomm_ring

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]

variable (k) in
/-- The `k`-algebra map `k[ε] → A`, `ε ↦ a`, for an element `a` of square zero. -/
noncomputable def dualNumberLift (a : A) (ha : a * a = 0) : DualNumber k →ₐ[k] A :=
  DualNumber.lift ⟨(Algebra.ofId k A, a), ha, fun _ ↦ Commute.all _ _⟩

theorem dualNumberLift_apply (a : A) (ha : a * a = 0) (x : DualNumber k) :
    dualNumberLift k a ha x = algebraMap k A x.fst + x.snd • a := by
  rw [dualNumberLift, DualNumber.lift_apply_apply, Algebra.smul_def]
  rfl

theorem dualNumberLift_injective {a : A} (ha : a * a = 0)
    (h : ∀ x y : k, algebraMap k A x + y • a = 0 → x = 0 ∧ y = 0) :
    Function.Injective (dualNumberLift k a ha) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  rw [dualNumberLift_apply] at hx
  obtain ⟨h1, h2⟩ := h _ _ hx
  exact TrivSqZeroExt.ext h1 h2

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem coe_map_dualNumberLift_dualUnit (a : A) (ha : a * a = 0) (X : Matrix n n k) :
    (Matrix.GeneralLinearGroup.map (dualNumberLift k a ha).toRingHom (dualUnit X) :
      Matrix n n A) = 1 + a • (algebraMap k A).mapMatrix X := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_dualUnit, Matrix.add_apply, Matrix.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualNumberLift_apply, fst_add, snd_add, fst_inr,
    snd_inr, Matrix.add_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    smul_eq_mul, Algebra.smul_def, mul_comm a]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.one_apply_ne hij]

/-- `(1 + εX)⁻¹ = 1 - εX`. -/
theorem dualUnit_neg (X : Matrix n n k) : dualUnit (-X) = (dualUnit X)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← dualUnit_add, add_neg_cancel, dualUnit_zero])

/-- The commutator of the tangent vectors `1 + aX` and `1 + bY`, for `a² = b² = 0`, is the tangent
vector `1 + ab⁅X, Y⁆` in the direction `ab`. -/
theorem commutatorElement_map_dualUnit {a b : A} (ha : a * a = 0) (hb : b * b = 0)
    (hab : a * b * (a * b) = 0) (X Y : Matrix n n k) :
    ⁅Matrix.GeneralLinearGroup.map (dualNumberLift k a ha).toRingHom (dualUnit X),
        Matrix.GeneralLinearGroup.map (dualNumberLift k b hb).toRingHom (dualUnit Y)⁆ =
      Matrix.GeneralLinearGroup.map (dualNumberLift k (a * b) hab).toRingHom
        (dualUnit ⁅X, Y⁆) := by
  set f := (algebraMap k A).mapMatrix (m := n)
  have hinv (c : A) (hc : c * c = 0) (Z : Matrix n n k) :
      (((Matrix.GeneralLinearGroup.map (dualNumberLift k c hc).toRingHom (dualUnit Z))⁻¹ :
        GL n A) : Matrix n n A) = 1 - c • f Z := by
    rw [← map_inv, ← dualUnit_neg, coe_map_dualNumberLift_dualUnit, map_neg, smul_neg,
      sub_eq_add_neg]
  have hzero (c d e : A) (hc : c * d * e = 0) (Z W V : Matrix n n A) :
      (c • Z) * (d • W) * (e • V) = 0 := by
    rw [show (c • Z) * (d • W) * (e • V) = (c * d * e) • (Z * W * V) by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring, hc, zero_smul]
  have hsq (c : A) (hc : c * c = 0) (Z W : Matrix n n A) : (c • Z) * (c • W) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, zero_smul]
  have huvu := hzero a b a (by rw [mul_comm a b, mul_assoc, ha, mul_zero]) (f X) (f Y) (f X)
  have hvuv := hzero b a b (by rw [mul_comm b a, mul_assoc, hb, mul_zero]) (f Y) (f X) (f Y)
  ext1
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul,
    coe_map_dualNumberLift_dualUnit, coe_map_dualNumberLift_dualUnit, hinv, hinv,
    one_add_mul_one_add_mul_one_sub_mul_one_sub (hsq a ha _ _) (hsq b hb _ _) huvu hvuv,
    coe_map_dualNumberLift_dualUnit, Ring.lie_def, map_sub, map_mul, map_mul, smul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm b a]
  rfl

/-- The two tangent directions `ε₁ = inl ε` and `ε₂ = ε` of `k[ε₁][ε₂] = (k[ε])[ε]`. -/
theorem dualNumber_eps_mul_eps_eq_zero :
    ((inl DualNumber.eps : DualNumber (DualNumber k)) * DualNumber.eps) *
      ((inl DualNumber.eps : DualNumber (DualNumber k)) * DualNumber.eps) = 0 := by
  rw [mul_mul_mul_comm, DualNumber.eps_mul_eps, mul_zero]

theorem dualNumberLift_mixed_injective :
    Function.Injective (dualNumberLift k
      ((inl DualNumber.eps : DualNumber (DualNumber k)) * DualNumber.eps)
      dualNumber_eps_mul_eps_eq_zero) := by
  refine dualNumberLift_injective _ fun x y h ↦ ?_
  have h1 := congrArg (fun w : DualNumber (DualNumber k) ↦ w.fst.fst) h
  have h2 := congrArg (fun w : DualNumber (DualNumber k) ↦ w.snd.snd) h
  have hm : (inl DualNumber.eps : DualNumber (DualNumber k)) * DualNumber.eps =
      inr DualNumber.eps := by
    simp only [DualNumber.eps, inl_mul_inr, smul_eq_mul, mul_one]
  simp only [hm, fst_add, snd_add, fst_smul, snd_smul, fst_inr, snd_inr, smul_zero, add_zero,
    Algebra.algebraMap_eq_smul_one, fst_one, snd_one, DualNumber.snd_eps,
    smul_eq_mul, mul_one, fst_zero, snd_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

end Commutator

/-! ### The Lie algebra -/

section LieSubalgebra

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]

/-- If the commutators of `V(I)` with values in `k[ε₁][ε₂]` lie in `V(J)`, then the bracket of two
tangent vectors of `V(I)` is a tangent vector of `V(J)`. -/
theorem dualUnit_lie_mem_zeroLocus {I J : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]
    [J.IsHopfIdeal k]
    (h : ∀ g ∈ zeroLocus I (DualNumber (DualNumber k)),
      ∀ g' ∈ zeroLocus I (DualNumber (DualNumber k)), ⁅g, g'⁆ ∈ zeroLocus J _)
    {X Y : Matrix n n k} (hX : dualUnit X ∈ zeroLocus I (DualNumber k))
    (hY : dualUnit Y ∈ zeroLocus I (DualNumber k)) :
    dualUnit ⁅X, Y⁆ ∈ zeroLocus J (DualNumber k) := by
  have hε : (DualNumber.eps : DualNumber (DualNumber k)) * DualNumber.eps = 0 :=
    DualNumber.eps_mul_eps
  have hε₁ : (inl DualNumber.eps : DualNumber (DualNumber k)) * inl DualNumber.eps = 0 := by
    rw [← inl_mul, DualNumber.eps_mul_eps, inl_zero]
  have := h _ (map_mem_zeroLocus (dualNumberLift k _ hε₁) hX) _
    (map_mem_zeroLocus (dualNumberLift k _ hε) hY)
  rw [commutatorElement_map_dualUnit hε₁ hε dualNumber_eps_mul_eps_eq_zero] at this
  exact (map_mem_zeroLocus_iff dualNumberLift_mixed_injective).1 this

variable (I : Ideal (CoordinateRing n k)) [I.IsHopfIdeal k]

/-- The Lie algebra `𝔤 ⊆ gl_n` of the closed subgroup `G = V(I)` of `GL_n`: the matrices `X` with
`1 + εX ∈ G(k[ε])`, the tangent space of `G` at the identity. The bracket is the mixed term of
the commutator of tangent vectors over `k[ε₁][ε₂]`.
(blueprint: `def-wf-lie-algebra-derivation`, `lemma-stable-subspaces-center--1`) -/
noncomputable def lieSubalgebra : LieSubalgebra k (Matrix n n k) where
  carrier := {X | dualUnit X ∈ zeroLocus I (DualNumber k)}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, dualUnit_add] at hX hY ⊢
    exact (zeroLocus I _).mul_mem hX hY
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, dualUnit_zero]
    exact (zeroLocus I _).one_mem
  smul_mem' c X hX := by
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [← map_scale_dualUnit]
    exact map_mem_zeroLocus _ hX
  lie_mem' {X Y} hX hY := dualUnit_lie_mem_zeroLocus (fun g hg g' hg' ↦ by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')) hX hY

variable {I}

theorem mem_lieSubalgebra {X : Matrix n n k} :
    X ∈ lieSubalgebra I ↔ dualUnit X ∈ zeroLocus I (DualNumber k) :=
  Iff.rfl

/-- `Lie` is antitone in the ideal: a closed subgroup has a smaller Lie algebra. -/
theorem lieSubalgebra_anti {J : Ideal (CoordinateRing n k)} [J.IsHopfIdeal k] (h : I ≤ J) :
    lieSubalgebra J ≤ lieSubalgebra I :=
  fun _ hX ↦ zeroLocus_anti h hX

/-- If the commutators of `V(I)` lie in `V(J)` (over `k[ε₁][ε₂]`), then the brackets of
`Lie V(I)` lie in `Lie V(J)`. (blueprint: `lemma-normality-geometric-monodromy`) -/
theorem lie_mem_lieSubalgebra_of_commutator_mem {J : Ideal (CoordinateRing n k)}
    [J.IsHopfIdeal k]
    (h : ∀ g ∈ zeroLocus I (DualNumber (DualNumber k)),
      ∀ g' ∈ zeroLocus I (DualNumber (DualNumber k)), ⁅g, g'⁆ ∈ zeroLocus J _)
    {X Y : Matrix n n k} (hX : X ∈ lieSubalgebra I) (hY : Y ∈ lieSubalgebra I) :
    ⁅X, Y⁆ ∈ lieSubalgebra J :=
  dualUnit_lie_mem_zeroLocus h hX hY

variable (I) in
/-- In characteristic zero, over an algebraically closed field, `G = V(I)` and its reduced
identity component have the same Lie algebra. (blueprint: `proposition-cartier-s-theorem`) -/
theorem lieSubalgebra_identityComponent [IsAlgClosed k] [CharZero k] :
    lieSubalgebra (identityComponent I) = lieSubalgebra I :=
  le_antisymm (lieSubalgebra_anti (le_identityComponent I))
    fun _ hX ↦ dualUnit_mem_zeroLocus_identityComponent I hX

variable (I) in
/-- The Lie algebra of `V(I)` is the range of the identification of the dual of the cotangent
space at the identity with matrices. -/
theorem range_dualCotangentToMatrixₗ :
    LinearMap.range (dualCotangentToMatrixₗ I) = (lieSubalgebra I).toSubmodule :=
  Submodule.ext fun _ ↦ mem_range_dualCotangentToMatrixₗ I

variable (I) in
/-- **Cartier's theorem, matrix form**: in characteristic zero, the Lie algebra of `V(I)` has the
dimension of `V(I)`. (blueprint: `proposition-cartier-s-theorem`,
`lemma-connected-components-images-homomorphisms--3`) -/
theorem finrank_lieSubalgebra [CharZero k] :
    (Module.finrank k (lieSubalgebra I) : WithBot ℕ∞) =
      ringKrullDim (CoordinateRing n k ⧸ I) := by
  rw [← HopfAlgebra.finrank_cotangent_eq_ringKrullDim k (CoordinateRing n k ⧸ I),
    finrank_cotangent_eq_finrank_range_dualCotangentToMatrixₗ I, range_dualCotangentToMatrixₗ]
  rfl

/-- **A closed subgroup with the Lie algebra of a connected group is the whole group**: in
characteristic zero, if `V(J) ⊆ V(I)` with `I` prime and `Lie V(J) = Lie V(I)`, then `J = I`.
(blueprint: `lemma-connected-components-images-homomorphisms--3`) -/
theorem eq_of_le_of_lieSubalgebra_eq [CharZero k] [I.IsPrime] {J : Ideal (CoordinateRing n k)}
    [J.IsHopfIdeal k] (hIJ : I ≤ J) (h : lieSubalgebra J = lieSubalgebra I) : J = I :=
  eq_of_le_of_ringKrullDim_eq I hIJ (by
    rw [← finrank_lieSubalgebra J, ← finrank_lieSubalgebra I, h])

/-- The tangent vector `1 + εX` as `1 + ε • X` with `X` viewed over `k[ε]`. -/
theorem coe_dualUnit_eq_one_add_eps_smul (X : Matrix n n k) :
    (dualUnit X : Matrix n n (DualNumber k)) =
      1 + (DualNumber.eps : DualNumber k) • (algebraMap k (DualNumber k)).mapMatrix X := by
  rw [coe_dualUnit]
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.map_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    DualNumber.inr_eq_smul_eps, Algebra.smul_def, smul_eq_mul, mul_comm]

theorem eps_smul_mapMatrix_eq_zero_iff {Z : Matrix n n k} :
    (DualNumber.eps : DualNumber k) • (algebraMap k (DualNumber k)).mapMatrix Z = 0 ↔ Z = 0 := by
  refine ⟨fun h ↦ Matrix.ext fun i j ↦ ?_, fun h ↦ by rw [h, map_zero, smul_zero]⟩
  have := congrArg (fun M : Matrix n n (DualNumber k) ↦ (M i j).snd) h
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

/-- For matrices `Y`, `X` over `k`, the tangent vector `1 + εX` commutes with `Y` if and only if
`X` does. -/
theorem commute_dualUnit_iff (X Y : Matrix n n k) :
    (algebraMap k (DualNumber k)).mapMatrix Y * (dualUnit X : Matrix n n (DualNumber k)) =
        (dualUnit X : Matrix n n (DualNumber k)) * (algebraMap k (DualNumber k)).mapMatrix Y ↔
      Y * X = X * Y := by
  rw [coe_dualUnit_eq_one_add_eps_smul, mul_add, add_mul, mul_one, one_mul, add_right_inj,
    Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, ← sub_eq_zero, ← smul_sub,
    ← map_sub, eps_smul_mapMatrix_eq_zero_iff, sub_eq_zero]

end LieSubalgebra

/-! ### The group–Lie comparison for linear conditions -/

section Comparison

variable {n : Type u} [Fintype n] [DecidableEq n] {k : Type u} [Field k]
  {I : Ideal (CoordinateRing n k)} [I.IsHopfIdeal k]

/-- A condition satisfied by all `k`-points of a reduced `G = V(I)` and cut out by equations is
satisfied by the tangent vectors `1 + εX`, `X ∈ Lie G`. -/
theorem forall_mem_lieSubalgebra_of_forall_mem_zeroLocus [IsAlgClosed k] (hI : I.IsRadical)
    {E : Set (CoordinateRing n k)} (h : ∀ g ∈ zeroLocus I k, ∀ e ∈ E, evalAlgHom g e = 0)
    {X : Matrix n n k} (hX : X ∈ lieSubalgebra I) {e : CoordinateRing n k} (he : e ∈ E) :
    evalAlgHom (k := k) (R := DualNumber k) (dualUnit X) e = 0 := by
  have hX' : dualUnit X ∈ zeroLocus I (DualNumber k) := hX
  exact hX' e (vanishingIdeal_zeroLocus_le_of_isRadical I hI
    (mem_vanishingIdeal.2 fun g hg ↦ h g hg e he))

/-- **The group–Lie comparison for closed subgroup functors.** Let `G = V(I)` be a connected closed
subgroup of `GL_n` (`I` prime) over an algebraically closed field of characteristic zero, and let
`P` be a property of the points of `G` cut out by equations `E` on `GL_n` and stable under the
group law. Then every point of `G(k)` has `P` if and only if every tangent vector `1 + εX`,
`X ∈ Lie G`, has `P`.

The closed subgroup `V(I ⊔ span E)` of `G` has the Lie algebra of `G`, hence is `G`
(`eq_of_le_of_lieSubalgebra_eq`). (blueprint: `lemma-stable-subspaces-center--1`) -/
theorem forall_zeroLocus_iff_forall_lieSubalgebra [IsAlgClosed k] [CharZero k] [I.IsPrime]
    (E : Set (CoordinateRing n k))
    (P : (R : Type u) → [CommRing R] → [Algebra k R] → zeroLocus I R → Prop)
    (hP : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : GL n R) (hg : g ∈ zeroLocus I R),
      (∀ e ∈ E, evalAlgHom g e = 0) ↔ P R ⟨g, hg⟩)
    (hone : P k 1)
    (hmul : ∀ (R : Type u) [CommRing R] [Algebra k R] (g g' : zeroLocus I R), P R g → P R g' →
      P R (g * g'))
    (hinv : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : zeroLocus I R), P R g → P R g⁻¹) :
    (∀ g : zeroLocus I k, P k g) ↔
      ∀ (X : Matrix n n k) (hX : X ∈ lieSubalgebra I), P (DualNumber k) ⟨dualUnit X, hX⟩ := by
  constructor
  · intro h X hX
    exact (hP _ _ hX).1 fun e he ↦ forall_mem_lieSubalgebra_of_forall_mem_zeroLocus
      (Ideal.IsPrime.isRadical ‹_›) (fun g hg e he ↦ (hP k g hg).2 (h ⟨g, hg⟩) e he) hX he
  · intro h
    have := isHopfIdeal_sup_span_of_forall I E ((hP k 1 (one_mem _)).2 hone)
      (fun R _ _ g g' hg hg' he he' ↦ (hP R (g * g') (mul_mem hg hg')).2
        (hmul R _ _ ((hP R g hg).1 he) ((hP R g' hg').1 he')))
      (fun R _ _ g hg he ↦ (hP R g⁻¹ (inv_mem hg)).2 (hinv R _ ((hP R g hg).1 he)))
    have hle : I ≤ I ⊔ Ideal.span E := le_sup_left
    have heq : lieSubalgebra (I ⊔ Ideal.span E) = lieSubalgebra I :=
      le_antisymm (lieSubalgebra_anti hle) fun X hX ↦
        evalAlgHom_eq_zero_sup_span_iff.2 ⟨hX, (hP _ _ hX).2 (h X hX)⟩
    have hJ := eq_of_le_of_lieSubalgebra_eq hle heq
    intro g
    refine (hP k g g.2).1 fun e he ↦ g.2 e ?_
    have : e ∈ I ⊔ Ideal.span E := Ideal.mem_sup_right (Ideal.subset_span he)
    rwa [hJ] at this

/-- **The group–Lie comparison for linear conditions.** Let `G = V(I)` be a connected closed
subgroup of `GL_n` (`I` prime) over an algebraically closed field of characteristic zero, and let
`S` be a family of subalgebras `S R ⊆ Matrix n n R`, cut out by equations `E` on `GL_n`. Then
every point of `G(k)` lies in `S k` if and only if every tangent vector `1 + εX`, `X ∈ Lie G`,
lies in `S k[ε]`: invertible matrices of a subalgebra have their inverses in it
(`Matrix.inv_mem_of_mem_subalgebra`). (blueprint: `lemma-stable-subspaces-center--1`) -/
theorem forall_mem_zeroLocus_iff_forall_mem_lieSubalgebra [IsAlgClosed k] [CharZero k]
    [I.IsPrime] (E : Set (CoordinateRing n k))
    (S : (R : Type u) → [CommRing R] → [Algebra k R] → Subalgebra R (Matrix n n R))
    (hS : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : GL n R),
      (∀ e ∈ E, evalAlgHom g e = 0) ↔ (g : Matrix n n R) ∈ S R) :
    (∀ g ∈ zeroLocus I k, (g : Matrix n n k) ∈ S k) ↔
      ∀ X ∈ lieSubalgebra I, (dualUnit X : Matrix n n (DualNumber k)) ∈ S (DualNumber k) := by
  have key := forall_zeroLocus_iff_forall_lieSubalgebra (I := I) E
    (fun R _ _ g ↦ ((g : GL n R) : Matrix n n R) ∈ S R) (fun R _ _ g _ ↦ hS R g)
    (Subalgebra.one_mem _)
    (fun R _ _ g g' hg hg' ↦ by
      rw [Subgroup.coe_mul, Units.val_mul]
      exact Subalgebra.mul_mem _ hg hg')
    (fun R _ _ g hg ↦ by
      rw [Subgroup.coe_inv, Matrix.coe_units_inv]
      exact Matrix.inv_mem_of_mem_subalgebra _ (g : GL n R).isUnit hg)
  exact ⟨fun h X hX ↦ key.1 (fun g ↦ h g g.2) X hX, fun h g hg ↦ key.2 h ⟨g, hg⟩⟩

/-! #### Stable subspaces -/

omit [DecidableEq n] in
/-- A subspace `U` of `kⁿ` is the range of an idempotent matrix fixing `U` pointwise. -/
theorem _root_.Submodule.exists_isIdempotentElem_matrix (U : Submodule k (n → k)) :
    ∃ P : Matrix n n k, IsIdempotentElem P ∧ (∀ v, P *ᵥ v ∈ U) ∧ ∀ u ∈ U, P *ᵥ u = u := by
  classical
  obtain ⟨C, hC⟩ := U.exists_isCompl
  have h1 (v : n → k) : LinearMap.toMatrix' (U.projection C hC) *ᵥ v = U.projection C hC v := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨LinearMap.toMatrix' (U.projection C hC), ?_, fun v ↦ ?_, fun u hu ↦ ?_⟩
  · rw [IsIdempotentElem, ← LinearMap.toMatrix'_mul]
    congr 1
    refine LinearMap.ext fun v ↦ ?_
    exact Submodule.projection_apply_of_mem_left hC (Submodule.projection_apply_mem hC v)
  · rw [h1]
    exact Submodule.projection_apply_mem hC v
  · rw [h1]
    exact Submodule.projection_apply_of_mem_left hC hu

/-- A matrix `M` preserves the range `U` of an idempotent matrix `P` fixing `U` if and only if
`(1 - P) M P = 0`. -/
theorem forall_mulVec_mem_iff_one_sub_mul_mul_eq_zero {U : Submodule k (n → k)}
    {P : Matrix n n k} (hP : (∀ v, P *ᵥ v ∈ U) ∧ ∀ u ∈ U, P *ᵥ u = u) (M : Matrix n n k) :
    (∀ u ∈ U, M *ᵥ u ∈ U) ↔ (1 - P) * M * P = 0 := by
  constructor
  · intro h
    refine Matrix.toLin'.injective (LinearMap.ext fun v ↦ ?_)
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hP.2 _ (h _ (hP.1 v)), sub_self]
  · intro h u hu
    have := congrArg (· *ᵥ u) h
    simp only [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hP.2 u hu, Matrix.sub_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at this
    rw [this]
    exact hP.1 _

/-- A tangent vector `1 + εX` stabilizes the range of an idempotent matrix `P` if and only if `X`
does: `(1 - P) X P = 0`. -/
theorem one_add_eps_smul_mem_ofIsIdempotentElem_iff {P : Matrix n n k} (hPi : IsIdempotentElem P)
    (X : Matrix n n k) :
    1 + (DualNumber.eps : DualNumber k) • (algebraMap k (DualNumber k)).mapMatrix X ∈
        Subalgebra.ofIsIdempotentElem (R := DualNumber k)
          (hPi.map (algebraMap k (DualNumber k)).mapMatrix) ↔
      (1 - P) * X * P = 0 := by
  rw [Subalgebra.mem_ofIsIdempotentElem]
  have h0 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPi.eq, sub_self]
  rw [mul_add, add_mul, mul_one, ← map_one (algebraMap k (DualNumber k)).mapMatrix, ← map_sub,
    ← map_mul, h0, map_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul,
    eps_smul_mapMatrix_eq_zero_iff]

/-- **Group-invariant and Lie-invariant subspaces agree.** Over an algebraically closed field of
characteristic zero, a subspace `U ⊆ kⁿ` is stable under a connected closed subgroup `G = V(I)` of
`GL_n` if and only if it is stable under its Lie algebra.

The stabilizer of `U` in `G` is the closed subgroup cut out by the linear equations
`(1 - P) g P = 0` for a projection `P` onto `U`; its Lie algebra is the stabilizer of `U` in
`Lie G`. (blueprint: `lemma-stable-subspaces-center--1`) -/
theorem forall_mulVec_mem_iff_forall_lieSubalgebra [IsAlgClosed k] [CharZero k] [I.IsPrime]
    (U : Submodule k (n → k)) :
    (∀ g ∈ zeroLocus I k, ∀ u ∈ U, (g : Matrix n n k) *ᵥ u ∈ U) ↔
      ∀ X ∈ lieSubalgebra I, ∀ u ∈ U, X *ᵥ u ∈ U := by
  obtain ⟨P, hPi, hP⟩ := U.exists_isIdempotentElem_matrix
  let S : (R : Type u) → [CommRing R] → [Algebra k R] → Subalgebra R (Matrix n n R) :=
    fun R _ _ ↦ Subalgebra.ofIsIdempotentElem (hPi.map (algebraMap k R).mapMatrix)
  have key := forall_mem_zeroLocus_iff_forall_mem_lieSubalgebra (I := I)
    (Set.range fun ij : n × n ↦ sandwichEquation (1 - P) P ij.1 ij.2) S fun R _ _ g ↦ by
      simp only [Set.forall_mem_range, Prod.forall, evalAlgHom_sandwichEquation, S,
        Subalgebra.mem_ofIsIdempotentElem]
      change (∀ i j, ((algebraMap k R).mapMatrix (1 - P) * (g : Matrix n n R) *
        (algebraMap k R).mapMatrix P : Matrix n n R) i j = 0) ↔ _
      rw [map_sub, map_one]
      exact ⟨fun h ↦ Matrix.ext fun i j ↦ h i j, fun h i j ↦ by rw [h]; rfl⟩
  have hk (M : Matrix n n k) : M ∈ S k ↔ (1 - P) * M * P = 0 := by
    simp only [S, Subalgebra.mem_ofIsIdempotentElem, Algebra.algebraMap_self,
      RingHom.mapMatrix_id, RingHom.id_apply]
  have hε (X : Matrix n n k) : (dualUnit X : Matrix n n (DualNumber k)) ∈ S (DualNumber k) ↔
      (1 - P) * X * P = 0 := by
    rw [coe_dualUnit_eq_one_add_eps_smul]
    exact one_add_eps_smul_mem_ofIsIdempotentElem_iff hPi X
  simp only [hk, hε] at key
  simp only [forall_mulVec_mem_iff_one_sub_mul_mul_eq_zero hP]
  exact key

/-! #### Centralizers -/

/-- The equations `(g Y - Y g)_ij = 0` of the centralizer of a set `T` of matrices. -/
noncomputable def centralizerEquations (T : Set (Matrix n n k)) : Set (CoordinateRing n k) :=
  ⋃ Y ∈ T, Set.range fun ij : n × n ↦
    sandwichEquation Y 1 ij.1 ij.2 - sandwichEquation 1 Y ij.1 ij.2

theorem forall_centralizerEquations_iff {T : Set (Matrix n n k)} {R : Type*} [CommRing R]
    [Algebra k R] (g : GL n R) :
    (∀ e ∈ centralizerEquations T, evalAlgHom g e = 0) ↔
      (g : Matrix n n R) ∈ Subalgebra.centralizer R ((algebraMap k R).mapMatrix '' T) := by
  simp only [centralizerEquations, Set.mem_iUnion, Set.mem_range, Prod.exists,
    forall_exists_index, Subalgebra.mem_centralizer_iff, Set.forall_mem_image]
  constructor
  · intro h Y hY
    ext i j
    have := h _ Y hY i j rfl
    rw [map_sub, evalAlgHom_sandwichEquation, evalAlgHom_sandwichEquation, sub_eq_zero] at this
    simpa using this
  · rintro h e Y hY i j rfl
    rw [map_sub, evalAlgHom_sandwichEquation, evalAlgHom_sandwichEquation, sub_eq_zero]
    simpa using congrFun₂ (h hY) i j

/-- **A matrix commutes with a connected group if and only if it commutes with its Lie algebra.**
Over an algebraically closed field of characteristic zero, the matrices of a set `T` commute with
all of `G(k)`, for `G = V(I)` connected, if and only if they commute with `Lie G`.
(blueprint: `lemma-stable-subspaces-center--2`) -/
theorem forall_commute_iff_forall_lieSubalgebra [IsAlgClosed k] [CharZero k] [I.IsPrime]
    (T : Set (Matrix n n k)) :
    (∀ g ∈ zeroLocus I k, ∀ Y ∈ T, Y * g = (g : Matrix n n k) * Y) ↔
      ∀ X ∈ lieSubalgebra I, ∀ Y ∈ T, Y * X = X * Y := by
  have key := forall_mem_zeroLocus_iff_forall_mem_lieSubalgebra (I := I) (centralizerEquations T)
    (fun R _ _ ↦ Subalgebra.centralizer R ((algebraMap k R).mapMatrix '' T))
    fun R _ _ g ↦ forall_centralizerEquations_iff g
  simp only [Subalgebra.mem_centralizer_iff, Set.forall_mem_image, Algebra.algebraMap_self,
    RingHom.mapMatrix_id, RingHom.id_apply, commute_dualUnit_iff] at key
  exact key

/-! #### The centre -/

variable (I) in
/-- The equations of the centralizer of `G(k)` in `G = V(I)`. -/
noncomputable def centerEquations : Set (CoordinateRing n k) :=
  centralizerEquations ((fun g : GL n k ↦ (g : Matrix n n k)) '' (zeroLocus I k : Set (GL n k)))

variable (I) in
/-- In characteristic zero, the ideal of the reduced centre of `G = V(I)` is cut out by the
equations of `G` and the commutation equations with `G(k)`: the scheme-theoretic centralizer
of `G(k)` in `G` is reduced (Cartier). -/
theorem center_eq_sup_span [IsAlgClosed k] [CharZero k] :
    center I = I ⊔ Ideal.span (centerEquations I) := by
  have := isHopfIdeal_sup_span_of_forall I (centerEquations I)
    ((forall_centralizerEquations_iff 1).2 (Subalgebra.one_mem _))
    (fun R _ _ g g' _ _ hg hg' ↦ (forall_centralizerEquations_iff _).2 (by
      rw [Units.val_mul]
      exact Subalgebra.mul_mem _ ((forall_centralizerEquations_iff g).1 hg)
        ((forall_centralizerEquations_iff g').1 hg')))
    (fun R _ _ g _ hg ↦ (forall_centralizerEquations_iff _).2 (by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_mem_of_mem_subalgebra _ g.isUnit
        ((forall_centralizerEquations_iff g).1 hg)))
  set J := I ⊔ Ideal.span (centerEquations I)
  have hJ : J.IsRadical := Ideal.IsHopfIdeal.isRadical (k := k) J
  have hpts : (zeroLocus J k : Set (GL n k)) = centerPoints I := by
    ext g
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_centerPoints_iff, mem_zeroLocus,
      evalAlgHom_eq_zero_sup_span_iff, centerEquations, forall_centralizerEquations_iff]
    simp only [Subalgebra.mem_centralizer_iff, Set.forall_mem_image, SetLike.mem_coe,
      Algebra.algebraMap_self, RingHom.mapMatrix_id, RingHom.id_apply]
    refine and_congr Iff.rfl (forall₂_congr fun h _ ↦ ?_)
    rw [← Units.val_mul, ← Units.val_mul, Units.val_inj, eq_comm]
  refine le_antisymm ?_ ?_
  · rw [center, ← hpts]
    exact vanishingIdeal_zeroLocus_le_of_isRadical J hJ
  · rw [center, ← hpts]
    exact le_vanishingIdeal_zeroLocus J

/-- **The Lie algebra of the centre.** Over an algebraically closed field of characteristic zero,
the Lie algebra of the centre `Z(G)` of a connected closed subgroup `G = V(I)` of `GL_n` is the
centre of the Lie algebra of `G`: the `X ∈ Lie G` commuting with all of `Lie G`.

A tangent vector of `Z(G)` is a tangent vector of `G` commuting with `G(k)` (the scheme-theoretic
centralizer is reduced, `center_eq_sup_span`), and a matrix commutes with the connected `G(k)` if
and only if it commutes with `Lie G` (`forall_commute_iff_forall_lieSubalgebra`).
(blueprint: `lemma-stable-subspaces-center--2`) -/
theorem mem_lieSubalgebra_center_iff [IsAlgClosed k] [CharZero k] [I.IsPrime]
    {X : Matrix n n k} :
    X ∈ lieSubalgebra (center I) ↔ X ∈ lieSubalgebra I ∧ ∀ Y ∈ lieSubalgebra I, X * Y = Y * X := by
  rw [mem_lieSubalgebra, mem_zeroLocus, center_eq_sup_span, evalAlgHom_eq_zero_sup_span_iff,
    centerEquations, forall_centralizerEquations_iff]
  have hc := forall_commute_iff_forall_lieSubalgebra (I := I) {X}
  simp only [Set.mem_singleton_iff, forall_eq] at hc
  simp only [Subalgebra.mem_centralizer_iff, Set.forall_mem_image, SetLike.mem_coe,
    commute_dualUnit_iff]
  refine and_congr Iff.rfl ⟨fun h Y hY ↦ (hc.1 fun g hg ↦ (h hg).symm) Y hY,
    fun h g hg ↦ (hc.2 h g hg).symm⟩

/-- The tangent vectors of the centre of a reduced `G = V(I)` commute with the Lie algebra of `G`:
they commute with `G(k)`, hence with `Lie G`. -/
theorem commute_of_mem_lieSubalgebra_center [IsAlgClosed k] (hI : I.IsRadical) {X Y : Matrix n n k}
    (hX : X ∈ lieSubalgebra (center I)) (hY : Y ∈ lieSubalgebra I) : X * Y = Y * X := by
  -- `X` commutes with `G(k)`
  have hXG (g : GL n k) (hg : g ∈ zeroLocus I k) : X * g = g * X := by
    have hmem : ∀ e ∈ centralizerEquations {(g : Matrix n n k)}, e ∈ center I := fun e he ↦
      mem_vanishingIdeal.2 fun z hz ↦ (forall_centralizerEquations_iff z).2 (by
        simp only [Subalgebra.mem_centralizer_iff, Set.image_singleton, Set.mem_singleton_iff,
          forall_eq, Algebra.algebraMap_self, RingHom.mapMatrix_id, RingHom.id_apply]
        rw [← Units.val_mul, ← Units.val_mul, (mem_centerPoints_iff I).1 hz |>.2 g hg]) e he
    have hX' : dualUnit X ∈ zeroLocus (center I) (DualNumber k) := hX
    have := (forall_centralizerEquations_iff (R := DualNumber k) (dualUnit X)).1
      fun e he ↦ hX' e (hmem e he)
    simp only [Subalgebra.mem_centralizer_iff, Set.image_singleton, Set.mem_singleton_iff,
      forall_eq, commute_dualUnit_iff] at this
    exact this.symm
  have hE : ∀ g ∈ zeroLocus I k, ∀ e ∈ centralizerEquations {X}, evalAlgHom g e = 0 :=
    fun g hg ↦ (forall_centralizerEquations_iff g).2 (by
      simp only [Subalgebra.mem_centralizer_iff, Set.image_singleton, Set.mem_singleton_iff,
        forall_eq, Algebra.algebraMap_self, RingHom.mapMatrix_id, RingHom.id_apply]
      exact hXG g hg)
  have hc := (forall_centralizerEquations_iff (R := DualNumber k) (dualUnit Y)).1 fun e he ↦
    forall_mem_lieSubalgebra_of_forall_mem_zeroLocus hI hE hY he
  simp only [Subalgebra.mem_centralizer_iff, Set.image_singleton, Set.mem_singleton_iff,
    forall_eq, commute_dualUnit_iff] at hc
  exact hc

end Comparison

end AlgebraicGeometry.GeneralLinearGroup
