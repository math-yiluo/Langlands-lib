import Langlands.GroupScheme.Quaternionic.Involution
import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Isometry groups of a twisted form as closed subgroups of an algebra-unit group

Let `A` be a finite-dimensional algebra over a field `K` with an involution of the first
kind `τ`, let `M` be a `K`-subspace of `A` and let `Q ∈ A`. For a commutative `K`-algebra
`R`, the units `u` of `R ⊗[K] A` with `u Q τ(u) - Q ∈ R ⊗ M` form a subgroup as soon as
`R ⊗ M` is stable under `y ↦ u y τ(u)`. This module constructs the affine group scheme of
these units as a closed subgroup of the unit group scheme of `A`, cut out by explicit
coordinates of `u Q τ(u) - Q` modulo `M`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.IsometryCut

open FirstKindInvolution

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]

/-! ### Coordinates modulo a subspace -/

section Coordinates

variable (M : Submodule K A) [FiniteDimensional K (A ⧸ M)]

/-- The `j`-th coordinate of the class modulo `M`, for the canonical basis of `A ⧸ M`. -/
def coordinate (j : Fin (Module.finrank K (A ⧸ M))) : A →ₗ[K] K :=
  (Module.finBasis K (A ⧸ M)).coord j ∘ₗ M.mkQ

theorem coordinate_eq_zero_of_mem (j : Fin (Module.finrank K (A ⧸ M))) {a : A}
    (ha : a ∈ M) : coordinate M j a = 0 := by
  simp [coordinate, (Submodule.Quotient.mk_eq_zero M).2 ha]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The `R`-linear extension `R ⊗[K] A → R` of `coordinate M j`. -/
def coord (j : Fin (Module.finrank K (A ⧸ M))) : R ⊗[K] A →ₗ[R] R :=
  ((Algebra.linearMap K R) ∘ₗ coordinate M j).liftBaseChange R

variable {R}

@[simp] theorem coord_tmul (j : Fin (Module.finrank K (A ⧸ M))) (r : R) (a : A) :
    coord M R j (r ⊗ₜ[K] a) = r * algebraMap K R (coordinate M j a) := by
  rw [coord, LinearMap.liftBaseChange_tmul, smul_eq_mul]
  rfl

/-- The coordinates commute with every change of coefficient algebra. -/
theorem coord_map {S : Type u} [CommRing S] [Algebra K S] (φ : R →ₐ[K] S)
    (j : Fin (Module.finrank K (A ⧸ M))) (y : R ⊗[K] A) :
    coord M S j (Algebra.TensorProduct.map φ (AlgHom.id K A) y) = φ (coord M R j y) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [_root_.map_add, LinearMap.map_add, hy, hy', LinearMap.map_add,
      _root_.map_add]
  | tmul r a => simp

/-- The coordinates of `y` are those of its image in `R ⊗[K] (A ⧸ M)`. -/
theorem baseChange_repr_mkQ (j : Fin (Module.finrank K (A ⧸ M))) (y : R ⊗[K] A) :
    ((Module.finBasis K (A ⧸ M)).baseChange R).repr (M.mkQ.baseChange R y) j =
      coord M R j y := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [LinearMap.map_add, _root_.map_add, Finsupp.add_apply, hy, hy',
      LinearMap.map_add]
  | tmul r a =>
    rw [LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul, coord_tmul,
      Algebra.smul_def, mul_comm]
    rfl

/-- An element of `R ⊗[K] A` lies in `R ⊗ M` exactly when all its coordinates modulo `M`
vanish. -/
theorem mem_baseChange_iff (y : R ⊗[K] A) :
    y ∈ M.baseChange R ↔ ∀ j, coord M R j y = 0 := by
  constructor
  · rintro ⟨z, rfl⟩ j
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [LinearMap.map_add, LinearMap.map_add, hz, hz', add_zero]
    | tmul r m =>
      rw [LinearMap.baseChange_tmul, coord_tmul, Submodule.subtype_apply,
        coordinate_eq_zero_of_mem M j m.2,
        _root_.map_zero, mul_zero]
  · intro h
    have hz : M.mkQ.baseChange R y = 0 := by
      apply ((Module.finBasis K (A ⧸ M)).baseChange R).repr.injective
      ext j
      rw [baseChange_repr_mkQ, h j, LinearEquiv.map_zero, Finsupp.zero_apply]
    have hker : y ∈ LinearMap.ker (M.mkQ.lTensor R) := by
      rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]
      exact hz
    rw [lTensor_mkQ R M] at hker
    obtain ⟨z, hz'⟩ := hker
    refine ⟨z, ?_⟩
    rw [← hz']
    exact congrFun (LinearMap.baseChange_eq_ltensor (A := R) M.subtype) z

end Coordinates

/-! ### The twisted defect and the subgroup of isometries -/

section Defect

variable (τ : FirstKindInvolution K A) (Q : A)
variable {R : Type u} [CommRing R] [Algebra K R]

/-- The defect `u Q τ(u) - Q` of `u ∈ R ⊗[K] A`, with `Q` and `τ` extended to `R`. -/
def defect (y : R ⊗[K] A) : R ⊗[K] A :=
  y * ((1 : R) ⊗ₜ[K] Q) * τ.baseChange R y - (1 : R) ⊗ₜ[K] Q

theorem defect_one : defect τ Q (1 : R ⊗[K] A) = 0 := by
  simp [defect]

theorem defect_mul (y z : R ⊗[K] A) :
    defect τ Q (y * z) = y * defect τ Q z * τ.baseChange R y + defect τ Q y := by
  simp only [defect, FirstKindInvolution.map_mul]
  noncomm_ring

theorem defect_units_inv (y : (R ⊗[K] A)ˣ) :
    defect τ Q ((y⁻¹ : (R ⊗[K] A)ˣ) : R ⊗[K] A) =
      -(((y⁻¹ : (R ⊗[K] A)ˣ) : R ⊗[K] A) * defect τ Q (y : R ⊗[K] A) *
        τ.baseChange R ((y⁻¹ : (R ⊗[K] A)ˣ) : R ⊗[K] A)) := by
  set a : R ⊗[K] A := ((y⁻¹ : (R ⊗[K] A)ˣ) : R ⊗[K] A)
  set v : R ⊗[K] A := (y : R ⊗[K] A)
  set Q' : R ⊗[K] A := (1 : R) ⊗ₜ[K] Q
  have h1 : a * v = 1 := Units.inv_mul y
  have h2 : τ.baseChange R v * τ.baseChange R a = 1 := by
    rw [← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one]
  have h3 : a * (v * Q' * τ.baseChange R v - Q') * τ.baseChange R a =
      Q' - a * Q' * τ.baseChange R a := by
    calc a * (v * Q' * τ.baseChange R v - Q') * τ.baseChange R a
        = (a * v) * Q' * (τ.baseChange R v * τ.baseChange R a) -
            a * Q' * τ.baseChange R a := by noncomm_ring
      _ = Q' - a * Q' * τ.baseChange R a := by rw [h1, h2, one_mul, mul_one]
  change a * Q' * τ.baseChange R a - Q' = -(a * (v * Q' * τ.baseChange R v - Q') *
    τ.baseChange R a)
  rw [h3, neg_sub]

/-- Changing `Q` by `Q' - Q` changes the defect by the defect-type expression of `Q' - Q`. -/
theorem defect_sub_defect (Q' : A) (y : R ⊗[K] A) :
    defect τ Q' y - defect τ Q y =
      y * ((1 : R) ⊗ₜ[K] (Q' - Q)) * τ.baseChange R y - (1 : R) ⊗ₜ[K] (Q' - Q) := by
  simp only [defect, TensorProduct.tmul_sub]
  noncomm_ring

end Defect

variable (τ : FirstKindInvolution K A) (M : Submodule K A)

/-- Stability of `R ⊗ M` under `y ↦ u y τ(u)` for all coefficient algebras. -/
def IsStable : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra K R] (y z : R ⊗[K] A),
    z ∈ M.baseChange R → y * z * τ.baseChange R y ∈ M.baseChange R

variable {τ M}

/-- The zero subspace is stable. -/
theorem isStable_bot : IsStable τ (⊥ : Submodule K A) := by
  intro R _ _ y z hz
  rw [Submodule.baseChange_bot, Submodule.mem_bot] at hz ⊢
  rw [hz, mul_zero, zero_mul]

/-- Extension of scalars of the alternating subspace `{a - τ a}` is the alternating
subspace of the extended involution. -/
theorem alternatingSubspace_baseChange (R : Type u) [CommRing R] [Algebra K R] :
    τ.alternatingSubspace.baseChange R =
      (τ.baseChange R).alternatingSubspace.restrictScalars R := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      rw [LinearMap.map_add]
      exact Submodule.add_mem _ hz hz'
    | tmul r m =>
      obtain ⟨a, ha⟩ := τ.mem_alternatingSubspace.1 m.2
      rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, Submodule.restrictScalars_mem,
        mem_alternatingSubspace]
      exact ⟨r ⊗ₜ[K] a, by rw [baseChange_tmul, ← TensorProduct.tmul_sub, ha]⟩
  · intro hy
    rw [Submodule.restrictScalars_mem, mem_alternatingSubspace] at hy
    obtain ⟨z, rfl⟩ := hy
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      rw [FirstKindInvolution.map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hz hz'
    | tmul r a =>
      rw [baseChange_tmul, ← TensorProduct.tmul_sub]
      exact Submodule.tmul_mem_baseChange_of_mem r (τ.sub_mem_alternatingSubspace a)

/-- Tits's subspace `{a - τ a}` is stable. -/
theorem isStable_alternatingSubspace : IsStable τ τ.alternatingSubspace := by
  intro R _ _ y z hz
  rw [alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    mem_alternatingSubspace] at hz ⊢
  obtain ⟨w, rfl⟩ := hz
  refine ⟨y * w * τ.baseChange R y, ?_⟩
  simp only [FirstKindInvolution.map_mul, apply_apply]
  noncomm_ring

/-- The defect commutes with every change of coefficient algebra. -/
theorem map_defect (τ : FirstKindInvolution K A) (Q : A) {R S : Type u} [CommRing R]
    [Algebra K R] [CommRing S] [Algebra K S] (φ : R →ₐ[K] S) (y : R ⊗[K] A) :
    Algebra.TensorProduct.map φ (AlgHom.id K A) (defect τ Q y) =
      defect τ Q (Algebra.TensorProduct.map φ (AlgHom.id K A) y) := by
  simp only [defect, _root_.map_sub, _root_.map_mul, Algebra.TensorProduct.map_tmul,
    _root_.map_one, AlgHom.id_apply, map_baseChange]

/-- The units `u` of `R ⊗[K] A` with `u Q τ(u) - Q ∈ R ⊗ M`. -/
def isometrySubgroup (hM : IsStable τ M) (Q : A) (R : Type u) [CommRing R] [Algebra K R] :
    Subgroup (R ⊗[K] A)ˣ where
  carrier := {y | defect τ Q (y : R ⊗[K] A) ∈ M.baseChange R}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, defect_one]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro y z hy hz
    simp only [Set.mem_ofPred_eq, Units.val_mul, defect_mul] at hy hz ⊢
    exact Submodule.add_mem _ (hM R _ _ hz) hy
  inv_mem' := by
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [defect_units_inv]
    exact Submodule.neg_mem _ (hM R _ _ hy)

theorem mem_isometrySubgroup (hM : IsStable τ M) (Q : A) {R : Type u} [CommRing R]
    [Algebra K R] (y : (R ⊗[K] A)ˣ) :
    y ∈ isometrySubgroup hM Q R ↔ defect τ Q (y : R ⊗[K] A) ∈ M.baseChange R :=
  Iff.rfl

/-- Over a stable subspace, the defining condition depends only on `Q` modulo `M`. -/
theorem defect_mem_iff_of_sub_mem (hM : IsStable τ M) {Q Q' : A} (h : Q' - Q ∈ M)
    {R : Type u} [CommRing R] [Algebra K R] (y : R ⊗[K] A) :
    defect τ Q' y ∈ M.baseChange R ↔ defect τ Q y ∈ M.baseChange R := by
  have hQ : (1 : R) ⊗ₜ[K] (Q' - Q) ∈ M.baseChange R :=
    Submodule.tmul_mem_baseChange_of_mem _ h
  have hd : defect τ Q' y - defect τ Q y ∈ M.baseChange R := by
    rw [defect_sub_defect]
    exact Submodule.sub_mem _ (hM R _ _ hQ) hQ
  constructor
  · intro h'
    have h'' := Submodule.sub_mem _ h' hd
    rwa [sub_sub_cancel] at h''
  · intro h'
    have h'' := Submodule.add_mem _ hd h'
    rwa [sub_add_cancel] at h''

/-- A value of the unit functor of `A`, regarded as a unit of `R ⊗[K] A`. -/
abbrev unitOf {R : CommAlgCat.{u} (CommRingCat.of K)}
    (x : (FiniteAlgebraUnits.functor K A).obj R) : (R ⊗[K] A)ˣ :=
  x

/-- The isometry subgroups, as subgroups of the values of the unit functor of `A`. -/
def isometryFamily (hM : IsStable τ M) (Q : A) :
    ∀ R : CommAlgCat.{u} (CommRingCat.of K),
      Subgroup ((FiniteAlgebraUnits.functor K A).obj R) :=
  fun R => isometrySubgroup hM Q R

theorem mem_isometryFamily (hM : IsStable τ M) (Q : A) {R : CommAlgCat.{u} (CommRingCat.of K)}
    (x : (FiniteAlgebraUnits.functor K A).obj R) :
    x ∈ isometryFamily hM Q R ↔
      defect τ Q (unitOf x : R ⊗[K] A) ∈ M.baseChange R :=
  Iff.rfl

/-! ### The cut-out closed subgroup scheme -/

variable [FiniteDimensional K A]

variable (K A) in
/-- The canonical coordinate basis of `A`. -/
abbrev unitsBasis : Module.Basis (Fin (Module.finrank K A)) K A :=
  Module.finBasis K A

variable (τ M) in
/-- The defining coordinates of `u Q τ(u) - Q` modulo `M` at the universal unit. -/
def generator (Q : A) (j : Fin (Module.finrank K (A ⧸ M))) :
    FiniteAlgebraUnits.candidateRing (unitsBasis K A) :=
  coord M _ j (defect τ Q
    (FiniteAlgebraUnits.algebraicUniversalUnit (unitsBasis K A) :
      FiniteAlgebraUnits.candidateRing (unitsBasis K A) ⊗[K] A))

variable (τ M) in
/-- The ideal of the unit coordinate ring generated by those coordinates. -/
def ideal (Q : A) : Ideal (FiniteAlgebraUnits.coordinateAlgebra (unitsBasis K A)) :=
  Ideal.span (Set.range (generator τ M Q))

/-- The isometry subgroups are cut out by `ideal`. -/
theorem isCutOutBy (hM : IsStable τ M) (Q : A) :
    Corepresented.IsCutOutBy (FiniteAlgebraUnits.corepresentableBy (unitsBasis K A))
      (isometryFamily hM Q) (ideal τ M Q) := by
  intro R x
  change x ∈ isometryFamily hM Q R ↔
    ∀ c ∈ ideal τ M Q, FiniteAlgebraUnits.unitCoefficientMap (unitsBasis K A) x c = 0
  set φ := FiniteAlgebraUnits.unitCoefficientMap (unitsBasis K A) x
  have hx : (unitOf x : R ⊗[K] A) = Algebra.TensorProduct.map φ (AlgHom.id K A)
      (FiniteAlgebraUnits.algebraicUniversalUnit (unitsBasis K A) :
        FiniteAlgebraUnits.candidateRing (unitsBasis K A) ⊗[K] A) := by
    conv_lhs => rw [← FiniteAlgebraUnits.algebraicPoint_unitCoefficientMap (unitsBasis K A) x]
    rfl
  have key : ∀ j, φ (generator τ M Q j) =
      coord M R j (defect τ Q (unitOf x : R ⊗[K] A)) := by
    intro j
    rw [generator, ← coord_map, map_defect, ← hx]
  rw [mem_isometryFamily, mem_baseChange_iff]
  constructor
  · intro h c hc
    have hle : ideal τ M Q ≤ RingHom.ker (φ : _ →+* R) := by
      rw [ideal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change φ _ = 0
      rw [key]
      exact h j
    exact hle hc
  · intro h j
    rw [← key]
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

/-- The affine group scheme of isometries: its points with values in `R` are the units `u` of
`R ⊗[K] A` with `u Q τ(u) - Q ∈ R ⊗ M`. -/
abbrev groupScheme (hM : IsStable τ M) (Q : A) : GroupScheme (Spec (CommRingCat.of K)) :=
  Corepresented.cutGroupScheme (isCutOutBy hM Q)

/-- The inclusion into the unit group scheme of `A`. -/
def inclusion (hM : IsStable τ M) (Q : A) :
    groupScheme hM Q ⟶ FiniteAlgebraUnits.groupScheme (unitsBasis K A) :=
  Corepresented.cutHom (isCutOutBy hM Q)

/-- The inclusion is a closed subgroup. -/
theorem isClosedSubgroup_inclusion (hM : IsStable τ M) (Q : A) :
    IsClosedSubgroup (inclusion hM Q) :=
  Corepresented.isClosedSubgroup_cutHom (isCutOutBy hM Q)

/-- On every test scheme `T`, a point of the unit group lies in the isometry group exactly
when its unit `u` over the global sections `R = Γ(T)` satisfies `u Q τ(u) - Q ∈ R ⊗ M`. -/
theorem mem_range_inclusion_iff (hM : IsStable τ M) (Q : A)
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (unitsBasis K A)).X) :
    x ∈ (SubgroupFunctor.range (inclusion hM Q)).carrier T ↔
      defect τ Q (FiniteAlgebraUnits.pointsEquiv (unitsBasis K A) T x :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] A) ∈
        M.baseChange ((algΓ (CommRingCat.of K)).obj T).unop := by
  unfold inclusion
  rw [Corepresented.range_cutHom]
  exact Corepresented.mem_cutSubgroupFunctor (isCutOutBy hM Q)

end Langlands.GroupScheme.Quaternionic.IsometryCut
