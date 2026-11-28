import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Centralizers of idempotents

Let `A` be a ring and `e ∈ A` an idempotent, `f = 1 - e`. The centralizer
`M = Subalgebra.centralizer F {e}` of `e` in an `F`-algebra `A` is the subalgebra
`e A e ⊕ f A f`. For a finite-dimensional semisimple `A` over a characteristic-zero local
field `F`, the unit group `Mˣ` is the centralizer in `Aˣ` of the split torus with points
`t e + s f` for `t, s ∈ Fˣ` and the Levi factor of the block upper triangular parabolic.
This module proves the following algebraic facts.

* `isSemisimpleRing_centralizer`: if `A` is a semisimple ring, so is `M`;
* `finrank_centralizer_lt`: if `A` is finite-dimensional and `e` is not central, then
  `dim M < dim A`;
* `mem_regularSet_centralizer`: over an infinite field, an element of `M` that is regular in
  `A` (Harish-Chandra's `g'`, `regularSet`) is regular in `M`.
-/

noncomputable section

open Polynomial Module

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe u v

namespace IdempotentCentralizer

section Semisimple

variable {A : Type v} [Ring A] {e : A}

/-- The `A × A`-module structure `(a, b) • x = a x e + b x (1 - e)` on the additive group of
`A`, for an idempotent `e`. -/
@[reducible] def bimoduleModule (he : IsIdempotentElem e) : Module (A × A) A where
  smul p x := p.1 * x * e + p.2 * x * (1 - e)
  one_smul x := by
    change (1 : A) * x * e + 1 * x * (1 - e) = x
    simp only [one_mul, mul_sub, mul_one, add_sub_cancel]
  mul_smul p q x := by
    change p.1 * q.1 * x * e + p.2 * q.2 * x * (1 - e) =
      p.1 * (q.1 * x * e + q.2 * x * (1 - e)) * e +
        p.2 * (q.1 * x * e + q.2 * x * (1 - e)) * (1 - e)
    have h1 : e * e = e := he.eq
    have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
    simp only [mul_add, add_mul, mul_assoc, h1, h2, h3, h4, mul_zero, add_zero, zero_add]
  smul_zero p := by
    change p.1 * (0 : A) * e + p.2 * (0 : A) * (1 - e) = 0
    simp
  smul_add p x y := by
    change p.1 * (x + y) * e + p.2 * (x + y) * (1 - e) =
      (p.1 * x * e + p.2 * x * (1 - e)) + (p.1 * y * e + p.2 * y * (1 - e))
    simp only [mul_add, add_mul]
    abel
  add_smul p q x := by
    change (p.1 + q.1) * x * e + (p.2 + q.2) * x * (1 - e) =
      (p.1 * x * e + p.2 * x * (1 - e)) + (q.1 * x * e + q.2 * x * (1 - e))
    simp only [add_mul]
    abel
  zero_smul x := by
    change (0 : A) * x * e + (0 : A) * x * (1 - e) = 0
    simp

theorem bimodule_smul_def (he : IsIdempotentElem e) (p : A × A) (x : A) :
    letI := bimoduleModule he
    p • x = p.1 * x * e + p.2 * x * (1 - e) := rfl

theorem bimodule_diag_smul_one (he : IsIdempotentElem e) (x : A) :
    letI := bimoduleModule he
    (x, x) • (1 : A) = x := by
  rw [bimodule_smul_def, mul_one, mul_sub, mul_one, add_sub_cancel]

/-- Every endomorphism of the `A × A`-module is right multiplication by its value at `1`. -/
theorem bimodule_end_apply (he : IsIdempotentElem e) :
    letI := bimoduleModule he
    ∀ (φ : Module.End (A × A) A) (x : A), φ x = x * φ 1 := by
  let _ : Module (A × A) A := bimoduleModule he
  intro φ x
  conv_lhs => rw [← bimodule_diag_smul_one he x]
  rw [map_smul, bimodule_smul_def, mul_sub (x * _), mul_one, add_sub_cancel]

variable (F : Type u) [CommRing F] [Algebra F A]

theorem mem_centralizer_singleton_iff {x : A} :
    x ∈ Subalgebra.centralizer F ({e} : Set A) ↔ e * x = x * e := by
  rw [Subalgebra.mem_centralizer_iff]
  simp

/-- The value at `1` of an endomorphism of the `A × A`-module commutes with `e`. -/
theorem bimodule_end_one_mem (he : IsIdempotentElem e) :
    letI := bimoduleModule he
    ∀ φ : Module.End (A × A) A, φ 1 ∈ Subalgebra.centralizer F ({e} : Set A) := by
  let _ : Module (A × A) A := bimoduleModule he
  intro φ
  rw [mem_centralizer_singleton_iff]
  have h1 : φ e = e * φ 1 := bimodule_end_apply he φ e
  have he1 : ((1 : A), (0 : A)) • (1 : A) = e := by
    rw [bimodule_smul_def]
    simp
  have h2 : φ e = φ 1 * e := by
    calc φ e = φ (((1 : A), (0 : A)) • (1 : A)) := by rw [he1]
      _ = φ 1 * e := by rw [map_smul, bimodule_smul_def]; simp
  rw [← h1, h2]

/-- Right multiplication by an element of the centralizer of `e`, as an endomorphism of the
`A × A`-module. -/
def rightMulEnd (he : IsIdempotentElem e) (m : Subalgebra.centralizer F ({e} : Set A)) :
    letI := bimoduleModule he
    Module.End (A × A) A :=
  letI := bimoduleModule he
  { toFun := fun x => x * (m : A)
    map_add' := fun x y => add_mul x y (m : A)
    map_smul' := fun p x => by
      have hm : e * (m : A) = (m : A) * e := (mem_centralizer_singleton_iff F).1 m.2
      have hm' : (1 - e) * (m : A) = (m : A) * (1 - e) := by
        rw [sub_mul, mul_sub, one_mul, mul_one, hm]
      change (p.1 * x * e + p.2 * x * (1 - e)) * (m : A) =
        p.1 * (x * m) * e + p.2 * (x * m) * (1 - e)
      rw [add_mul, mul_assoc (p.1 * x), hm, mul_assoc (p.2 * x), hm']
      simp only [mul_assoc] }

theorem rightMulEnd_apply (he : IsIdempotentElem e) (m : Subalgebra.centralizer F ({e} : Set A))
    (x : A) : rightMulEnd F he m x = x * (m : A) := rfl

/-- The endomorphism ring of the `A × A`-module `A` is the opposite of the centralizer of
`e`. -/
def endRingEquiv (he : IsIdempotentElem e) :
    letI := bimoduleModule he
    Module.End (A × A) A ≃+* (Subalgebra.centralizer F ({e} : Set A))ᵐᵒᵖ :=
  letI := bimoduleModule he
  { toFun := fun φ => MulOpposite.op ⟨φ 1, bimodule_end_one_mem F he φ⟩
    invFun := fun m => rightMulEnd F he m.unop
    left_inv := fun φ => by
      ext x
      change x * φ 1 = φ x
      rw [bimodule_end_apply he φ x]
    right_inv := fun m => by
      apply MulOpposite.unop_injective
      apply Subtype.ext
      change (1 : A) * (m.unop : A) = m.unop
      rw [one_mul]
    map_mul' := fun φ ψ => by
      apply MulOpposite.unop_injective
      apply Subtype.ext
      change φ (ψ 1) = ψ 1 * φ 1
      exact bimodule_end_apply he φ (ψ 1)
    map_add' := fun φ ψ => by
      apply MulOpposite.unop_injective
      apply Subtype.ext
      rfl }

/-- The centralizer of an idempotent in a semisimple algebra is a semisimple ring. -/
theorem isSemisimpleRing_centralizer [IsSemisimpleRing A] (he : IsIdempotentElem e) :
    IsSemisimpleRing (Subalgebra.centralizer F ({e} : Set A)) := by
  let _ : Module (A × A) A := bimoduleModule he
  have : Module.Finite (A × A) A := by
    refine ⟨⟨{(1 : A)}, ?_⟩⟩
    rw [Finset.coe_singleton, eq_top_iff]
    intro x _
    rw [Submodule.mem_span_singleton]
    exact ⟨(x, x), bimodule_diag_smul_one he x⟩
  have := IsSemisimpleRing.moduleEnd (A × A) A
  have : IsSemisimpleRing (Subalgebra.centralizer F ({e} : Set A))ᵐᵒᵖ :=
    (endRingEquiv F he).isSemisimpleRing
  exact isSemisimpleRing_mulOpposite_iff.1 inferInstance

end Semisimple

section Dimension

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- The centralizer of a non-central element is a proper subspace, of smaller dimension. -/
theorem finrank_centralizer_lt {e : A} (hc : ∃ a : A, e * a ≠ a * e) :
    finrank F (Subalgebra.centralizer F ({e} : Set A)) < finrank F A := by
  obtain ⟨a, ha⟩ := hc
  have hlt : Subalgebra.toSubmodule (Subalgebra.centralizer F ({e} : Set A)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : a ∈ Subalgebra.toSubmodule (Subalgebra.centralizer F ({e} : Set A)) := by
      rw [htop]; exact Submodule.mem_top
    exact ha ((mem_centralizer_singleton_iff F).1 this)
  exact Submodule.finrank_lt hlt.ne

end Dimension

section Characteristic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characteristic polynomial of an endomorphism preserving two complementary subspaces is
the product of the characteristic polynomials of its restrictions. -/
theorem charpoly_eq_mul_of_isCompl (φ : Module.End K V) {P Q : Submodule K V}
    (hPQ : IsCompl P Q) (hP : ∀ x ∈ P, φ x ∈ P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    φ.charpoly = (φ.restrict hP).charpoly * (φ.restrict hQ).charpoly := by
  let E := Submodule.prodEquivOfIsCompl P Q hPQ
  have hψ : (φ.restrict hP).prodMap (φ.restrict hQ) = E.symm.conj φ := by
    apply LinearMap.ext
    intro p
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, eq_comm, LinearEquiv.symm_apply_eq]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl',
      LinearMap.prodMap_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, map_add]
  rw [← E.symm.charpoly_conj φ, ← hψ, LinearMap.charpoly_prodMap]

end Characteristic

section Regular

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A]

/-- The projection `x ↦ e x e + (1 - e) x (1 - e)` onto the centralizer of an idempotent `e`. -/
def diagonalProjection (e : A) : A →ₗ[F] A where
  toFun x := e * x * e + (1 - e) * x * (1 - e)
  map_add' x y := by simp only [mul_add, add_mul]; abel
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_add, mul_smul_comm, smul_mul_assoc]

theorem diagonalProjection_apply (e x : A) :
    diagonalProjection F e x = e * x * e + (1 - e) * x * (1 - e) := rfl

/-- The off-diagonal part `e A (1 - e) ⊕ (1 - e) A e`: the kernel of the diagonal projection. -/
def offDiagonal (e : A) : Submodule F A := LinearMap.ker (diagonalProjection F e)

theorem mem_offDiagonal_iff {e x : A} :
    x ∈ offDiagonal F e ↔ diagonalProjection F e x = 0 := LinearMap.mem_ker

variable {F} {e : A}

/-- Products with an idempotent `e` and with `1 - e`, in right-associated form. -/
theorem idempotent_mul_rules (he : IsIdempotentElem e) :
    e * e = e ∧ (1 - e) * e = 0 ∧ e * (1 - e) = 0 ∧ (1 - e) * (1 - e) = 1 - e ∧
      (∀ y : A, e * (e * y) = e * y) ∧ (∀ y : A, (1 - e) * (e * y) = 0) ∧
      (∀ y : A, e * ((1 - e) * y) = 0) ∧ (∀ y : A, (1 - e) * ((1 - e) * y) = (1 - e) * y) := by
  have h1 : e * e = e := he.eq
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
  have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  refine ⟨h1, h2, h3, h4, fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [← mul_assoc, h1]
  · rw [← mul_assoc, h2, zero_mul]
  · rw [← mul_assoc, h3, zero_mul]
  · rw [← mul_assoc, h4]

theorem diagonalProjection_of_commute (he : IsIdempotentElem e) {x : A} (hx : e * x = x * e) :
    diagonalProjection F e x = x := by
  have h1 : (1 - e) * x = x * (1 - e) := by rw [sub_mul, mul_sub, one_mul, mul_one, hx]
  rw [diagonalProjection_apply, hx, h1, mul_assoc, he.eq, mul_assoc, he.one_sub.eq, ← mul_add,
    add_sub_cancel, mul_one]

theorem commute_diagonalProjection (he : IsIdempotentElem e) (x : A) :
    e * diagonalProjection F e x = diagonalProjection F e x * e := by
  obtain ⟨h1, h2, -, -, h1', -, h3', -⟩ := idempotent_mul_rules he
  simp only [diagonalProjection_apply, mul_add, add_mul, mul_assoc, h1, h2, h1', h3', mul_zero,
    add_zero]

theorem diagonalProjection_idem (he : IsIdempotentElem e) (x : A) :
    diagonalProjection F e (diagonalProjection F e x) = diagonalProjection F e x :=
  diagonalProjection_of_commute he (commute_diagonalProjection he x)

theorem diagonalProjection_mul_left {Y : A} (hY : e * Y = Y * e)
    (x : A) : diagonalProjection F e (Y * x) = Y * diagonalProjection F e x := by
  have hY' : (1 - e) * Y = Y * (1 - e) := by rw [sub_mul, mul_sub, one_mul, mul_one, hY]
  rw [diagonalProjection_apply, diagonalProjection_apply, mul_add, ← mul_assoc e Y, hY,
    ← mul_assoc (1 - e) Y, hY']
  simp only [mul_assoc]

theorem diagonalProjection_mul_right {Y : A} (hY : e * Y = Y * e)
    (x : A) : diagonalProjection F e (x * Y) = diagonalProjection F e x * Y := by
  have hY₁ : Y * e = e * Y := hY.symm
  have hY₂ : Y * (1 - e) = (1 - e) * Y := by rw [sub_mul, mul_sub, one_mul, mul_one, hY]
  rw [diagonalProjection_apply, diagonalProjection_apply, add_mul]
  simp only [mul_assoc, hY₁, hY₂]

theorem isCompl_centralizer_offDiagonal (he : IsIdempotentElem e) :
    IsCompl (Subalgebra.toSubmodule (Subalgebra.centralizer F ({e} : Set A))) (offDiagonal F e) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have hc : e * x = x * e := (mem_centralizer_singleton_iff F).1 hx
    rw [← diagonalProjection_of_commute (F := F) he hc]
    exact (mem_offDiagonal_iff F).1 hx'
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨diagonalProjection F e x, ?_, x - diagonalProjection F e x, ?_, by abel⟩
    · exact (mem_centralizer_singleton_iff F).2 (commute_diagonalProjection he x)
    · rw [mem_offDiagonal_iff, map_sub, diagonalProjection_idem he, sub_self]

theorem adjoint_mem_centralizer {Y : A} (hY : Y ∈ Subalgebra.centralizer F ({e} : Set A)) :
    ∀ x ∈ Subalgebra.toSubmodule (Subalgebra.centralizer F ({e} : Set A)),
      adjointEndomorphism F Y x ∈ Subalgebra.toSubmodule (Subalgebra.centralizer F ({e} : Set A)) := by
  intro x hx
  rw [adjointEndomorphism_apply]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hY hx) (Subalgebra.mul_mem _ hx hY)

theorem adjoint_mem_offDiagonal {Y : A}
    (hY : Y ∈ Subalgebra.centralizer F ({e} : Set A)) :
    ∀ x ∈ offDiagonal F e, adjointEndomorphism F Y x ∈ offDiagonal F e := by
  intro x hx
  have hc : e * Y = Y * e := (mem_centralizer_singleton_iff F).1 hY
  rw [mem_offDiagonal_iff] at hx ⊢
  rw [adjointEndomorphism_apply, map_sub, diagonalProjection_mul_left hc,
    diagonalProjection_mul_right hc, hx, mul_zero, zero_mul, sub_zero]

variable (F) in
/-- The adjoint action of the centralizer `M` of `e` on the off-diagonal part, as a linear family
of endomorphisms. -/
def offDiagonalAdjoint (e : A) :
    Subalgebra.centralizer F ({e} : Set A) →ₗ[F] Module.End F (offDiagonal F e) where
  toFun Y := (adjointEndomorphism F (Y : A)).restrict (adjoint_mem_offDiagonal Y.2)
  map_add' Y Z := by
    ext x
    simp only [LinearMap.coe_restrict_apply, LinearMap.add_apply, Submodule.coe_add,
      adjointEndomorphism_apply, Subalgebra.coe_add, add_mul, mul_add]
    abel
  map_smul' c Y := by
    ext x
    simp only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, Submodule.coe_smul,
      adjointEndomorphism_apply, Subalgebra.coe_smul, RingHom.id_apply, smul_mul_assoc,
      mul_smul_comm, smul_sub]

theorem offDiagonalAdjoint_apply
    (Y : Subalgebra.centralizer F ({e} : Set A)) (x : offDiagonal F e) :
    ((offDiagonalAdjoint F e Y x : offDiagonal F e) : A) = (Y : A) * x - x * (Y : A) := rfl

variable [FiniteDimensional F A]

/-- For `Y` in the centralizer `M` of `e`, the characteristic polynomial of `ad Y` on `A` is the
product of those of `ad Y` on `M` and on the off-diagonal part. -/
theorem charpoly_adjointEndomorphism_eq_mul (he : IsIdempotentElem e)
    (Y : Subalgebra.centralizer F ({e} : Set A)) :
    (adjointEndomorphism F (Y : A)).charpoly =
      (adjointEndomorphism F Y).charpoly * (offDiagonalAdjoint F e Y).charpoly := by
  rw [charpoly_eq_mul_of_isCompl (adjointEndomorphism F (Y : A))
    (isCompl_centralizer_offDiagonal he) (adjoint_mem_centralizer Y.2)
    (adjoint_mem_offDiagonal Y.2)]
  congr 1

theorem natTrailingDegree_charpoly_adjointEndomorphism (he : IsIdempotentElem e)
    (Y : Subalgebra.centralizer F ({e} : Set A)) :
    (adjointEndomorphism F (Y : A)).charpoly.natTrailingDegree =
      (adjointEndomorphism F Y).charpoly.natTrailingDegree +
        (offDiagonalAdjoint F e Y).charpoly.natTrailingDegree := by
  rw [charpoly_adjointEndomorphism_eq_mul he Y,
    natTrailingDegree_mul (LinearMap.charpoly_monic _).ne_zero (LinearMap.charpoly_monic _).ne_zero]

omit [FiniteDimensional F A] in
/-- `ad e` has no kernel on the off-diagonal part. -/
theorem offDiagonalAdjoint_injective (he : IsIdempotentElem e)
    (he' : e ∈ Subalgebra.centralizer F ({e} : Set A)) :
    ∀ x : offDiagonal F e, offDiagonalAdjoint F e ⟨e, he'⟩ x = 0 → x = 0 := by
  intro x hx
  have hx' : e * (x : A) - (x : A) * e = 0 := by
    have := congrArg (fun z : offDiagonal F e => (z : A)) hx
    simpa only [offDiagonalAdjoint_apply, Submodule.coe_zero] using this
  have hc : e * (x : A) = (x : A) * e := sub_eq_zero.1 hx'
  apply Subtype.ext
  rw [Submodule.coe_zero, ← diagonalProjection_of_commute (F := F) he hc]
  exact (mem_offDiagonal_iff F).1 x.2

/-- Over an infinite field, some element of the centralizer `M` of `e` is regular in `M` and acts
invertibly on the off-diagonal part. -/
theorem exists_regular_offDiagonal_invertible [Infinite F] (he : IsIdempotentElem e) :
    ∃ Y : Subalgebra.centralizer F ({e} : Set A),
      Y ∈ regularSet F (Subalgebra.centralizer F ({e} : Set A)) ∧
        (offDiagonalAdjoint F e Y).charpoly.natTrailingDegree = 0 := by
  classical
  let b := Module.Free.chooseBasis F (Subalgebra.centralizer F ({e} : Set A))
  let P := (LinearMap.polyCharpoly
    (LieAlgebra.ad F (Subalgebra.centralizer F ({e} : Set A))).toLinearMap b).coeff
      (LieAlgebra.rank F (Subalgebra.centralizer F ({e} : Set A)))
  let Q := (LinearMap.polyCharpoly (offDiagonalAdjoint F e) b).coeff 0
  have hP : P ≠ 0 := LieAlgebra.polyCharpoly_coeff_rank_ne_zero F _ b
  have he' : e ∈ Subalgebra.centralizer F ({e} : Set A) :=
    (mem_centralizer_singleton_iff F).2 rfl
  have hQe : MvPolynomial.eval (b.repr ⟨e, he'⟩) Q ≠ 0 := by
    rw [LinearMap.polyCharpoly_coeff_eval, ← Polynomial.constantCoeff_apply]
    exact ((LinearMap.not_hasEigenvalue_zero_tfae (offDiagonalAdjoint F e ⟨e, he'⟩)).out 3 6).2
      (offDiagonalAdjoint_injective he he')
  have hQ : Q ≠ 0 := fun h => hQe (by rw [h, map_zero])
  have hPQ : P * Q ≠ 0 := mul_ne_zero hP hQ
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (P * Q) ≠ 0 := by
    by_contra! h
    exact hPQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul] at hx
  let Y := b.repr.symm (Finsupp.equivFunOnFinite.symm x)
  have hYx : ⇑(b.repr Y) = x := by
    simp only [Y, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
  refine ⟨Y, ?_, ?_⟩
  · rw [mem_regularSet_iff_isRegular, LieAlgebra.isRegular_iff_coeff_polyCharpoly_rank_ne_zero F b,
      hYx]
    exact left_ne_zero_of_mul hx
  · have hQY : MvPolynomial.eval (b.repr Y) Q ≠ 0 := by
      rw [hYx]; exact right_ne_zero_of_mul hx
    rw [LinearMap.polyCharpoly_coeff_eval] at hQY
    exact Polynomial.natTrailingDegree_eq_zero.2 (Or.inr hQY)

/-- **Regular elements stay regular in the centralizer of an idempotent.** Over an infinite
field, an element of the centralizer `M` of an idempotent `e` that is regular in `A` is regular
in `M`. -/
theorem mem_regularSet_centralizer [Infinite F] (he : IsIdempotentElem e)
    (X : Subalgebra.centralizer F ({e} : Set A)) (hX : (X : A) ∈ regularSet F A) :
    X ∈ regularSet F (Subalgebra.centralizer F ({e} : Set A)) := by
  obtain ⟨Y, hY, hY0⟩ := exists_regular_offDiagonal_invertible (F := F) he
  have h1 := (mem_regularSet_iff F Y).1 hY
  have h2 := lieAlgebraRank_le F (Y : A)
  rw [natTrailingDegree_charpoly_adjointEndomorphism he Y, hY0, h1] at h2
  have h3 := (mem_regularSet_iff F (X : A)).1 hX
  rw [natTrailingDegree_charpoly_adjointEndomorphism he X] at h3
  have h4 := lieAlgebraRank_le F X
  rw [mem_regularSet_iff]
  omega

end Regular

end IdempotentCentralizer

end Langlands.HarmonicAnalysis.UnitConjugation
