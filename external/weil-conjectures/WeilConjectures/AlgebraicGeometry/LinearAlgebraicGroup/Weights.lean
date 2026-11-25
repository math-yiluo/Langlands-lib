/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Archimedean
public import Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.Mathlib.Data.Multiset.MapFold
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.ToLin
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.ExteriorPower
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.Kronecker
public import WeilConjectures.RepresentationTheory.ExteriorPower

/-!
# Determinant weights of a degree datum

A *real character* is a homomorphism `λ : k^× → (ℝ, +)`.  Composing it with the
determinant character `δ_V(w) = det ρ_V(w)` of a representation and normalising by the
dimension produces the *determinant weight* `dw_λ(V) = λ(δ_V(γ)) / dim V`, a real number
attached to any representation of a degree datum whose determinant is finite on the degree-zero
subgroup `P = ker deg`.  The weight does not depend on the choice of the degree-one element `γ`.

The propositions here are the arithmetic that the weight bookkeeping of the Weil conjectures
runs on.  The *readout* says that a positive central pair `(N, z)` computes the determinant
weight of a subquotient on which `z` acts by a scalar `c_Q`: `dw_λ(Q) = λ(c_Q) / N`.  The
*tensor* and *exterior* propositions say that the determinant weights of the simple constituents
of `V ⊗ E` and of `⋀^s V` are, respectively, sums `dw_λ(V_i) + dw_λ(E_j)` and `s`-fold subsums of
the rank-counted weight list of `V`.  None of the three needs `V` or `E` to be semisimple.

Subrepresentations are Mathlib's `Subrepresentation`, so a subquotient is
`Subrepresentation.subquotient S U` for `U < S`, and semisimplicity is the class
`Representation.IsSemisimpleRepresentation`.

The readout is stated for a subquotient of the defining representation of the datum.  A general
rational representation `r` of the arithmetic monodromy group `G` is meant to reduce to this
case, because `r(G)` is again a matrix group, hence the defining representation of another
represented degree datum; that reduction needs a transport of the positive central pair `(N, z)`
along `r`, which is not stated here.

The last section reads the weight of a rank-one character off a single element of positive
degree.

## Main declarations

* `Representation.RealCharacter`: a homomorphism `k^× → (ℝ, +)`.
* `Representation.HasFiniteGeometricDet`, `Representation.detWeight`: the finiteness of the
  determinant character on `P`, and the determinant weight `dw_λ`.
* `Representation.detWeight_mul_of_mem_ker`: the determinant weight does not depend on the choice
  of the degree-one element.
* `Representation.weightMultiset`: the rank-counted weight multiset of a decomposition.
* `Representation.toAdd_apply_detCharacter_eq_zero`: a real character kills the determinant of
  a degree-zero element when the geometric determinant is finite.
* `RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair`: the weight readout from a
  positive central pair, and
  `RepresentedDegreeDatum.exists_detWeight_eq_of_isPositiveCentralPair_of_isIrreducible`: its
  version for an irreducible subquotient, where `z` acts as a scalar by Schur's lemma.
* `DegreeDatum.norm_apply_eq_zpow`: a rank-one character with finite geometric image has constant
  modulus `|ι(χ(γ))| ^ m` on the elements of degree `m`.
* `DegreeDatum.forall_norm_eq_rpow_iff_exists`, `DegreeDatum.forall_norm_eq_rpow_iff_forall`: the
  weight of such a character is read off from one element of positive degree.
* `Representation.exists_detWeight_eq_add_of_subquotient_tprod`: the weights of the constituents
  of a tensor product, over an algebraically closed field of characteristic zero, and its converse
  `Representation.exists_isIrreducible_subquotient_tprod_detWeight_eq_add`.
* `Representation.detWeight_subquotient_tprod_eq_add`: the weights of the subquotients of the
  tensor product of two irreducible representations, and
  `DegreeDatum.detWeight_subquotient_tprod_eq_add`: the same for a degree datum, where the proof
  happens.
* `Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: the weights of the
  constituents of an exterior power, over an algebraically closed field of characteristic zero.
* `DegreeDatum.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: the same for a degree
  datum, where the proof happens.
* `Representation.exists_detWeight_eq_sum_of_exteriorPower` (and its degree-datum version): the
  converse, every admissible sum of weights occurs.
* `Representation.CompositionSeries.weightMultiset`: the rank-counted constituent weights of a
  composition series.
* `Representation.CompositionSeries.exteriorPower_detWeight`: the weights of the constituents of
  `⋀^r V` for a not necessarily semisimple `V`, and their converse.
* `RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair_of_basis`: the readout for any
  representation whose matrices in a basis are those of the datum, and
  `RepresentedDegreeDatum.exists_detWeight_eq_of_isPositiveCentralPair_of_surjective`: the readout
  for an irreducible quotient of such a representation.

## Implementation details

The exterior statement is first proved for a semisimple `V` and then transferred along a
composition series to the semisimplification, whose exterior powers have the same constituents.

The readout is proved by taking determinants in `z = h Fᴺ`, with `h` in the geometric monodromy
group `H`.  The determinant of the action on `Q` is a polynomial function on the stabilizer of
`U ≤ S` (`Matrix.GeneralLinearGroup.exists_evalAlgHom_eq_det_of_mk_eq`), so its finitely many
values on `ρ(P)` are also its values on the closure `H`
(`Matrix.GeneralLinearGroup.evalAlgHom_mem_of_mem_zeroLocus_vanishingIdeal`).  The character
then kills the finite-order factor contributed by `h`.
-/

@[expose] public section

open scoped Matrix Kronecker TensorProduct

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- A *real character* of the field `k` is a group homomorphism `λ: kˣ → (ℝ, +)` from the units
of `k` to the reals under addition, `λ(ab) = λ(a) + λ(b)`. The weights of this file are read off
through such a character, from the determinants of representations (`detWeight`); for
`k = ℚ̄_ℓ` the relevant one is `log |ι(·)|` for a field embedding `ι: k → ℂ`. -/
abbrev RealCharacter (k : Type*) [Field k] := kˣ →* Multiplicative ℝ

/-- A representation has *finite geometric determinant* for a degree homomorphism `deg` when its
determinant character takes only finitely many values on the degree-zero subgroup `P = ker deg`. -/
def HasFiniteGeometricDet (deg : W →* Multiplicative ℤ) (ρ : Representation k W V) : Prop :=
  (Set.range fun w : deg.ker ↦ ρ.detCharacter w).Finite

/-- The *determinant weight* of a representation with respect to a real character `χ` and
a degree-one element `γ` is `dw_χ(ρ) = χ(δ(γ)) / dim V`.

For `V = 0` the division by `dim V = 0` makes it the junk value `0`; the same happens when `V`
is infinite-dimensional, as `Module.finrank` is then `0`. -/
noncomputable def detWeight (χ : RealCharacter k) (γ : W) (ρ : Representation k W V) : ℝ :=
  Multiplicative.toAdd (χ (ρ.detCharacter γ)) / Module.finrank k V

/-- A real character kills the determinant of a degree-zero element when the geometric
determinant is finite: `δ(u)` has finite order `e`, so `e λ(δ(u)) = λ(δ(u) ^ e) = 0` in the
torsion-free group `ℝ`. -/
theorem toAdd_apply_detCharacter_eq_zero {deg : W →* Multiplicative ℤ}
    (ρ : Representation k W V) (hdet : ρ.HasFiniteGeometricDet deg) (χ : RealCharacter k)
    {u : W} (hu : u ∈ deg.ker) : Multiplicative.toAdd (χ (ρ.detCharacter u)) = 0 := by
  let φ := ρ.detCharacter.comp deg.ker.subtype
  have : Finite φ.range := (hdet : (Set.range φ).Finite).to_subtype
  have hfin : IsOfFinOrder (χ (ρ.detCharacter u)) :=
    (χ.comp φ.range.subtype).isOfFinOrder (isOfFinOrder_of_finite ⟨φ ⟨u, hu⟩, ⟨u, hu⟩, rfl⟩)
  obtain ⟨m, hm, hum⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h := congr(Multiplicative.toAdd $hum)
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left (Nat.cast_ne_zero.2 hm.ne')

/-- The determinant weight does not depend on the chosen degree-one element: replacing `γ` by
`u γ` for a degree-zero element `u` leaves it unchanged, because the determinant character takes
finitely many values on the degree-zero subgroup and `ℝ` is torsion-free. -/
theorem detWeight_mul_of_mem_ker {deg : W →* Multiplicative ℤ} (ρ : Representation k W V)
    (hdet : ρ.HasFiniteGeometricDet deg) (χ : RealCharacter k) (γ : W) {u : W}
    (hu : u ∈ deg.ker) : ρ.detWeight χ (u * γ) = ρ.detWeight χ γ := by
  rw [detWeight, detWeight, map_mul, map_mul, toAdd_mul,
    ρ.toAdd_apply_detCharacter_eq_zero hdet χ hu, zero_add]

/-- The rank-counted weight multiset of a family of subrepresentations: the determinant weight of
`Vs j` occurs `dim Vs j` times. -/
noncomputable def weightMultiset {ι : Type*} [Fintype ι] {ρ : Representation k W V}
    (χ : RealCharacter k) (γ : W) (Vs : ι → Subrepresentation ρ) : Multiset ℝ :=
  ∑ j : ι, Multiset.replicate (Module.finrank k (Vs j).toSubmodule)
    ((Vs j).toRepresentation.detWeight χ γ)

/-- Finiteness of the geometric determinant only depends on the degree-zero subgroup. -/
theorem hasFiniteGeometricDet_congr {deg deg' : W →* Multiplicative ℤ} (h : deg.ker = deg'.ker)
    (ρ : Representation k W V) : ρ.HasFiniteGeometricDet deg ↔ ρ.HasFiniteGeometricDet deg' := by
  unfold HasFiniteGeometricDet
  rw [h]

/-- Finiteness of the geometric determinant only depends on the determinant character. -/
theorem hasFiniteGeometricDet_iff_of_detCharacter_eq {V' : Type*} [AddCommGroup V'] [Module k V']
    {deg : W →* Multiplicative ℤ} {ρ : Representation k W V} {σ : Representation k W V'}
    (h : σ.detCharacter = ρ.detCharacter) :
    σ.HasFiniteGeometricDet deg ↔ ρ.HasFiniteGeometricDet deg := by
  unfold HasFiniteGeometricDet
  rw [h]

/-- The determinant weight only depends on the determinant character and the dimension. -/
theorem detWeight_eq_of_detCharacter_eq {V' : Type*} [AddCommGroup V'] [Module k V']
    {ρ : Representation k W V} {σ : Representation k W V'} (h : σ.detCharacter = ρ.detCharacter)
    (hd : Module.finrank k V' = Module.finrank k V) (χ : RealCharacter k) (γ : W) :
    σ.detWeight χ γ = ρ.detWeight χ γ := by
  unfold detWeight
  rw [h, hd]

/-- Equivalent representations have the same determinant weight. -/
theorem Equiv.detWeight_eq {V' : Type*} [AddCommGroup V'] [Module k V']
    {ρ : Representation k W V} {σ : Representation k W V'} (e : ρ.Equiv σ) (χ : RealCharacter k)
    (γ : W) : σ.detWeight χ γ = ρ.detWeight χ γ :=
  detWeight_eq_of_detCharacter_eq e.detCharacter_eq e.finrank_eq χ γ

/-- Equivalent representations both have, or both do not have, finite geometric determinant. -/
theorem Equiv.hasFiniteGeometricDet_iff {V' : Type*} [AddCommGroup V'] [Module k V']
    {deg : W →* Multiplicative ℤ} {ρ : Representation k W V} {σ : Representation k W V'}
    (e : ρ.Equiv σ) : σ.HasFiniteGeometricDet deg ↔ ρ.HasFiniteGeometricDet deg :=
  hasFiniteGeometricDet_iff_of_detCharacter_eq e.detCharacter_eq

/-- The determinant weight is homogeneous in the chosen element: `dw(γ ^ m) = m dw(γ)`. -/
theorem detWeight_zpow (ρ : Representation k W V) (χ : RealCharacter k) (γ : W) (m : ℤ) :
    ρ.detWeight χ (γ ^ m) = m * ρ.detWeight χ γ := by
  unfold detWeight
  rw [map_zpow, map_zpow, toAdd_zpow, zsmul_eq_mul, mul_div_assoc]

/-- The determinant weight at `u γ ^ m`, for `u` of degree zero, is `m` times that at `γ`. -/
theorem detWeight_mul_zpow_of_mem_ker {deg : W →* Multiplicative ℤ} (ρ : Representation k W V)
    (hdet : ρ.HasFiniteGeometricDet deg) (χ : RealCharacter k) (γ : W) {u : W}
    (hu : u ∈ deg.ker) (m : ℤ) : ρ.detWeight χ (u * γ ^ m) = m * ρ.detWeight χ γ := by
  rw [ρ.detWeight_mul_of_mem_ker hdet χ _ hu, detWeight_zpow]

/-- If every element has degree zero, the determinant weight of a representation with finite
geometric determinant vanishes. -/
theorem detWeight_eq_zero_of_forall_deg_eq_one {deg : W →* Multiplicative ℤ}
    (hdeg : ∀ w, deg w = 1) (ρ : Representation k W V) (hdet : ρ.HasFiniteGeometricDet deg)
    (χ : RealCharacter k) (γ : W) : ρ.detWeight χ γ = 0 := by
  have := ρ.detWeight_mul_of_mem_ker hdet χ 1 (u := γ) (hdeg γ)
  rw [mul_one] at this
  rw [this, detWeight, map_one, map_one, toAdd_one, zero_div]

end Representation

namespace AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

open Matrix.GeneralLinearGroup

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-- Fix a real character `χ` and a positive central pair `(N, z)` for a represented degree
datum.  If a nonzero `W`-subquotient `Q = S / U` of the defining representation has finite
geometric determinant and `z` acts on `Q` as the scalar `c`, then `dw_χ(Q) = χ(c) / N`.  The
scalar hypothesis is automatic when `Q` is simple, by Schur's lemma. -/
theorem detWeight_eq_of_isPositiveCentralPair (D : RepresentedDegreeDatum W n k)
    (χ : Representation.RealCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) {U S : Subrepresentation D.asRepresentation} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D.deg) (c : kˣ)
    (hc : ∀ x ∈ S, Matrix.toLinAlgEquiv' (z : Matrix n n k) x - (c : k) • x ∈ U) :
    (S.subquotient U).detWeight χ D.degreeOneElement =
      Multiplicative.toAdd (χ c) / N := by
  classical
  obtain ⟨hN, -, h, hh, _, rfl, hzh⟩ := id hz
  set Q := S.subquotient U
  set γ := D.degreeOneElement
  obtain ⟨p, hp⟩ := exists_evalAlgHom_eq_det_of_mk_eq S.toSubmodule U.toSubmodule
  -- `p` computes the determinant character of `Q` on `ρ(W)`
  have hrep (w : W) : evalAlgHom (D.rep w) p = Q.detCharacter w := by
    rw [Representation.coe_detCharacter_apply]
    exact hp _ _ fun x ↦ ⟨_, rfl, rfl⟩
  -- the induced action of `h ∈ H(k)` on `Q`
  have hG := D.zeroLocus_geometricMonodromy_le_zeroLocus_arithmeticMonodromy k hh
  let fh : Module.End k (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) :=
    Submodule.mapQ _ _ (((h : Matrix n n k).mulVecLin).restrict
      fun x hx ↦ D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hG S hx)
      fun x hx ↦ D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hG U hx
  -- by density, `det fh` is a value of the determinant character on `P`
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ : evalAlgHom h p ∈
      Units.val '' Set.range fun u : D.deg.ker ↦ Q.detCharacter u :=
    evalAlgHom_mem_of_mem_zeroLocus_vanishingIdeal (Γ := D.degreeZero.map D.rep) p
      (hdet.image Units.val)
      (by rintro _ ⟨w, hw, rfl⟩; exact ⟨_, ⟨⟨w, hw⟩, rfl⟩, (hrep w).symm⟩) hh
  have hfh : evalAlgHom h p = LinearMap.det fh := hp _ _ fun x ↦ ⟨_, rfl, rfl⟩
  have hzG := hz.mem_zeroLocus_arithmeticMonodromy
  -- two descriptions of the action of `z = h Fᴺ` on `Q`
  have h₁ : evalAlgHom z p = (c : k) ^ Module.finrank k
      (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) := by
    rw [hp _ ((c : k) • LinearMap.id) fun x ↦ ⟨⟨_, D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy
      hzG S x.2⟩, rfl, ?_⟩, LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul, eq_comm,
      Submodule.Quotient.eq]
    exact hc x x.2
  have h₂ : evalAlgHom z p = LinearMap.det fh * Q.detCharacter (γ ^ N) := by
    rw [Representation.coe_detCharacter_apply, ← map_mul]
    refine hp _ _ fun x ↦ ⟨_, ?_, rfl⟩
    rw [← hzh, Units.val_mul, ← Matrix.mulVec_mulVec]
    simp only [frobenius, γ, ← map_pow]
    rfl
  have hunit : c ^ Module.finrank k (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) =
      Q.detCharacter (u * γ ^ N) := Units.ext <| by
    rw [Units.val_pow_eq_pow_val, map_mul, Units.val_mul, ← h₁, h₂, ← hfh, ← hu]
  have h₃ := congr(Multiplicative.toAdd (χ $hunit))
  rw [map_pow, toAdd_pow, map_mul, map_mul, toAdd_mul,
    Q.toAdd_apply_detCharacter_eq_zero hdet χ u.2, zero_add, map_pow, map_pow, toAdd_pow,
    nsmul_eq_mul, nsmul_eq_mul] at h₃
  obtain ⟨x, hxS, hxU⟩ := IsConcreteLE.exists_of_lt hUS
  have : Nontrivial (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype) :=
    ⟨Submodule.Quotient.mk ⟨x, hxS⟩, 0, by rwa [Ne, Submodule.Quotient.mk_eq_zero]⟩
  have hr := Module.finrank_pos (R := k)
    (M := S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype)
  rw [Representation.detWeight, div_eq_div_iff (by positivity) (by positivity)]
  linarith

/-- The weight readout for an irreducible subquotient, over an algebraically closed field: by
Schur's lemma the central element `z` acts on a nonzero irreducible subquotient `Q = S / U` as a
scalar `c`, nonzero because `z` is invertible, and then `dw_χ(Q) = χ(c) / N`. -/
theorem exists_detWeight_eq_of_isPositiveCentralPair_of_isIrreducible [IsAlgClosed k]
    (D : RepresentedDegreeDatum W n k) (χ : Representation.RealCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) {U S : Subrepresentation D.asRepresentation} (hUS : U < S)
    (hirr : (S.subquotient U).IsIrreducible)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D.deg) :
    ∃ c : kˣ, (∀ x ∈ S, Matrix.toLinAlgEquiv' (z : Matrix n n k) x - (c : k) • x ∈ U) ∧
      (S.subquotient U).detWeight χ D.degreeOneElement = Multiplicative.toAdd (χ c) / N := by
  have hzG := hz.mem_zeroLocus_arithmeticMonodromy
  obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hirr
    (Matrix.toLinAlgEquiv' (z : Matrix n n k))
    (fun w x ↦ by
      simp only [asRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, hz.commute w])
    (fun x hx ↦ D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG U hx)
    (fun x hx ↦ D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hzG S hx)
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hxS, hxU⟩ := IsConcreteLE.exists_of_lt hUS
    refine hxU ?_
    have := D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy (inv_mem hzG) U
      (by simpa using hc x hxS)
    simpa [Matrix.mulVec_mulVec] using this
  exact ⟨Units.mk0 c hc0, hc, D.detWeight_eq_of_isPositiveCentralPair χ hz hUS hdet _ hc⟩

section Basis

open Module Matrix.GeneralLinearGroup

variable {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k W V}

/-- A representation `ρ` whose matrices in a basis `b` are those of the datum is equivalent, via
the coordinates `b.equivFun`, to the defining representation of the datum. -/
noncomputable def basisEquiv (D : RepresentedDegreeDatum W n k) (b : Basis n k V)
    (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k)) :
    ρ.Equiv D.asRepresentation :=
  .mk b.equivFun fun w ↦ LinearMap.ext fun x ↦ by
    simp [asRepresentation, ← hρ, LinearMap.toMatrix_mulVec_repr]

/-- The `k`-points of the arithmetic monodromy group preserve every subrepresentation of a
representation `ρ` whose matrices in a basis `b` are those of the datum. -/
theorem toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy (D : RepresentedDegreeDatum W n k)
    (b : Basis n k V) (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k))
    {g : GL n k}
    (hg : g ∈ zeroLocus D.arithmeticMonodromy k) (S : Subrepresentation ρ) {x : V}
    (hx : x ∈ S) : Matrix.toLin b b (g : Matrix n n k) x ∈ S := by
  let e := D.basisEquiv b hρ
  rw [Matrix.toLin_apply_eq_equivFun_symm]
  exact (Subrepresentation.mem_orderIsoMapComap_iff e S).1
    (D.mulVec_mem_of_mem_zeroLocus_arithmeticMonodromy hg _
      (Subrepresentation.apply_mem_orderIsoMapComap e S hx))

/-- The weight readout `dw_χ(Q) = χ(c) / N` for a subquotient `Q = S / U` of any representation
`ρ` whose matrices in a basis `b` are those of the datum. -/
theorem detWeight_eq_of_isPositiveCentralPair_of_basis (D : RepresentedDegreeDatum W n k)
    (χ : Representation.RealCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) (b : Basis n k V)
    (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k))
    {U S : Subrepresentation ρ} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D.deg) (c : kˣ)
    (hc : ∀ x ∈ S, Matrix.toLin b b (z : Matrix n n k) x - (c : k) • x ∈ U) :
    (S.subquotient U).detWeight χ D.degreeOneElement =
      Multiplicative.toAdd (χ c) / N := by
  let e := D.basisEquiv b hρ
  let O := Subrepresentation.orderIsoMapComap e
  have hchar := Subrepresentation.detCharacter_subquotient_orderIsoMapComap e S U
  have hdim := (Subrepresentation.subquotientEquiv e S U).toLinearEquiv.finrank_eq
  rw [← Representation.detWeight_eq_of_detCharacter_eq hchar hdim.symm]
  refine D.detWeight_eq_of_isPositiveCentralPair χ hz (O.lt_iff_lt.2 hUS)
    ((Representation.hasFiniteGeometricDet_iff_of_detCharacter_eq hchar).2 hdet) c
    fun y hy ↦ (Subrepresentation.mem_orderIsoMapComap_iff e U).2 ?_
  have := hc _ ((Subrepresentation.mem_orderIsoMapComap_iff e S).1 hy)
  change b.equivFun.symm (_ *ᵥ b.equivFun (b.equivFun.symm y)) - (c : k) • b.equivFun.symm y ∈ U
    at this
  change b.equivFun.symm _ ∈ U
  rw [LinearEquiv.apply_symm_apply] at this
  rw [map_sub, map_smul]
  exact this

/-- The weight readout for an irreducible quotient `r₁` of a representation `ρ` whose matrices in a
basis `b` are those of the datum, over an algebraically closed field: by Schur's lemma the central
element `z` acts on `r₁` by a nonzero scalar `c`, and then `dw_χ(r₁) = χ(c) / N`. -/
theorem exists_detWeight_eq_of_isPositiveCentralPair_of_surjective [IsAlgClosed k]
    [FiniteDimensional k V] (D : RepresentedDegreeDatum W n k)
    (χ : Representation.RealCharacter k) {N : ℕ} {z : GL n k}
    (hz : D.IsPositiveCentralPair N z) (b : Basis n k V)
    (hρ : ∀ w, LinearMap.toMatrix b b (ρ w) = (D.rep w : Matrix n n k))
    {V₁ : Type*} [AddCommGroup V₁] [Module k V₁] {r₁ : Representation k W V₁}
    (hr₁ : r₁.IsIrreducible) (hdet₁ : r₁.HasFiniteGeometricDet D.deg)
    (f : ρ.IntertwiningMap r₁) (hf : Function.Surjective f) :
    ∃ c : kˣ, (∀ x, f (Matrix.toLin b b (z : Matrix n n k) x) = (c : k) • f x) ∧
      r₁.detWeight χ D.degreeOneElement = Multiplicative.toAdd (χ c) / N := by
  let Z : V →ₗ[k] V := Matrix.toLin b b (z : Matrix n n k)
  have hZcomm (w : W) : Z ∘ₗ ρ w = ρ w ∘ₗ Z := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hρ,
      LinearMap.toMatrix_toLin, ← Units.val_mul, ← Units.val_mul, hz.commute w]
  have hZmem (T : Subrepresentation ρ) {x : V} (hx : x ∈ T) : Z x ∈ T :=
    D.toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy b hρ
      hz.mem_zeroLocus_arithmeticMonodromy T hx
  have hZsurj : Function.Surjective Z := by
    have : IsUnit Z := z.isUnit.map (Matrix.toLinAlgEquiv b)
    exact ((Module.End.isUnit_iff Z).1 this).2
  -- `r₁` is the subquotient `ρ / ker f`
  let e : ((⊤ : Subrepresentation ρ).subquotient f.ker).Equiv r₁ :=
    (Subrepresentation.subquotientEquivOfIntertwiningMap f (U' := ⊥) (S' := ⊤)
      (fun _ _ ↦ Submodule.mem_top) (fun _ _ hx ↦ (Submodule.mem_bot k).2 hx)
      (fun _ _ hx ↦ (Submodule.mem_bot k).1 hx) fun y _ ↦ by
        obtain ⟨x, rfl⟩ := hf y
        exact ⟨x, Submodule.mem_top, (Submodule.mem_bot k).2 (sub_self _)⟩).trans
      (Subrepresentation.topSubquotientBotEquiv r₁)
  obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible
    (e.isIrreducible_iff.2 hr₁) Z (fun w x ↦ LinearMap.congr_fun (hZcomm w) x)
    (fun _ hx ↦ hZmem _ hx) (fun _ hx ↦ hZmem _ hx)
  have hc' (x : V) : f (Z x) = c • f x := by
    have := hc x Submodule.mem_top
    rwa [Representation.IntertwiningMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  have := hr₁.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
  obtain ⟨x₀, rfl⟩ := hf v
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, rfl⟩ := hZsurj x₀
    exact hv (by rw [hc', zero_smul])
  have hUS : f.ker < ⊤ := lt_top_iff_ne_top.2 fun h ↦ hv <|
    (Representation.IntertwiningMap.mem_ker _ _ _ _).1 (h ▸ Submodule.mem_top)
  refine ⟨Units.mk0 c hc0, hc', ?_⟩
  rw [e.detWeight_eq]
  exact D.detWeight_eq_of_isPositiveCentralPair_of_basis χ hz b hρ hUS
    ((e.hasFiniteGeometricDet_iff).1 hdet₁) _ fun x _ ↦ by
      rw [Units.val_mk0]
      exact hc x Submodule.mem_top

end Basis

end AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]

/-- The rank-counted list of a family of values: `∑ⱼ replicate (d j) (f j)` is the multiset of the
values of `f` along the first projection of `Σ j, Fin (d j)`. -/
private theorem sum_replicate_eq_map_univ_sigma {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (f : ι → ℝ) :
    ∑ j, Multiset.replicate (d j) (f j) =
      (Finset.univ : Finset (Σ j, Fin (d j))).val.map fun a ↦ f a.1 := by
  have h : (Finset.univ : Finset (Σ j, Fin (d j))).val.map (fun a ↦ f a.1) =
      ∑ a : Σ j, Fin (d j), ({f a.1} : Multiset ℝ) := by
    rw [Finset.sum_eq_multiset_sum]
    conv_lhs => rw [← Multiset.sum_map_singleton
      (Multiset.map (fun a : Σ j, Fin (d j) ↦ f a.1) Finset.univ.val)]
    rw [Multiset.map_map]
    rfl
  rw [h, Fintype.sum_sigma]
  simp [Multiset.nsmul_singleton]

end Representation

namespace AlgebraicGeometry.Monodromy

open Module Matrix.GeneralLinearGroup Representation

universe u

/-- The exterior-power weight theorem for a degree datum `D₀`, that is, for a surjective degree
map and a chosen element of degree one: for `V = ⊕ Vs j` with simple summands, every simple
subquotient `Q` of `⋀^s V` has weight `dw(Q) = T.sum` for a sub-multiset `T` of size `s` of the
rank-counted weight multiset of `V`. -/
theorem DegreeDatum.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {W : Type*} [Group W] (D₀ : DegreeDatum W)
    (χ : RealCharacter k)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rV : Representation k W V) (s : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Subrepresentation rV)
    (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet D₀.deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule)
    {U S : Subrepresentation (rV.exteriorPower s)} (hUS : U < S)
    (hsimple : IsIrreducible (S.subquotient U))
    (hdet : (S.subquotient U).HasFiniteGeometricDet D₀.deg) :
    ∃ T : Multiset ℝ, T ≤ weightMultiset χ D₀.degreeOneElement Vs ∧ Multiset.card T = s ∧
      (S.subquotient U).detWeight χ D₀.degreeOneElement = T.sum := by
  classical
  -- A basis of `V` adapted to the decomposition, indexed by `ULift (Fin r)`: the positive central
  -- pair is constructed for index types in the universe of `k`.
  let d : ι → ℕ := fun j ↦ finrank k (Vs j).toSubmodule
  let bσ : Basis (Σ j, Fin (d j)) k V :=
    hdirect.collectedBasis fun j ↦ Module.finBasis k (Vs j).toSubmodule
  let eσ : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) ≃ Σ j, Fin (d j) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  -- The exterior power of `GL` uses the decidable equality of the linear order.
  let : DecidableEq (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) :=
    fun a b ↦ LinearOrder.toDecidableEq a b
  let b : Basis (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k V := bσ.reindex eσ.symm
  let idx : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) → ι := fun i ↦ (eσ i).1
  have hb_mem (i) : b i ∈ (Vs (idx i)).toSubmodule := by
    rw [Basis.reindex_apply]
    exact hdirect.collectedBasis_mem _ _
  -- The represented degree datum of `V` in the basis `b`, and a positive central pair.
  let D : RepresentedDegreeDatum W (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k :=
    { D₀ with rep := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp rV.toHomUnits }
  have hρ (w : W) : LinearMap.toMatrix b b (rV w) = (D.rep w : Matrix _ _ k) := by
    ext i i'
    rw [LinearMap.toMatrix_apply]
    exact (LinearMap.toMatrixAlgEquiv_apply b (rV w) i i').symm
  have hss : D.IsSemisimple :=
    (Subrepresentation.orderIsoMapComap (D.basisEquiv b hρ)).complementedLattice_iff.1
      (isSemisimpleRepresentation_of_isInternal Vs hsimpleVs hdirect)
  obtain ⟨N, z, hz⟩ := D.exists_isPositiveCentralPair hss
  -- The central element `Z` acting on `V`.
  let Z : V →ₗ[k] V := Matrix.toLin b b (z : Matrix _ _ k)
  have hZcomm (w : W) : Z ∘ₗ rV w = rV w ∘ₗ Z := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hρ,
      LinearMap.toMatrix_toLin, ← Units.val_mul, ← Units.val_mul, hz.commute w]
  have hZmem (T : Subrepresentation rV) {x : V} (hx : x ∈ T) : Z x ∈ T :=
    D.toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy b hρ
      hz.mem_zeroLocus_arithmeticMonodromy T hx
  -- `Z` acts on each `Vs j` by a nonzero scalar `cs j`, and `dw(Vs j) = χ(cs j) / N`.
  have hscalar (j : ι) : ∃ c : kˣ, (∀ x ∈ (Vs j).toSubmodule, Z x = (c : k) • x) ∧
      (Vs j).toRepresentation.detWeight χ D₀.degreeOneElement =
        Multiplicative.toAdd (χ c) / N := by
    have hirr : IsIrreducible ((Vs j).subquotient ⊥) :=
      (Subrepresentation.orderIsoMapComap
        (Subrepresentation.subquotientBotEquiv (Vs j))).isSimpleOrder_iff.2 (hsimpleVs j)
    obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hirr Z
      (fun w x ↦ LinearMap.congr_fun (hZcomm w) x) (fun x hx ↦ hZmem ⊥ hx) (fun x hx ↦ hZmem _ hx)
    have hc' (x) (hx : x ∈ (Vs j).toSubmodule) : Z x = c • x :=
      sub_eq_zero.1 ((Submodule.mem_bot k).1 (hc x hx))
    have hbot : ⊥ < Vs j := (Subrepresentation.isAtom_of_isIrreducible (hsimpleVs j)).bot_lt
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨x, hx, hx0⟩ := IsConcreteLE.exists_of_lt hbot
      refine hx0 ((Submodule.mem_bot k).2 ?_)
      have h0 : Z x = 0 := by rw [hc' x hx, zero_smul]
      rw [Matrix.toLin_apply_eq_equivFun_symm, LinearEquiv.map_eq_zero_iff] at h0
      have := congrArg (fun y ↦ (z⁻¹).val *ᵥ y) h0
      simpa [Matrix.mulVec_mulVec] using this
    have hchar := Subrepresentation.detCharacter_subquotient_bot (Vs j)
    refine ⟨Units.mk0 c hc0, hc', ?_⟩
    rw [← detWeight_eq_of_detCharacter_eq hchar
      (Subrepresentation.subquotientBotEquiv (Vs j)).toLinearEquiv.finrank_eq]
    exact D.detWeight_eq_of_isPositiveCentralPair_of_basis χ hz b hρ hbot
      ((hasFiniteGeometricDet_iff_of_detCharacter_eq hchar).2 (hdetVs j)) _
      fun x hx ↦ by
        rw [Units.val_mk0, show Matrix.toLin b b (z : Matrix _ _ k) x = Z x from rfl, hc' x hx,
          sub_self]
        exact Submodule.zero_mem _
  choose cs hcs hdw using hscalar
  have hZb (i) : Z (b i) = ((cs (idx i) : kˣ) : k) • b i := hcs _ _ (hb_mem i)
  -- The exterior power: its datum, the transported central pair, and `⋀^s Z`.
  let B := b.exteriorPower s
  let r : GL (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k →* GL _ k :=
    Matrix.GeneralLinearGroup.exteriorPower s
  obtain ⟨φ, hφ⟩ := exists_algHom_comp_eq_evalAlgHom_exteriorPower (k := k)
    (n := ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) s
  have hz' := hz.map r φ hφ
  have hρ' (w : W) : LinearMap.toMatrix B B (rV.exteriorPower s w) =
      ((D.map r).rep w : Matrix _ _ k) := by
    change LinearMap.toMatrix B B (exteriorPower.map s (rV w)) = _
    rw [LinearMap.toMatrix_exteriorPower_map, hρ]
    rfl
  have hZ' : exteriorPower.map s Z = Matrix.toLin B B (r z : Matrix _ _ k) := by
    apply (LinearMap.toMatrix B B).injective
    rw [LinearMap.toMatrix_exteriorPower_map, LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin]
    rfl
  have hZ'mem (T : Subrepresentation (rV.exteriorPower s)) {x} (hx : x ∈ T) :
      exteriorPower.map s Z x ∈ T := by
    rw [hZ']
    exact (D.map r).toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy B hρ'
      hz'.mem_zeroLocus_arithmeticMonodromy T hx
  -- Schur's lemma on `Q = S / U`, and the eigenvalue of `⋀^s Z`.
  obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hsimple
    (exteriorPower.map s Z) (fun w x ↦ by
      change exteriorPower.map s Z (exteriorPower.map s (rV w) x) =
        exteriorPower.map s (rV w) (exteriorPower.map s Z x)
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hZcomm, exteriorPower.map_comp,
        LinearMap.comp_apply])
    (fun x hx ↦ hZ'mem U hx) (fun x hx ↦ hZ'mem S hx)
  have hev : Module.End.HasEigenvalue (exteriorPower.map s Z) c :=
    Module.End.hasEigenvalue_of_subquotient _ hUS (fun x hx ↦ hZ'mem U hx)
      (fun x hx ↦ hZ'mem S hx) c hc
  obtain ⟨I, hI⟩ := exteriorPower.exists_eq_prod_of_hasEigenvalue_map b hZb hev
  -- The weight readout on `Q`.
  have hQ := (D.map r).detWeight_eq_of_isPositiveCentralPair_of_basis χ hz' B hρ' hUS hdet
    (∏ i ∈ I.1, cs (idx i)) fun x hx ↦ by
      rw [← hZ', Units.coe_prod, ← hI]
      exact hc x hx
  refine ⟨I.1.val.map fun i ↦
    (Vs (idx i)).toRepresentation.detWeight χ D₀.degreeOneElement, ?_, ?_, ?_⟩
  · rw [weightMultiset, sum_replicate_eq_map_univ_sigma]
    calc _ ≤ (Finset.univ : Finset (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))))).val.map
          fun i ↦ (Vs (idx i)).toRepresentation.detWeight χ D₀.degreeOneElement :=
          Multiset.map_le_map (Finset.val_le_iff.2 (Finset.subset_univ _))
      _ = _ := by
        rw [← Finset.map_univ_equiv eσ, Finset.map_val, Multiset.map_map]
        rfl
  · simp
  · rw [← Finset.sum_eq_multiset_sum]
    refine hQ.trans ?_
    simp only [hdw, map_prod, toAdd_prod, Finset.sum_div]

/-- The converse of `DegreeDatum.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: if all
simple constituents of `⋀^s V` have finite geometric determinant, every sub-multiset `T` of size
`s` of the rank-counted weight multiset is the weight `dw(Q) = T.sum` of some simple constituent
`Q` of `⋀^s V`. -/
theorem DegreeDatum.exists_detWeight_eq_sum_of_exteriorPower
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {W : Type*} [Group W] (D₀ : DegreeDatum W)
    (χ : RealCharacter k)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rV : Representation k W V) (s : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Subrepresentation rV)
    (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet D₀.deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule)
    (hdet : ∀ U S : Subrepresentation (rV.exteriorPower s), IsIrreducible (S.subquotient U) →
      (S.subquotient U).HasFiniteGeometricDet D₀.deg)
    {T : Multiset ℝ} (hT : T ≤ weightMultiset χ D₀.degreeOneElement Vs)
    (hcard : Multiset.card T = s) :
    ∃ U S : Subrepresentation (rV.exteriorPower s), U < S ∧ IsIrreducible (S.subquotient U) ∧
      (S.subquotient U).detWeight χ D₀.degreeOneElement = T.sum := by
  classical
  -- The same setup as for `exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`.
  let d : ι → ℕ := fun j ↦ finrank k (Vs j).toSubmodule
  let bσ : Basis (Σ j, Fin (d j)) k V :=
    hdirect.collectedBasis fun j ↦ Module.finBasis k (Vs j).toSubmodule
  let eσ : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) ≃ Σ j, Fin (d j) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  let : DecidableEq (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) :=
    fun a b ↦ LinearOrder.toDecidableEq a b
  let b : Basis (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k V := bσ.reindex eσ.symm
  let idx : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) → ι := fun i ↦ (eσ i).1
  have hb_mem (i) : b i ∈ (Vs (idx i)).toSubmodule := by
    rw [Basis.reindex_apply]
    exact hdirect.collectedBasis_mem _ _
  let D : RepresentedDegreeDatum W (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k :=
    { D₀ with rep := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp rV.toHomUnits }
  have hρ (w : W) : LinearMap.toMatrix b b (rV w) = (D.rep w : Matrix _ _ k) := by
    ext i i'
    rw [LinearMap.toMatrix_apply]
    exact (LinearMap.toMatrixAlgEquiv_apply b (rV w) i i').symm
  have hss : D.IsSemisimple :=
    (Subrepresentation.orderIsoMapComap (D.basisEquiv b hρ)).complementedLattice_iff.1
      (isSemisimpleRepresentation_of_isInternal Vs hsimpleVs hdirect)
  obtain ⟨N, z, hz⟩ := D.exists_isPositiveCentralPair hss
  let Z : V →ₗ[k] V := Matrix.toLin b b (z : Matrix _ _ k)
  have hZcomm (w : W) : Z ∘ₗ rV w = rV w ∘ₗ Z := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hρ,
      LinearMap.toMatrix_toLin, ← Units.val_mul, ← Units.val_mul, hz.commute w]
  have hZmem (T : Subrepresentation rV) {x : V} (hx : x ∈ T) : Z x ∈ T :=
    D.toLin_apply_mem_of_mem_zeroLocus_arithmeticMonodromy b hρ
      hz.mem_zeroLocus_arithmeticMonodromy T hx
  have hscalar (j : ι) : ∃ c : kˣ, (∀ x ∈ (Vs j).toSubmodule, Z x = (c : k) • x) ∧
      (Vs j).toRepresentation.detWeight χ D₀.degreeOneElement =
        Multiplicative.toAdd (χ c) / N := by
    have hirr : IsIrreducible ((Vs j).subquotient ⊥) :=
      (Subrepresentation.orderIsoMapComap
        (Subrepresentation.subquotientBotEquiv (Vs j))).isSimpleOrder_iff.2 (hsimpleVs j)
    obtain ⟨c, hc⟩ := Subrepresentation.exists_apply_sub_smul_mem_of_isIrreducible hirr Z
      (fun w x ↦ LinearMap.congr_fun (hZcomm w) x) (fun x hx ↦ hZmem ⊥ hx) (fun x hx ↦ hZmem _ hx)
    have hc' (x) (hx : x ∈ (Vs j).toSubmodule) : Z x = c • x :=
      sub_eq_zero.1 ((Submodule.mem_bot k).1 (hc x hx))
    have hbot : ⊥ < Vs j := (Subrepresentation.isAtom_of_isIrreducible (hsimpleVs j)).bot_lt
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨x, hx, hx0⟩ := IsConcreteLE.exists_of_lt hbot
      refine hx0 ((Submodule.mem_bot k).2 ?_)
      have h0 : Z x = 0 := by rw [hc' x hx, zero_smul]
      rw [Matrix.toLin_apply_eq_equivFun_symm, LinearEquiv.map_eq_zero_iff] at h0
      have := congrArg (fun y ↦ (z⁻¹).val *ᵥ y) h0
      simpa [Matrix.mulVec_mulVec] using this
    have hchar := Subrepresentation.detCharacter_subquotient_bot (Vs j)
    refine ⟨Units.mk0 c hc0, hc', ?_⟩
    rw [← detWeight_eq_of_detCharacter_eq hchar
      (Subrepresentation.subquotientBotEquiv (Vs j)).toLinearEquiv.finrank_eq]
    exact D.detWeight_eq_of_isPositiveCentralPair_of_basis χ hz b hρ hbot
      ((hasFiniteGeometricDet_iff_of_detCharacter_eq hchar).2 (hdetVs j)) _
      fun x hx ↦ by
        rw [Units.val_mk0, show Matrix.toLin b b (z : Matrix _ _ k) x = Z x from rfl, hc' x hx,
          sub_self]
        exact Submodule.zero_mem _
  choose cs hcs hdw using hscalar
  have hZb (i) : Z (b i) = ((cs (idx i) : kˣ) : k) • b i := hcs _ _ (hb_mem i)
  let B := b.exteriorPower s
  let r : GL (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) k →* GL _ k :=
    Matrix.GeneralLinearGroup.exteriorPower s
  obtain ⟨φ, hφ⟩ := exists_algHom_comp_eq_evalAlgHom_exteriorPower (k := k)
    (n := ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) s
  have hz' := hz.map r φ hφ
  have hρ' (w : W) : LinearMap.toMatrix B B (rV.exteriorPower s w) =
      ((D.map r).rep w : Matrix _ _ k) := by
    change LinearMap.toMatrix B B (exteriorPower.map s (rV w)) = _
    rw [LinearMap.toMatrix_exteriorPower_map, hρ]
    rfl
  have hZ' : exteriorPower.map s Z = Matrix.toLin B B (r z : Matrix _ _ k) := by
    apply (LinearMap.toMatrix B B).injective
    rw [LinearMap.toMatrix_exteriorPower_map, LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin]
    rfl
  -- `T` is the list of weights of an `s`-element set `I` of basis vectors.
  let f : ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j)))) → ℝ :=
    fun i ↦ (Vs (idx i)).toRepresentation.detWeight χ D₀.degreeOneElement
  have hW : weightMultiset χ D₀.degreeOneElement Vs = Finset.univ.val.map f := by
    rw [weightMultiset, sum_replicate_eq_map_univ_sigma, ← Finset.map_univ_equiv eσ,
      Finset.map_val, Multiset.map_map]
    rfl
  obtain ⟨u, hu, rfl⟩ := Multiset.exists_le_map_eq_of_le_map (hW ▸ hT)
  let I : Finset (ULift.{u} (Fin (Fintype.card (Σ j, Fin (d j))))) :=
    ⟨u, Multiset.nodup_of_le hu Finset.univ.nodup⟩
  have hI : I.card = s := by rw [← hcard, Multiset.card_map]; rfl
  -- The eigenspace of `⋀^s Z` for `c = ∏_{i ∈ I} c_i` is a nonzero subrepresentation.
  let c : kˣ := ∏ i ∈ I, cs (idx i)
  let E : Subrepresentation (rV.exteriorPower s) :=
    { toSubmodule := Module.End.eigenspace (exteriorPower.map s Z) c
      apply_mem_toSubmodule w x hx := by
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        change exteriorPower.map s Z (exteriorPower.map s (rV w) x) =
          (c : k) • exteriorPower.map s (rV w) x
        rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hZcomm, exteriorPower.map_comp,
          LinearMap.comp_apply, hx, map_smul] }
  have hBI : B ⟨I, hI⟩ ∈ E := by
    change B ⟨I, hI⟩ ∈ Module.End.eigenspace _ _
    rw [Module.End.mem_eigenspace_iff, exteriorPower.map_basis_exteriorPower_of_diagonal b hZb,
      Units.coe_prod]
  have hE : E ≠ ⊥ := fun h ↦ by
    rw [h] at hBI
    exact B.ne_zero ⟨I, hI⟩ ((Submodule.mem_bot k).1 hBI)
  obtain ⟨U, hUE, hirr⟩ := Subrepresentation.exists_lt_isIrreducible_subquotient hE
  refine ⟨U, E, hUE, hirr, ?_⟩
  have hQ := (D.map r).detWeight_eq_of_isPositiveCentralPair_of_basis χ hz' B hρ' hUE
    (hdet U E hirr) c fun x hx ↦ by
      rw [← hZ', (Module.End.mem_eigenspace_iff.1 hx), sub_self]
      exact Submodule.zero_mem _
  refine hQ.trans ?_
  change _ = (I.val.map f).sum
  rw [← Finset.sum_eq_multiset_sum]
  simp only [c, map_prod, toAdd_prod, Finset.sum_div, f, hdw]

/-- The tensor-product weight theorem for a degree datum `D₀` and irreducible `V` and `E`: every
subquotient `Q` of `V ⊗ E` with finite geometric determinant has `dw(Q) = dw(V) + dw(E)`. -/
theorem DegreeDatum.detWeight_subquotient_tprod_eq_add
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {W : Type*} [Group W] (D₀ : DegreeDatum W)
    (χ : RealCharacter k)
    {V E : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (rV : Representation k W V) (rE : Representation k W E)
    (hV : rV.IsIrreducible) (hE : rE.IsIrreducible)
    (hdetV : rV.HasFiniteGeometricDet D₀.deg) (hdetE : rE.HasFiniteGeometricDet D₀.deg)
    {U S : Subrepresentation (rV.tprod rE)} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet D₀.deg) :
    (S.subquotient U).detWeight χ D₀.degreeOneElement =
      rV.detWeight χ D₀.degreeOneElement + rE.detWeight χ D₀.degreeOneElement := by
  classical
  let X := rV.prod rE
  let fst := Representation.IntertwiningMap.fst k rV rE
  let snd := Representation.IntertwiningMap.snd k rV rE
  -- `V ⊕ E` is semisimple
  have hX : X.IsSemisimpleRepresentation := by
    let Vs : Bool → Subrepresentation X := fun j ↦
      if j then (Representation.IntertwiningMap.inl k rV rE).range
      else (Representation.IntertwiningMap.inr k rV rE).range
    refine isSemisimpleRepresentation_of_isInternal Vs (fun j ↦ ?_) ?_
    · cases j
      · let e : rE.Equiv (Vs false).toRepresentation :=
          .mk (LinearEquiv.ofInjective (LinearMap.inr k V E) LinearMap.inr_injective)
            fun _ ↦ LinearMap.ext fun _ ↦ Subtype.ext <| by
              change LinearMap.inr k V E _ = X _ (LinearMap.inr k V E _)
              simp [X]
        exact e.isIrreducible_iff.1 hE
      · let e : rV.Equiv (Vs true).toRepresentation :=
          .mk (LinearEquiv.ofInjective (LinearMap.inl k V E) LinearMap.inl_injective)
            fun _ ↦ LinearMap.ext fun _ ↦ Subtype.ext <| by
              change LinearMap.inl k V E _ = X _ (LinearMap.inl k V E _)
              simp [X]
        exact e.isIrreducible_iff.1 hV
    · refine (DirectSum.isInternal_submodule_iff_isCompl _ (i := true) (j := false) (by decide)
        (by ext x; cases x <;> simp)).2 ?_
      exact LinearMap.isCompl_range_inl_inr
  -- the represented degree datum of `V ⊕ E` in a basis, and a positive central pair
  let n := ULift.{u} (Fin (Module.finrank k (V × E)))
  let b : Basis n k (V × E) := (Module.finBasis k (V × E)).reindex Equiv.ulift.symm
  let D : RepresentedDegreeDatum W n k :=
    { D₀ with rep := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp X.toHomUnits }
  have hρ (w : W) : LinearMap.toMatrix b b (X w) = (D.rep w : Matrix n n k) := by
    ext i i'
    rw [LinearMap.toMatrix_apply]
    exact (LinearMap.toMatrixAlgEquiv_apply b (X w) i i').symm
  have hss : D.IsSemisimple :=
    (Subrepresentation.orderIsoMapComap (D.basisEquiv b hρ)).complementedLattice_iff.1 hX
  obtain ⟨N, z, hz⟩ := D.exists_isPositiveCentralPair hss
  -- `z` acts on `V` by a scalar `c` and on `E` by a scalar `d`
  obtain ⟨c, hc, hcV⟩ := D.exists_detWeight_eq_of_isPositiveCentralPair_of_surjective χ hz b hρ
    hV hdetV fst (Representation.IntertwiningMap.fst_surjective rV rE)
  obtain ⟨d, hd, hdE⟩ := D.exists_detWeight_eq_of_isPositiveCentralPair_of_surjective χ hz b hρ
    hE hdetE snd (Representation.IntertwiningMap.snd_surjective rV rE)
  -- the datum of `(V ⊕ E) ⊗ (V ⊕ E)`, with the transported positive central pair `(N, z ⊗ z)`
  let B := b.tensorProduct b
  let r : GL n k →* GL (n × n) k := kroneckerHom.comp ((MonoidHom.id _).prod (MonoidHom.id _))
  obtain ⟨φ, hφ⟩ := exists_algHom_comp_eq_evalAlgHom_kroneckerHom (k := k) (n := n)
  have hz' := hz.map r φ hφ
  have hρ' (w : W) : LinearMap.toMatrix B B (X.tprod X w) = ((D.map r).rep w : Matrix _ _ k) := by
    change LinearMap.toMatrix B B (TensorProduct.map (X w) (X w)) = _
    rw [TensorProduct.toMatrix_map, hρ]
    rfl
  -- the quotient map `p: (V ⊕ E) ⊗ (V ⊕ E) → V ⊗ E`, through which `z ⊗ z` acts by `c d`
  let p := fst.tensor snd
  have hp : Function.Surjective p :=
    TensorProduct.map_surjective (Representation.IntertwiningMap.fst_surjective rV rE)
      (Representation.IntertwiningMap.snd_surjective rV rE)
  have hpz (x : (V × E) ⊗[k] (V × E)) :
      p (Matrix.toLin B B (r z : Matrix _ _ k) x) = ((c * d : kˣ) : k) • p x := by
    change p (Matrix.toLin B B ((z : Matrix n n k) ⊗ₖ (z : Matrix n n k)) x) = _
    rw [Matrix.toLin_kronecker]
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, p, Representation.IntertwiningMap.tensor_apply, hc, hd,
        TensorProduct.smul_tmul_smul, Units.val_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  -- the readout on the preimage of `Q`
  let e := Subrepresentation.subquotientComapEquiv p hp U S
  have hUS' : Subrepresentation.comap p U < Subrepresentation.comap p S := by
    refine lt_of_le_of_ne (fun x hx ↦ hUS.le hx) fun h ↦ ?_
    obtain ⟨y, hyS, hyU⟩ := IsConcreteLE.exists_of_lt hUS
    obtain ⟨x, rfl⟩ := hp y
    have hx : x ∈ Subrepresentation.comap p S := hyS
    rw [← h] at hx
    exact hyU hx
  have hQ := (D.map r).detWeight_eq_of_isPositiveCentralPair_of_basis χ hz' B hρ' hUS'
    ((e.hasFiniteGeometricDet_iff).1 hdet) (c * d) fun x _ ↦ by
      rw [Subrepresentation.mem_comap, map_sub, map_smul, hpz, sub_self]
      exact U.toSubmodule.zero_mem
  rw [e.detWeight_eq]
  refine hQ.trans ?_
  rw [hcV, hdE, map_mul, toAdd_mul, add_div]

end AlgebraicGeometry.Monodromy

namespace Representation

open AlgebraicGeometry.Monodromy

variable {k : Type*} [Field k] {W : Type*} [Group W]

/-- Let `V` be a nonzero semisimple representation of a degree datum over an algebraically closed
field of characteristic zero, written as an internal direct sum of simple subrepresentations
`Vs j`, with rank-counted weight multiset `Representation.weightMultiset χ γ Vs`: the multiset in
which the determinant weight of `Vs j` occurs `dim Vs j` times.  If the summands `Vs j` and the
simple constituent `Q = S / U` of `⋀^s V` all have finite geometric determinant, then `dw_χ(Q)` is
the sum of a sub-multiset of the weight multiset of size `s`, that is, `a_{i₁} + ⋯ + a_{i_s}` for
indices `i₁ < ⋯ < i_s` in the rank-counted weight list.

The degree map need not be surjective and `γ` need not have degree one. -/
theorem exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (rV : Representation k W V) (s : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Subrepresentation rV)
    (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule)
    {U S : Subrepresentation (rV.exteriorPower s)} (hUS : U < S)
    (hsimple : IsIrreducible (S.subquotient U))
    (hdet : (S.subquotient U).HasFiniteGeometricDet deg) :
    ∃ T : Multiset ℝ, T ≤ weightMultiset χ γ Vs ∧ Multiset.card T = s ∧
      (S.subquotient U).detWeight χ γ = T.sum := by
  classical
  by_cases htriv : ∀ w, deg w = 1
  · -- Every element has degree zero: all the weights vanish.
    have hV0 (j : ι) := detWeight_eq_zero_of_forall_deg_eq_one htriv _ (hdetVs j) χ γ
    have hW : weightMultiset χ γ Vs =
        Multiset.replicate (Multiset.card (weightMultiset χ γ Vs)) 0 :=
      Multiset.eq_replicate_of_mem fun x hx ↦ by
        obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hx
        rw [hV0] at hj
        exact Multiset.eq_of_mem_replicate hj
    have hcard : Multiset.card (weightMultiset χ γ Vs) = Module.finrank k V := by
      rw [weightMultiset, Multiset.card_sum]
      simp only [Multiset.card_replicate]
      rw [Module.finrank_eq_card_basis
        (hdirect.collectedBasis fun j ↦ Module.finBasis k (Vs j).toSubmodule),
        Fintype.card_sigma]
      simp
    have hs : s ≤ Module.finrank k V := by
      obtain ⟨x, hxS, hxU⟩ := IsConcreteLE.exists_of_lt hUS
      have hx0 : x ≠ 0 := fun h ↦ hxU (h ▸ Submodule.zero_mem _)
      have hpos : 0 < Module.finrank k (⋀[k]^s V) :=
        Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx0⟩
      rw [exteriorPower.finrank_eq] at hpos
      by_contra! h
      rw [Nat.choose_eq_zero_of_lt h] at hpos
      exact hpos.false
    refine ⟨Multiset.replicate s 0, ?_, Multiset.card_replicate _ _, ?_⟩
    · rw [hW, Multiset.replicate_le_replicate, hcard]
      exact hs
    · rw [detWeight_eq_zero_of_forall_deg_eq_one htriv _ hdet χ γ, Multiset.sum_replicate,
        smul_zero]
  -- Otherwise divide the degrees by their generator to get a degree datum.
  simp only [not_forall] at htriv
  obtain ⟨D₀, hker, u, hu, m, hγ⟩ := DegreeDatum.exists_ker_eq_and_eq_mul_zpow deg htriv γ
  obtain ⟨T₀, hle, hcard, hsum⟩ := D₀.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower χ rV
    s Vs hsimpleVs (fun j ↦ (hasFiniteGeometricDet_congr hker _).1 (hdetVs j)) hdirect hUS hsimple
    ((hasFiniteGeometricDet_congr hker _).1 hdet)
  refine ⟨T₀.map fun x ↦ (m : ℝ) * x, ?_, by rw [Multiset.card_map, hcard], ?_⟩
  · have : weightMultiset χ γ Vs =
        (weightMultiset χ D₀.degreeOneElement Vs).map fun x ↦ (m : ℝ) * x := by
      rw [weightMultiset, weightMultiset, ← Multiset.coe_mapAddMonoidHom, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate, hγ,
        detWeight_mul_zpow_of_mem_ker _ (hdetVs j) χ D₀.degreeOneElement hu]
    rw [this]
    exact Multiset.map_le_map hle
  · rw [hγ, detWeight_mul_zpow_of_mem_ker _ hdet χ D₀.degreeOneElement hu,
      Multiset.sum_map_mul_left, Multiset.map_id']
    exact congrArg _ hsum

/-- The converse of `exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`: let `V` be a
semisimple representation of a degree datum over an algebraically closed field of characteristic
zero, written as an internal direct sum of simple subrepresentations `Vs j` with finite geometric
determinant. If all simple constituents of `⋀^s V` have finite geometric determinant, every
sub-multiset `T` of size `s` of the rank-counted weight multiset is the determinant weight
`dw_χ(Q) = T.sum` of some simple constituent `Q = S / U` of `⋀^s V`. As in
`exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower`, the degree map need not be surjective
and `γ` need not have degree one. -/
theorem exists_detWeight_eq_sum_of_exteriorPower [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rV : Representation k W V) (s : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Vs : ι → Subrepresentation rV)
    (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule)
    (hdet : ∀ U S : Subrepresentation (rV.exteriorPower s), IsIrreducible (S.subquotient U) →
      (S.subquotient U).HasFiniteGeometricDet deg)
    {T : Multiset ℝ} (hT : T ≤ weightMultiset χ γ Vs) (hcard : Multiset.card T = s) :
    ∃ U S : Subrepresentation (rV.exteriorPower s), U < S ∧ IsIrreducible (S.subquotient U) ∧
      (S.subquotient U).detWeight χ γ = T.sum := by
  classical
  by_cases htriv : ∀ w, deg w = 1
  · -- Every element has degree zero: all the weights vanish.
    have hV0 (j : ι) := detWeight_eq_zero_of_forall_deg_eq_one htriv _ (hdetVs j) χ γ
    have hT0 : T.sum = 0 := Multiset.sum_eq_zero fun x hx ↦ by
      obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 (Multiset.mem_of_le hT hx)
      rw [hV0] at hj
      exact Multiset.eq_of_mem_replicate hj
    -- `s ≤ dim V`, so `⋀^s V` is nonzero and has a simple constituent.
    have hcardW : Multiset.card (weightMultiset χ γ Vs) = Module.finrank k V := by
      rw [weightMultiset, Multiset.card_sum]
      simp only [Multiset.card_replicate]
      rw [Module.finrank_eq_card_basis
        (hdirect.collectedBasis fun j ↦ Module.finBasis k (Vs j).toSubmodule),
        Fintype.card_sigma]
      simp
    have hs : s ≤ Module.finrank k V := hcard ▸ hcardW ▸ Multiset.card_le_card hT
    have htop : (⊤ : Subrepresentation (rV.exteriorPower s)) ≠ ⊥ := by
      intro h
      have hpos : 0 < Module.finrank k (⋀[k]^s V) := by
        rw [exteriorPower.finrank_eq]
        exact Nat.choose_pos hs
      obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
      have hxtop : x ∈ (⊤ : Subrepresentation (rV.exteriorPower s)) := Submodule.mem_top
      rw [h] at hxtop
      exact hx ((Submodule.mem_bot k).1 hxtop)
    obtain ⟨U, hU, hirr⟩ := Subrepresentation.exists_lt_isIrreducible_subquotient htop
    exact ⟨U, ⊤, hU, hirr, by
      rw [detWeight_eq_zero_of_forall_deg_eq_one htriv _ (hdet U ⊤ hirr) χ γ, hT0]⟩
  -- Otherwise divide the degrees by their generator to get a degree datum.
  simp only [not_forall] at htriv
  obtain ⟨D₀, hker, u, hu, m, hγ⟩ := DegreeDatum.exists_ker_eq_and_eq_mul_zpow deg htriv γ
  have hW : weightMultiset χ γ Vs =
      (weightMultiset χ D₀.degreeOneElement Vs).map fun x ↦ (m : ℝ) * x := by
    rw [weightMultiset, weightMultiset, ← Multiset.coe_mapAddMonoidHom, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate, hγ,
      detWeight_mul_zpow_of_mem_ker _ (hdetVs j) χ D₀.degreeOneElement hu]
  obtain ⟨T₀, hT₀, rfl⟩ := Multiset.exists_le_map_eq_of_le_map (hW ▸ hT)
  obtain ⟨U, S, hUS, hirr, hdw⟩ := D₀.exists_detWeight_eq_sum_of_exteriorPower χ rV s Vs
    hsimpleVs (fun j ↦ (hasFiniteGeometricDet_congr hker _).1 (hdetVs j)) hdirect
    (fun U S h ↦ (hasFiniteGeometricDet_congr hker _).1 (hdet U S h)) hT₀
    (by rw [← hcard, Multiset.card_map])
  refine ⟨U, S, hUS, hirr, ?_⟩
  rw [hγ, detWeight_mul_zpow_of_mem_ker _ (hdet U S hirr) χ D₀.degreeOneElement hu, hdw,
    Multiset.sum_map_mul_left, Multiset.map_id']

/-- The weights of the subquotients of the tensor product of two irreducible representations `V`
and `E` of a degree datum, over an algebraically closed field of characteristic zero: if `V`, `E`
and a subquotient `Q = S / U` of `V ⊗ E` have finite geometric determinant, then
`dw_χ(Q) = dw_χ(V) + dw_χ(E)`.  The degree map need not be surjective and `γ` need not have degree
one. -/
theorem detWeight_subquotient_tprod_eq_add [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V E : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (rV : Representation k W V) (rE : Representation k W E)
    (hV : rV.IsIrreducible) (hE : rE.IsIrreducible)
    (hdetV : rV.HasFiniteGeometricDet deg) (hdetE : rE.HasFiniteGeometricDet deg)
    {U S : Subrepresentation (rV.tprod rE)} (hUS : U < S)
    (hdet : (S.subquotient U).HasFiniteGeometricDet deg) :
    (S.subquotient U).detWeight χ γ = rV.detWeight χ γ + rE.detWeight χ γ := by
  by_cases htriv : ∀ w, deg w = 1
  · -- every element has degree zero: all the weights vanish
    rw [detWeight_eq_zero_of_forall_deg_eq_one htriv _ hdet χ γ,
      detWeight_eq_zero_of_forall_deg_eq_one htriv _ hdetV χ γ,
      detWeight_eq_zero_of_forall_deg_eq_one htriv _ hdetE χ γ, add_zero]
  -- otherwise divide the degrees by their generator to get a degree datum
  simp only [not_forall] at htriv
  obtain ⟨D₀, hker, u, hu, m, rfl⟩ := DegreeDatum.exists_ker_eq_and_eq_mul_zpow deg htriv γ
  rw [detWeight_mul_zpow_of_mem_ker _ hdet χ _ hu, detWeight_mul_zpow_of_mem_ker _ hdetV χ _ hu,
    detWeight_mul_zpow_of_mem_ker _ hdetE χ _ hu, ← mul_add,
    D₀.detWeight_subquotient_tprod_eq_add χ _ _ hV hE ((hasFiniteGeometricDet_congr hker _).1 hdetV)
      ((hasFiniteGeometricDet_congr hker _).1 hdetE) hUS
      ((hasFiniteGeometricDet_congr hker _).1 hdet)]

/-- Let `V` and `E` be finite-dimensional representations of one and the same degree datum over an
algebraically closed field of characteristic zero, and let `Q` be a simple constituent of `V ⊗ E`,
presented as a subquotient `S / U` for subrepresentations `U < S` of `V ⊗ E`.  If `Q` and all
simple constituents of `V` and of `E` have finite geometric determinant, then
`dw_χ(Q) = dw_χ(V_i) + dw_χ(E_j)` for a simple constituent `V_i = SV / UV` of `V` and a simple
constituent `E_j = SE / UE` of `E`.  Neither `V`, nor `E`, nor `V ⊗ E` is assumed semisimple. -/
theorem exists_detWeight_eq_add_of_subquotient_tprod [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V E : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (rV : Representation k W V) (rE : Representation k W E)
    (hdetV : ∀ UV SV : Subrepresentation rV, IsIrreducible (SV.subquotient UV) →
      (SV.subquotient UV).HasFiniteGeometricDet deg)
    (hdetE : ∀ UE SE : Subrepresentation rE, IsIrreducible (SE.subquotient UE) →
      (SE.subquotient UE).HasFiniteGeometricDet deg)
    {U S : Subrepresentation (rV.tprod rE)}
    (hsimple : IsIrreducible (S.subquotient U))
    (hdet : (S.subquotient U).HasFiniteGeometricDet deg) :
    ∃ UV SV : Subrepresentation rV, ∃ UE SE : Subrepresentation rE,
      UV < SV ∧ UE < SE ∧
      IsIrreducible (SV.subquotient UV) ∧ IsIrreducible (SE.subquotient UE) ∧
      (SV.subquotient UV).HasFiniteGeometricDet deg ∧
      (SE.subquotient UE).HasFiniteGeometricDet deg ∧
      (S.subquotient U).detWeight χ γ =
        (SV.subquotient UV).detWeight χ γ + (SE.subquotient UE).detWeight χ γ := by
  obtain ⟨UV, SV, UE, SE, hUV, hUE, hV, hE, U', S', ⟨e⟩⟩ :=
    Subrepresentation.exists_subquotient_tprod_equiv hsimple
  -- `Q' = S' / (U' ∩ S')`, a subquotient of `V_i ⊗ E_j` equivalent to `Q`
  let e' := (Subrepresentation.subquotientInfEquiv U' S').trans e
  refine ⟨UV, SV, UE, SE, hUV, hUE, hV, hE, hdetV UV SV hV, hdetE UE SE hE, ?_⟩
  rw [e'.detWeight_eq]
  exact detWeight_subquotient_tprod_eq_add χ deg γ _ _ hV hE (hdetV UV SV hV) (hdetE UE SE hE)
    (Subrepresentation.inf_lt_of_isIrreducible (e.isIrreducible_iff.2 hsimple))
    (e'.hasFiniteGeometricDet_iff.1 hdet)

/-- The converse of `exists_detWeight_eq_add_of_subquotient_tprod`: for simple constituents
`V_i = SV / UV` of `V` and `E_j = SE / UE` of `E` with finite geometric determinant, if all simple
constituents of `V ⊗ E` have finite geometric determinant, then some simple constituent `Q` of
`V ⊗ E` has `dw_χ(Q) = dw_χ(V_i) + dw_χ(E_j)`: any simple constituent of `V_i ⊗ E_j` is one. -/
theorem exists_isIrreducible_subquotient_tprod_detWeight_eq_add [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    {V E : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    {rV : Representation k W V} {rE : Representation k W E}
    {UV SV : Subrepresentation rV} {UE SE : Subrepresentation rE}
    (hV : IsIrreducible (SV.subquotient UV)) (hE : IsIrreducible (SE.subquotient UE))
    (hdetV : (SV.subquotient UV).HasFiniteGeometricDet deg)
    (hdetE : (SE.subquotient UE).HasFiniteGeometricDet deg)
    (hdet : ∀ U S : Subrepresentation (rV.tprod rE), IsIrreducible (S.subquotient U) →
      (S.subquotient U).HasFiniteGeometricDet deg) :
    ∃ U S : Subrepresentation (rV.tprod rE), U < S ∧ IsIrreducible (S.subquotient U) ∧
      (S.subquotient U).detWeight χ γ =
        (SV.subquotient UV).detWeight χ γ + (SE.subquotient UE).detWeight χ γ := by
  -- a simple constituent `⊤ / B` of `V_i ⊗ E_j`
  have := hV.nontrivial
  have := hE.nontrivial
  have : Nontrivial ((SV.toSubmodule ⧸ UV.toSubmodule.comap SV.toSubmodule.subtype) ⊗[k]
      (SE.toSubmodule ⧸ UE.toSubmodule.comap SE.toSubmodule.subtype)) :=
    Module.finrank_pos_iff.1 (by
      rw [Module.finrank_tensorProduct (R := k)]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (SV.toSubmodule ⧸ UV.toSubmodule.comap SV.toSubmodule.subtype)
    ⊗[k] (SE.toSubmodule ⧸ UE.toSubmodule.comap SE.toSubmodule.subtype))
  obtain ⟨B, hB, hirr⟩ := Subrepresentation.exists_lt_isIrreducible_subquotient
    (ρ := (SV.subquotient UV).tprod (SE.subquotient UE)) (A := ⊤)
    fun h ↦ hx <| by
      have : x ∈ (⊤ : Subrepresentation ((SV.subquotient UV).tprod (SE.subquotient UE))) :=
        Submodule.mem_top
      rw [h] at this
      exact (Submodule.mem_bot k).1 this
  -- it is a subquotient of `SV ⊗ SE`, hence of `V ⊗ E`
  let qV : SV.toRepresentation.IntertwiningMap (SV.subquotient UV) := ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
  let qE : SE.toRepresentation.IntertwiningMap (SE.subquotient UE) := ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
  let iV : SV.toRepresentation.IntertwiningMap rV := ⟨Submodule.subtype _, fun _ ↦ rfl⟩
  let iE : SE.toRepresentation.IntertwiningMap rE := ⟨Submodule.subtype _, fun _ ↦ rfl⟩
  let q := qV.tensor qE
  let i := iV.tensor iE
  have hq : Function.Surjective q :=
    TensorProduct.map_surjective (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _)
  have hi : Function.Injective i :=
    TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
      (Submodule.injective_subtype _)
  let e₁ := Subrepresentation.subquotientComapEquiv q hq B ⊤
  let U := Subrepresentation.map i (Subrepresentation.comap q B)
  let S := Subrepresentation.map i (Subrepresentation.comap q ⊤)
  let e₂ : (S.subquotient U).Equiv _ := (Subrepresentation.subquotientEquivOfIntertwiningMap i
    (U := Subrepresentation.comap q B) (S := Subrepresentation.comap q ⊤) (U' := U) (S' := S)
    (fun x hx ↦ ⟨x, hx, rfl⟩) (fun x _ hx ↦ ⟨x, hx, rfl⟩)
    (fun x _ hx ↦ by
      obtain ⟨y, hy, hxy⟩ := Subrepresentation.mem_map.1 hx
      exact hi hxy ▸ hy) fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := Subrepresentation.mem_map.1 hy
      exact ⟨x, hx, by rw [sub_self]; exact U.toSubmodule.zero_mem⟩).symm
  let e := e₂.trans e₁
  have hQ : IsIrreducible (S.subquotient U) := e.isIrreducible_iff.2 hirr
  have hUS : U < S := by
    have hle : U ≤ S := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := Subrepresentation.mem_map.1 hy
      exact Subrepresentation.mem_map.2
        ⟨x, Subrepresentation.mem_comap.2 (by exact Submodule.mem_top), rfl⟩
    simpa [inf_eq_left.2 hle] using Subrepresentation.inf_lt_of_isIrreducible hQ
  refine ⟨U, S, hUS, hQ, ?_⟩
  rw [← e.detWeight_eq]
  exact detWeight_subquotient_tprod_eq_add χ deg γ _ _ hV hE hdetV hdetE hB
    (e.hasFiniteGeometricDet_iff.2 (hdet U S hQ))

end Representation

namespace AlgebraicGeometry.Monodromy.DegreeDatum

variable {W : Type*} [Group W] {k : Type*} [Field k]

/-- **A rank-one character has constant modulus on a degree component.**  Let `χ: W → kˣ` be a
character of a degree datum with finite image on the degree-zero subgroup `P`, and `ι: k → ℂ` a
field embedding.  Every `w` of degree `m` satisfies `|ι(χ(w))| = |ι(χ(γ))| ^ m`: writing
`w = u γ ^ m` with `u ∈ P`, the value `χ(u)` is a root of unity. -/
theorem norm_apply_eq_zpow (D : DegreeDatum W) (χ : W →* kˣ)
    (hχ : (Set.range fun u : D.deg.ker ↦ χ u).Finite) (ι : k →+* ℂ) {w : W} {m : ℤ}
    (hw : D.deg w = Multiplicative.ofAdd m) :
    ‖ι (χ w : k)‖ = ‖ι (χ D.degreeOneElement : k)‖ ^ m := by
  have hu : w * (D.degreeOneElement ^ m)⁻¹ ∈ D.deg.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, D.deg_degreeOneElement, hw, ← ofAdd_zsmul,
      smul_eq_mul, mul_one, mul_inv_cancel]
  let φ := χ.comp D.deg.ker.subtype
  have : Finite φ.range := (hχ : (Set.range φ).Finite).to_subtype
  obtain ⟨e, he, hue⟩ := isOfFinOrder_iff_pow_eq_one.1 <| (Units.map ι.toMonoidHom).isOfFinOrder <|
    φ.range.subtype.isOfFinOrder (isOfFinOrder_of_finite ⟨φ ⟨_, hu⟩, ⟨_, hu⟩, rfl⟩)
  have h1 : ‖ι (χ (w * (D.degreeOneElement ^ m)⁻¹) : k)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by simpa [φ] using congr(Units.val $hue)) he.ne'
  calc ‖ι (χ w : k)‖
      = ‖ι (χ (w * (D.degreeOneElement ^ m)⁻¹) * χ (D.degreeOneElement ^ m) : k)‖ := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel_right]
    _ = ‖ι (χ D.degreeOneElement : k)‖ ^ m := by
        rw [map_mul, norm_mul, h1, one_mul, map_zpow, Units.val_zpow_eq_zpow_val,
          map_zpow₀, norm_zpow]

/-- For an element `σ` of positive degree `e` and a character `χ` with finite image on `P`,
`|ι(χ(σ))| = q ^ (e w / 2)` if and only if `|ι(χ(γ))| = q ^ (w / 2)`. -/
theorem norm_apply_eq_rpow_iff (D : DegreeDatum W) (χ : W →* kˣ)
    (hχ : (Set.range fun u : D.deg.ker ↦ χ u).Finite) (ι : k →+* ℂ) {q : ℝ} (hq : 0 < q)
    (t : ℝ) {σ : W} {e : ℕ} (he : 0 < e) (hσ : D.deg σ = Multiplicative.ofAdd (e : ℤ)) :
    ‖ι (χ σ : k)‖ = q ^ (e * t / 2) ↔ ‖ι (χ D.degreeOneElement : k)‖ = q ^ (t / 2) := by
  rw [D.norm_apply_eq_zpow χ hχ ι hσ, zpow_natCast, mul_div_assoc, mul_comm (e : ℝ),
    Real.rpow_mul_natCast hq.le]
  exact pow_left_inj₀ (norm_nonneg _) (by positivity) he.ne'

/-- **Rank-one weight from a positive-degree element.**  Let `χ` be a character of a degree datum
with finite image on `P`, `ι: k → ℂ` a field embedding and `q > 0`.  Let `F x` be a nonempty
family of elements of positive degrees `d x`, such as the geometric Frobenius elements at the
closed points of a curve over `𝔽_q`, of degree `[κ(x): 𝔽_q]`.  Then `χ` is pure of weight `t`
along this family, `|ι(χ(F x))| = q ^ (d x t / 2)` for all `x`, if and only if one element `σ`
of positive degree `e` satisfies `|ι(χ(σ))| = q ^ (e t / 2)`. -/
theorem forall_norm_eq_rpow_iff_exists (D : DegreeDatum W) (χ : W →* kˣ)
    (hχ : (Set.range fun u : D.deg.ker ↦ χ u).Finite) (ι : k →+* ℂ) {q : ℝ} (hq : 0 < q)
    (t : ℝ) {X : Type*} [Nonempty X] (F : X → W) (d : X → ℕ) (hd : ∀ x, 0 < d x)
    (hF : ∀ x, D.deg (F x) = Multiplicative.ofAdd (d x : ℤ)) :
    (∀ x, ‖ι (χ (F x) : k)‖ = q ^ (d x * t / 2)) ↔
      ∃ σ : W, ∃ e : ℕ, 0 < e ∧ D.deg σ = Multiplicative.ofAdd (e : ℤ) ∧
        ‖ι (χ σ : k)‖ = q ^ (e * t / 2) := by
  refine ⟨fun h ↦ ?_, fun ⟨σ, e, he, hσ, h⟩ x ↦ ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨F x, d x, hd x, hF x, h x⟩
  · rw [D.norm_apply_eq_rpow_iff χ hχ ι hq t he hσ] at h
    rwa [D.norm_apply_eq_rpow_iff χ hχ ι hq t (hd x) (hF x)]

/-- **Rank-one weight from a positive-degree element**, the version for every element: under the
hypotheses of `forall_norm_eq_rpow_iff_exists`, `χ` is pure of weight `t` along the family `F` if
and only if every element `σ` of positive degree `e` satisfies `|ι(χ(σ))| = q ^ (e t / 2)`. -/
theorem forall_norm_eq_rpow_iff_forall (D : DegreeDatum W) (χ : W →* kˣ)
    (hχ : (Set.range fun u : D.deg.ker ↦ χ u).Finite) (ι : k →+* ℂ) {q : ℝ} (hq : 0 < q)
    (t : ℝ) {X : Type*} [Nonempty X] (F : X → W) (d : X → ℕ) (hd : ∀ x, 0 < d x)
    (hF : ∀ x, D.deg (F x) = Multiplicative.ofAdd (d x : ℤ)) :
    (∀ x, ‖ι (χ (F x) : k)‖ = q ^ (d x * t / 2)) ↔
      ∀ (σ : W) (e : ℕ), 0 < e → D.deg σ = Multiplicative.ofAdd (e : ℤ) →
        ‖ι (χ σ : k)‖ = q ^ (e * t / 2) := by
  refine ⟨fun h σ e he hσ ↦ ?_, fun h x ↦ h _ _ (hd x) (hF x)⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have := h x
  rw [D.norm_apply_eq_rpow_iff χ hχ ι hq t (hd x) (hF x)] at this
  rwa [D.norm_apply_eq_rpow_iff χ hχ ι hq t he hσ]

end AlgebraicGeometry.Monodromy.DegreeDatum

namespace Representation.CompositionSeries

open DirectSum

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The *rank-counted constituent weights* of a composition series: the determinant weight of each
composition factor `A_i`, repeated `dim A_i` times. -/
noncomputable def weightMultiset (χ : RealCharacter k) (γ : W) (s : ρ.CompositionSeries) :
    Multiset ℝ :=
  ∑ i, Multiset.replicate (Module.finrank k ((s.series i.succ).toSubmodule ⧸
    (s.series i.castSucc).toSubmodule.comap (s.series i.succ).toSubmodule.subtype))
    ((s.factor i).detWeight χ γ)

/-- The weight multiset of a composition series is that of the decomposition of its
semisimplification into its summands. -/
theorem weightMultiset_directSumSummand (χ : RealCharacter k) (γ : W) (s : ρ.CompositionSeries) :
    Representation.weightMultiset χ γ (directSumSummand fun i ↦ s.factor i) =
      s.weightMultiset χ γ := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(directSumSummandEquiv (fun i ↦ s.factor i) i).finrank_eq,
    (directSumSummandEquiv (fun i ↦ s.factor i) i).detWeight_eq]

/-- An irreducible subquotient `S / U` is equivalent to `S / (U ⊓ S)`, with `U ⊓ S < S`. -/
private theorem exists_lt_of_isIrreducible {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k W V'} {U S : Subrepresentation σ}
    (hirr : (S.subquotient U).IsIrreducible) :
    U ⊓ S < S ∧ (S.subquotient (U ⊓ S)).IsIrreducible ∧
      Nonempty ((S.subquotient (U ⊓ S)).Equiv (S.subquotient U)) :=
  ⟨Subrepresentation.inf_lt_of_isIrreducible hirr,
    (Subrepresentation.subquotientInfEquiv U S).isIrreducible_iff.2 hirr,
    ⟨Subrepresentation.subquotientInfEquiv U S⟩⟩

/-- The two directions of `exteriorPower_detWeight` for a representation `ρ` whose `r`-th exterior
power has the same constituents as that of a semisimple representation `X`, decomposed into simple
summands `Vs j`. -/
private theorem exteriorPower_detWeight_of_constituentsLE [IsAlgClosed k] [CharZero k]
    (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W) (r : ℕ)
    {V' : Type*} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [Nontrivial V']
    {X : Representation k W V'} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Vs : ι → Subrepresentation X) (hsimpleVs : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdetVs : ∀ j, (Vs j).toRepresentation.HasFiniteGeometricDet deg)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule) {M : Multiset ℝ}
    (hM : Representation.weightMultiset χ γ Vs = M)
    (h₁ : ConstituentsLE (ρ.exteriorPower r) (X.exteriorPower r))
    (h₂ : ConstituentsLE (X.exteriorPower r) (ρ.exteriorPower r))
    (hdet : ∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      (S.subquotient U).HasFiniteGeometricDet deg) :
    (∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      ∃ T ≤ M, Multiset.card T = r ∧ (S.subquotient U).detWeight χ γ = T.sum) ∧
    ∀ T ≤ M, Multiset.card T = r →
      ∃ U S : Subrepresentation (ρ.exteriorPower r), U < S ∧ (S.subquotient U).IsIrreducible ∧
        (S.subquotient U).detWeight χ γ = T.sum := by
  subst hM
  refine ⟨fun U S hirr ↦ ?_, fun T hT hcard ↦ ?_⟩
  · -- `Q` is a constituent of `⋀^r X`.
    obtain ⟨U', S', hirr', ⟨e⟩⟩ := h₁ U S hirr
    obtain ⟨hlt, hirr'', ⟨e'⟩⟩ := exists_lt_of_isIrreducible hirr'
    obtain ⟨T, hT, hcard, hdw⟩ := exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower χ deg γ
      X r Vs hsimpleVs hdetVs hdirect hlt hirr''
      ((e.trans e'.symm).hasFiniteGeometricDet_iff.2 (hdet U S hirr))
    exact ⟨T, hT, hcard, by rw [← (e.trans e'.symm).detWeight_eq, hdw]⟩
  · -- a constituent of `⋀^r X` with the weight `T.sum`, and the same constituent of `⋀^r V`
    obtain ⟨U, S, -, hirr, hdw⟩ := exists_detWeight_eq_sum_of_exteriorPower χ deg γ X r Vs
      hsimpleVs hdetVs hdirect (fun U S hirr ↦ by
        obtain ⟨U', S', hirr', ⟨e⟩⟩ := h₂ U S hirr
        exact e.hasFiniteGeometricDet_iff.1 (hdet U' S' hirr')) hT hcard
    obtain ⟨U', S', hirr', ⟨e⟩⟩ := h₂ U S hirr
    obtain ⟨hlt, hirr'', ⟨e'⟩⟩ := exists_lt_of_isIrreducible hirr'
    exact ⟨U' ⊓ S', S', hlt, hirr'', by rw [(e.trans e'.symm).detWeight_eq, hdw]⟩

/-- **Determinant weights of an exterior power.** Let `V` be a nonzero finite-dimensional
representation of `W` over an algebraically closed field of characteristic zero, with a degree
map `deg` and an element `γ` at which the weights are taken, and let `s` be a composition series of
`V` with composition factors `A_1, …, A_t`. Assume that every `A_i` and every simple constituent of
`⋀^r V` has finite geometric determinant. Then

* every simple constituent `Q` of `⋀^r V` has determinant weight `T.sum` for a sub-multiset `T` of
  size `r` of the rank-counted constituent weights (in which `dw(A_i)` occurs `dim A_i` times);
* conversely, every such sum `T.sum` is the determinant weight of some simple constituent.

Neither `V` nor `⋀^r V` is assumed semisimple. -/
theorem exteriorPower_detWeight [IsAlgClosed k] [CharZero k] [FiniteDimensional k V]
    [Nontrivial V] (χ : RealCharacter k) (deg : W →* Multiplicative ℤ) (γ : W)
    (s : ρ.CompositionSeries) (r : ℕ) (hdetA : ∀ i, (s.factor i).HasFiniteGeometricDet deg)
    (hdet : ∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      (S.subquotient U).HasFiniteGeometricDet deg) :
    (∀ U S : Subrepresentation (ρ.exteriorPower r), (S.subquotient U).IsIrreducible →
      ∃ T ≤ s.weightMultiset χ γ, Multiset.card T = r ∧
        (S.subquotient U).detWeight χ γ = T.sum) ∧
    ∀ T ≤ s.weightMultiset χ γ, Multiset.card T = r →
      ∃ U S : Subrepresentation (ρ.exteriorPower r), U < S ∧ (S.subquotient U).IsIrreducible ∧
        (S.subquotient U).detWeight χ γ = T.sum :=
  have := s.nontrivial_semisimplification
  exteriorPower_detWeight_of_constituentsLE χ deg γ r (X := s.semisimplification)
    (directSumSummand fun i ↦ s.factor i) s.isIrreducible_directSumSummand
    (fun i ↦ (directSumSummandEquiv (fun i ↦ s.factor i) i).hasFiniteGeometricDet_iff.2 (hdetA i))
    s.isInternal_semisimplification (s.weightMultiset_directSumSummand χ γ)
    (s.constituentsLE_exteriorPower_semisimplification r)
    (s.constituentsLE_exteriorPower_semisimplification' r) hdet
end Representation.CompositionSeries
