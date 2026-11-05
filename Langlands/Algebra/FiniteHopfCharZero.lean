import Langlands.Algebra.FiniteHopfConvolutionPower
import Langlands.Algebra.ArtinianReducedCriterion
import Langlands.GroupScheme.Lie.SubgroupEqualityAlgebra
import Mathlib.Algebra.DualNumber
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Finite commutative Hopf algebras in characteristic zero are reduced -/

noncomputable section

open WithConv
open scoped TensorProduct

namespace Langlands.FiniteHopfCharZero

section Derivation

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

/-- In characteristic zero a derivation preserves nilpotent elements. -/
theorem derivation_isNilpotent (D : Derivation k A A) {a : A}
    (ha : IsNilpotent a) : IsNilpotent (D a) := by
  obtain ⟨n, hn⟩ := ha
  induction n generalizing a with
  | zero =>
    have hone : (1 : A) = 0 := by simpa using hn
    have hz : a = 0 := by rw [← mul_one a, hone, mul_zero]
    rw [hz, map_zero]
    exact IsNilpotent.zero
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      have hz : a = 0 := by simpa using hn
      rw [hz, map_zero]
      exact IsNilpotent.zero
    have hp : a ^ n * D a = 0 := by
      have h := congrArg D hn
      rw [D.leibniz_pow, map_zero, Nat.succ_sub_one, smul_eq_mul] at h
      have hs : ((n + 1 : ℕ) : k) • (a ^ n * D a) = 0 := by
        simpa only [Nat.cast_smul_eq_nsmul] using h
      exact (smul_eq_zero.mp hs).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    have hprod : (a * D a) ^ n = 0 := by
      calc
        (a * D a) ^ n = a ^ n * (D a * (D a) ^ (n - 1)) := by
          rw [mul_pow, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
        _ = (a ^ n * D a) * (D a) ^ (n - 1) := by ring
        _ = 0 := by rw [hp, zero_mul]
    have hDprod := ih hprod
    have hother : IsNilpotent (a * D (D a)) :=
      (Commute.all _ _).isNilpotent_mul_right ⟨n + 1, hn⟩
    have hsq : IsNilpotent ((D a) ^ 2) := by
      convert (Commute.all _ _).isNilpotent_sub hDprod hother using 1
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    exact hsq.of_pow

end Derivation

section DualNumbers

variable {k : Type*} [Field k]
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- Change both coefficients of a dual number. -/
def dualMap (f : A →ₐ[k] B) : DualNumber A →ₐ[k] DualNumber B where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst + y.fst) = f x.fst + f y.fst
      exact map_add f _ _
    · change f (x.snd + y.snd) = f x.snd + f y.snd
      exact map_add f _ _
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst * y.fst) = f x.fst * f y.fst
      exact map_mul f _ _
    · change f (x.fst * y.snd + x.snd * y.fst) =
        f x.fst * f y.snd + f x.snd * f y.fst
      simp only [map_add, map_mul]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · change f (algebraMap k A c) = algebraMap k B c
      exact f.commutes c
    · change f 0 = 0
      exact map_zero f

@[simp] theorem dualMap_fst (f : A →ₐ[k] B) (x : DualNumber A) :
    (dualMap f x).fst = f x.fst := rfl

@[simp] theorem dualMap_snd (f : A →ₐ[k] B) (x : DualNumber A) :
    (dualMap f x).snd = f x.snd := rfl

@[simp] theorem fst_comp_dualMap (f : A →ₐ[k] B) :
    (TrivSqZeroExt.fstHom k B B).comp (dualMap f) =
      f.comp (TrivSqZeroExt.fstHom k A A) := rfl

@[simp] theorem dualMap_comp_inl (f : A →ₐ[k] B) :
    (dualMap f).comp (TrivSqZeroExt.inlAlgHom k A A) =
      (TrivSqZeroExt.inlAlgHom k B B).comp f := by
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · rfl
  · change f 0 = 0
    exact map_zero f

@[simp] theorem dualMap_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := rfl

@[simp] theorem dualMap_id : dualMap (AlgHom.id k A) = AlgHom.id k (DualNumber A) := rfl

/-- A linear form with the Leibniz rule at a point gives a dual-number lift. -/
def tangentLift (φ : A →ₐ[k] k) (d : A →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = φ a * d b + φ b * d a) :
    A →ₐ[k] DualNumber k := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [map_one, one_mul] at h
    linear_combination -h
  refine {
    toFun := fun a => ⟨φ a, d a⟩
    map_zero' := by ext <;> simp
    map_one' := by ext <;> simp [hd1]
    map_add' := fun a b => by
      apply TrivSqZeroExt.ext
      · exact map_add φ a b
      · exact map_add d a b
    map_mul' := fun a b => by
      apply TrivSqZeroExt.ext
      · exact map_mul φ a b
      · change d (a * b) = φ a * d b + d a * φ b
        rw [hd, mul_comm (φ b) (d a)]
    commutes' := fun c => ?_ }
  apply TrivSqZeroExt.ext
  · exact φ.commutes c
  · change d (algebraMap k A c) = 0
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero]

end DualNumbers

section HopfPoints

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

abbrev pointMap (f : A →ₐ[k] B) : WithConv (H →ₐ[k] A) →* WithConv (H →ₐ[k] B) :=
  FiniteHopfConvolutionPower.postcomp f

@[simp] theorem pointMap_comp (f : A →ₐ[k] B) (g : B →ₐ[k] C)
    (x : WithConv (H →ₐ[k] A)) :
    pointMap g (pointMap f x) = pointMap (g.comp f) x := rfl

@[simp] theorem pointMap_id (x : WithConv (H →ₐ[k] A)) :
    pointMap (AlgHom.id k A) x = x := by
  apply WithConv.ext
  exact AlgHom.id_comp _

abbrev constant : WithConv (H →ₐ[k] A) →* WithConv (H →ₐ[k] DualNumber A) :=
  pointMap (TrivSqZeroExt.inlAlgHom k A A)

abbrev reduction : WithConv (H →ₐ[k] DualNumber A) →* WithConv (H →ₐ[k] A) :=
  pointMap (TrivSqZeroExt.fstHom k A A)

@[simp] theorem reduction_constant (x : WithConv (H →ₐ[k] A)) :
    reduction (constant x) = x := by
  rw [constant, reduction, pointMap_comp]
  exact pointMap_id x

@[simp] theorem reduction_dualMap (f : A →ₐ[k] B)
    (x : WithConv (H →ₐ[k] DualNumber A)) :
    reduction (pointMap (dualMap f) x) = pointMap f (reduction x) := by
  rw [reduction, pointMap_comp, fst_comp_dualMap, ← pointMap_comp]

@[simp] theorem dualMap_constant (f : A →ₐ[k] B)
    (x : WithConv (H →ₐ[k] A)) :
    pointMap (dualMap f) (constant x) = constant (pointMap f x) := by
  rw [constant, pointMap_comp, dualMap_comp_inl, ← pointMap_comp]

/-- A tangent vector at a rational point extends to a derivation on a Hopf algebra. -/
theorem exists_derivation_evaluating (φ : H →ₐ[k] k) (d : H →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = φ a * d b + φ b * d a) :
    ∃ D : Derivation k H H, ∀ a, φ (D a) = d a := by
  let F : WithConv (H →ₐ[k] DualNumber k) := toConv (tangentLift φ d hd)
  let u : WithConv (H →ₐ[k] H) := toConv (AlgHom.id k H)
  let b : k →ₐ[k] H := Algebra.ofId k H
  let v : WithConv (H →ₐ[k] k) := toConv (φ.comp (HopfAlgebra.antipodeAlgHom k H))
  have hpinv : pointMap φ (toConv (AlgHom.id k H))⁻¹ = v := by
    apply WithConv.ext
    exact AlgHom.ext fun a => rfl
  have hpid : pointMap φ (toConv (AlgHom.id k H)) = toConv φ := by
    apply WithConv.ext
    exact AlgHom.ext fun a => rfl
  have hv : v * toConv φ = 1 := by
    have h := congrArg (pointMap φ)
      (inv_mul_cancel (toConv (AlgHom.id k H)))
    simpa only [map_mul, map_one, hpinv, hpid] using h
  have hvr : toConv φ * v = 1 := by
    have h := congrArg (pointMap φ)
      (mul_inv_cancel (toConv (AlgHom.id k H)))
    simpa only [map_mul, map_one, hpinv, hpid] using h
  let t := constant v * F
  let L : WithConv (H →ₐ[k] DualNumber H) :=
    constant u * pointMap (dualMap b) t
  have hF : reduction F = toConv φ := rfl
  have ht : reduction t = 1 := by
    simp only [t, map_mul, reduction_constant, hF, hv]
  have hL : reduction L = u := by
    simp only [L, map_mul, reduction_constant, reduction_dualMap, ht, map_one, mul_one]
  have hφb : φ.comp b = AlgHom.id k k := by ext
  have hbu : pointMap φ u = toConv φ := rfl
  have heval : pointMap (dualMap φ) L = F := by
    dsimp only [L]
    rw [map_mul, dualMap_constant, hbu, pointMap_comp, dualMap_comp,
      hφb, dualMap_id, pointMap_id]
    change constant (toConv φ) * (constant v * F) = F
    calc
      _ = (constant (toConv φ) * constant v) * F :=
        (mul_assoc (constant (toConv φ)) (constant v) F).symm
      _ = constant (toConv φ * v) * F := by rw [map_mul]
      _ = F := by
        rw [hvr, map_one]
        exact one_mul F
  have hfst (a : H) : (ofConv L a).fst = a :=
    DFunLike.congr_fun (congrArg ofConv hL) a
  let D₀ : H →ₗ[k] H :=
    ((TrivSqZeroExt.sndHom H H).restrictScalars k).comp (ofConv L).toLinearMap
  have hD₀ (a : H) : D₀ a = (ofConv L a).snd := rfl
  let D : Derivation k H H := Derivation.mk' D₀ (by
    intro a c
    change (ofConv L (a * c)).snd = a * (ofConv L c).snd + c * (ofConv L a).snd
    rw [map_mul, DualNumber.snd_mul, hfst, hfst, mul_comm (ofConv L a).snd c])
  refine ⟨D, fun a => ?_⟩
  have h := DFunLike.congr_fun (congrArg ofConv heval) a
  exact congrArg TrivSqZeroExt.snd h

end HopfPoints

section Reducedness

variable {k H : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]

/-- A tangent derivation at any rational point annihilates every nilpotent element. -/
theorem tangent_eq_zero_of_isNilpotent (φ : H →ₐ[k] k) (d : H →ₗ[k] k)
    (hd : ∀ a b, d (a * b) = φ a * d b + φ b * d a)
    {a : H} (ha : IsNilpotent a) : d a = 0 := by
  obtain ⟨D, hD⟩ := exists_derivation_evaluating φ d hd
  rw [← hD a]
  exact ((derivation_isNilpotent D ha).map φ).eq_zero

/-- The nilradical lies in the square of the ideal of any rational point. -/
theorem nilradical_le_point_ker_sq (φ : H →ₐ[k] k) :
    nilradical H ≤ RingHom.ker φ ^ 2 := by
  intro a ha
  by_contra hsq
  have hφ : a ∈ RingHom.ker φ := (IsNilpotent.map (show IsNilpotent a from ha) φ).eq_zero
  obtain ⟨d, hda, hd⟩ :=
    Langlands.GroupScheme.Lie.SubgroupEquality.exists_leibniz_ne_zero φ hφ hsq
  exact hda (tangent_eq_zero_of_isNilpotent φ d hd ha)

variable [Module.Finite k H]

/-- Every maximal ideal of a finite algebra over an algebraically closed field is a point. -/
theorem exists_point_ker_eq [IsAlgClosed k] (m : MaximalSpectrum H) :
    ∃ φ : H →ₐ[k] k, RingHom.ker φ = m.asIdeal := by
  let : m.asIdeal.IsMaximal := m.isMaximal
  let : Field (H ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let ψ : H ⧸ m.asIdeal →ₐ[k] k := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ k m.asIdeal), ?_⟩
  change RingHom.ker (ψ.toRingHom.comp (Ideal.Quotient.mk m.asIdeal)) = m.asIdeal
  rw [RingHom.ker_comp_of_injective _ ψ.injective, Ideal.mk_ker]

/-- Finite commutative Hopf algebras over algebraically closed characteristic-zero fields
are reduced. -/
theorem isReduced_of_isAlgClosed [IsAlgClosed k] : IsReduced H := by
  let : IsArtinianRing H := isArtinian_of_tower k inferInstance
  apply ArtinianReducedCriterion.isReduced_of_nilradical_le_maximal_sq
  intro m
  obtain ⟨φ, hφ⟩ := exists_point_ker_eq (k := k) m
  rw [← hφ]
  exact nilradical_le_point_ker_sq φ

include k in
/-- A finite commutative Hopf algebra over any characteristic-zero field is reduced. -/
theorem isReduced : IsReduced H := by
  let : IsReduced (AlgebraicClosure k ⊗[k] H) :=
    isReduced_of_isAlgClosed (k := AlgebraicClosure k) (H := AlgebraicClosure k ⊗[k] H)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : H →ₐ[k] AlgebraicClosure k ⊗[k] H)
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))

end Reducedness

end Langlands.FiniteHopfCharZero
