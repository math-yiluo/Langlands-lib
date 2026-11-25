/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.LocalPoints
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# The bracket on the Lie algebra of a group scheme over a field

Let `G` be a group scheme over a field `k`. Its tangent vectors are the points `v` of `G` with
values in the dual numbers `k[ε]` reducing to the identity; such a point is determined by the
homomorphism `v^♯ : 𝒪_{G,1} → k[ε]`, `a ↦ a(1) + ε D_v(a)` on the local ring at the identity
(`AlgebraicGeometry.GrpObj.kerHom`). For an element `m` of square zero in the maximal ideal of a
local `k`-algebra `A` with residue field `k`, substituting `ε ↦ m` gives the point `v^{(m)}` of `G`
with values in `A`, with `(v^{(m)})^♯(a) = a(1) + m D_v(a)`.

All computations go through these points, using only that `G(A)` is a group functorially in `A`:

* the product `v^{(m)} w^{(n)}` has `(v^{(m)} w^{(n)})^♯ = a(1) + m D_v + n D_w + mn C(v, w)` for a
  fixed `C(v, w)`, the `εδ`-coefficient of `v_ε w_δ` over `k[ε][δ] = k[ε, δ]/(ε², δ²)`
  (`kerHom_tangentMap_mul_tangentMap`); in particular the group law on tangent vectors is the
  addition of the `D_v`;
* if `m` kills the maximal ideal, `u^{(m)}` is central and `(u^{(m)} q)^♯ = q^♯ + m D_u`
  (`kerHom_tangentMap_mul`);
* the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `[v, w]^{(εδ)}` for a unique tangent vector `[v, w]`, the
  *bracket* (`tangentBracket`), with `D_{[v, w]} = C(v, w) - C(w, v)`.

Substituting into the bracket gives `[v^{(m)}, w^{(n)}] = [v, w]^{(mn)}`. From this the bracket is
biadditive and alternating, and the Hall–Witt identity over `k[α][β][γ]` gives the Jacobi
identity.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt IsLocalRing
open scoped MonObj commutatorElement

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k]

/-! ### Test rings -/

section TestRings

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The residue map `A[τ] → k`, `x + yτ ↦ π(x)`, of the dual numbers over a `k`-algebra with a
residue map `π`. -/
def dualAug (π : A →ₐ[k] k) : DualNumber A →ₐ[k] k :=
  π.comp (fstHom k A A)

instance (π : A →ₐ[k] k) [IsLocalHom π.toRingHom] : IsLocalHom (dualAug π).toRingHom := by
  have : IsLocalHom (fstHom k A A).toRingHom := ⟨fun _ ↦ isUnit_iff_isUnit_fst.mpr⟩
  exact RingHom.isLocalHom_comp π.toRingHom (fstHom k A A).toRingHom

@[simp]
theorem dualAug_apply (π : A →ₐ[k] k) (x : DualNumber A) : dualAug π x = π x.fst :=
  rfl

end TestRings

/-- The residue map of `k[ε]`. -/
abbrev aug₁ : DualNumber k →ₐ[k] k :=
  fstHom k k k

/-- The residue map of `k[ε][δ] = k[ε, δ]/(ε², δ²)`. -/
abbrev aug₂ : DualNumber (DualNumber k) →ₐ[k] k :=
  dualAug aug₁

/-- The element `ε` of `k[ε][δ]`. -/
abbrev eps₂ : DualNumber (DualNumber k) :=
  inl (inr 1)

/-- The element `δ` of `k[ε][δ]`. -/
abbrev del₂ : DualNumber (DualNumber k) :=
  inr 1

theorem eps₂_mul_self : (eps₂ : DualNumber (DualNumber k)) * eps₂ = 0 := by
  ext <;> simp

theorem del₂_mul_self : (del₂ : DualNumber (DualNumber k)) * del₂ = 0 := by
  ext <;> simp

theorem eps₂_mul_del₂_mul_self :
    (eps₂ * del₂ : DualNumber (DualNumber k)) * (eps₂ * del₂) = 0 := by
  ext <;> simp

@[simp]
theorem aug₂_eps₂ : aug₂ (eps₂ : DualNumber (DualNumber k)) = 0 := by
  simp

@[simp]
theorem aug₂_del₂ : aug₂ (del₂ : DualNumber (DualNumber k)) = 0 := by
  simp

/-- The `k`-algebra homomorphism `k[ε][δ] → A`, `ε ↦ m`, `δ ↦ n`, for elements of square zero. -/
def lift₂ {A : Type u} [CommRing A] [Algebra k A] (m n : A) (hm : m * m = 0) (hn : n * n = 0) :
    DualNumber (DualNumber k) →ₐ[k] A :=
  DualNumber.lift ⟨(DualNumber.liftElem m hm, n), hn, fun _ ↦ Commute.all _ _⟩

theorem lift₂_apply {A : Type u} [CommRing A] [Algebra k A] (m n : A) (hm : m * m = 0)
    (hn : n * n = 0) (x : DualNumber (DualNumber k)) :
    lift₂ m n hm hn x = DualNumber.liftElem m hm x.fst + DualNumber.liftElem m hm x.snd * n :=
  rfl

variable (G : Over (Spec (.of k))) [GrpObj G]

/-! ### Tangent vectors and their substitutions -/

variable {G}

/-- The `ε`-coefficient `D_v : 𝒪_{G,1} → k` of a tangent vector `v`, so that
`v^♯(a) = a(1) + ε D_v(a)`. -/
noncomputable def tangentCoeff (v : pointsKer G aug₁) (a : stalkOne G) : k :=
  (kerHom v a).snd

theorem kerHom_tangent (v : pointsKer G aug₁) (a : stalkOne G) :
    kerHom v a = inl (counit G a) + inr (tangentCoeff v a) := by
  ext
  · simpa using kerHom_apply_of_mem_ker v a
  · simp [tangentCoeff]

theorem tangent_ext {v w : pointsKer G aug₁} (h : ∀ a, tangentCoeff v a = tangentCoeff w a) :
    v = w :=
  kerHom_injective (RingHom.ext fun a ↦ by rw [kerHom_tangent, kerHom_tangent, h])

variable {A : Type u} [CommRing A] [Algebra k A] [IsLocalRing A] {π : A →ₐ[k] k}
  [IsLocalHom π.toRingHom]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem aug_comp_liftElem (m : A) (hm : m * m = 0) (hπ : π m = 0) :
    π.comp (DualNumber.liftElem m hm) = aug₁ := by
  ext
  simp [DualNumber.liftElem_apply, hπ]

/-- The point `v^{(m)}` of `G` with values in `A` obtained from a tangent vector `v` by the
substitution `ε ↦ m`, for `m` of square zero in the maximal ideal. -/
noncomputable def tangentMap (m : A) (hm : m * m = 0) (hπ : π m = 0) :
    pointsKer G aug₁ →* pointsKer G π :=
  kerMap (DualNumber.liftElem m hm) (aug_comp_liftElem m hm hπ)

theorem kerHom_tangentMap (m : A) (hm : m * m = 0) (hπ : π m = 0) (v : pointsKer G aug₁)
    (a : stalkOne G) :
    kerHom (tangentMap m hm hπ v) a =
      algebraMap k A (counit G a) + algebraMap k A (tangentCoeff v a) * m := by
  rw [tangentMap, kerHom_kerMap]
  simp [kerHom_tangent, DualNumber.liftElem_apply]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem liftElem_comp_eq {B : Type u} [CommRing B] [Algebra k B] (ψ : A →ₐ[k] B) (m : A)
    (hm : m * m = 0) (m' : B) (hm' : m' * m' = 0) (h : ψ m = m') :
    ψ.comp (DualNumber.liftElem m hm) = DualNumber.liftElem (R := k) m' hm' := by
  ext
  simp [DualNumber.liftElem_apply, h]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
/-- Base change of a substituted tangent vector is the substitution of the image. -/
theorem kerMap_tangentMap {B : Type u} [CommRing B] [Algebra k B] [IsLocalRing B]
    {πB : B →ₐ[k] k} (ψ : A →ₐ[k] B) (hψ : πB.comp ψ = π) (m : A) (hm : m * m = 0)
    (hπ : π m = 0) (m' : B) (hm' : m' * m' = 0) (hπ' : πB m' = 0) (h : ψ m = m')
    (v : pointsKer G aug₁) :
    kerMap ψ hψ (tangentMap m hm hπ v) = tangentMap m' hm' hπ' v := by
  rw [tangentMap, tangentMap, kerMap_kerMap]
  exact congrArg (· v) (kerMap_congr (liftElem_comp_eq ψ m hm m' hm' h)
    (by rw [← AlgHom.comp_assoc, hψ]; exact aug_comp_liftElem m hm hπ)
    (aug_comp_liftElem m' hm' hπ'))

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
/-- Substituting `ε ↦ 0` gives the identity point. -/
theorem tangentMap_zero (v : pointsKer G aug₁) :
    tangentMap (π := π) (0 : A) (mul_zero 0) (map_zero π) v = 1 :=
  kerMap_eq_one _ (by ext; simp [DualNumber.liftElem_apply]) _ v

theorem inr_one_mul_self : (inr 1 : DualNumber k) * inr 1 = 0 := by
  ext <;> simp

/-- Substituting `ε ↦ ε` is the identity. -/
theorem tangentMap_inr_one (v : pointsKer G aug₁) :
    tangentMap (A := DualNumber k) (π := aug₁) (inr 1) inr_one_mul_self (by simp) v = v := by
  rw [tangentMap, kerMap_congr (ψ' := AlgHom.id k (DualNumber k)) (by
      ext <;> simp [DualNumber.liftElem_apply, DualNumber.fst_eps, DualNumber.snd_eps,
        algebraMap_eq_inl]) _ (AlgHom.comp_id _), kerMap_id]

/-- The point `v_ε` of `G` over `k[ε][δ]` of a tangent vector `v`. -/
noncomputable abbrev tangentEps (v : pointsKer G aug₁) : pointsKer G (aug₂ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber k)) (π := aug₂) eps₂ eps₂_mul_self aug₂_eps₂ v

/-- The point `v_δ` of `G` over `k[ε][δ]` of a tangent vector `v`. -/
noncomputable abbrev tangentDel (v : pointsKer G aug₁) : pointsKer G (aug₂ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber k)) (π := aug₂) del₂ del₂_mul_self aug₂_del₂ v

/-- The `εδ`-coefficient `C(v, w)` of `v_ε w_δ` over `k[ε][δ]`. -/
noncomputable def mulCoeff (v w : pointsKer G aug₁) (a : stalkOne G) : k :=
  (kerHom (tangentEps v * tangentDel w) a).snd.snd

/-- `δ ↦ 0`: the map `k[ε][δ] → k[ε]`. -/
abbrev fst₂ : DualNumber (DualNumber k) →ₐ[k] DualNumber k :=
  fstHom k (DualNumber k) (DualNumber k)

/-- `ε ↦ 0, δ ↦ ε`: the map `k[ε][δ] → k[ε]`. -/
abbrev rho₂ : DualNumber (DualNumber k) →ₐ[k] DualNumber k :=
  lift₂ 0 (inr 1) (mul_zero 0) inr_one_mul_self

theorem aug₁_comp_fst₂ : aug₁.comp fst₂ = (aug₂ : DualNumber (DualNumber k) →ₐ[k] k) :=
  rfl

theorem aug₁_comp_rho₂ : aug₁.comp rho₂ = (aug₂ : DualNumber (DualNumber k) →ₐ[k] k) := by
  refine AlgHom.ext fun x ↦ ?_
  simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem aug_comp_lift₂ (m n : A) (hm : m * m = 0) (hn : n * n = 0) (hπm : π m = 0)
    (hπn : π n = 0) : π.comp (lift₂ m n hm hn) = aug₂ := by
  refine AlgHom.ext fun x ↦ ?_
  simp [lift₂_apply, DualNumber.liftElem_apply, hπm, hπn]

theorem kerMap_fst₂_tangentEps_mul (v w : pointsKer G aug₁) :
    kerMap fst₂ aug₁_comp_fst₂ (tangentEps v * tangentDel w) = v := by
  rw [map_mul, kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp) (by simp),
    kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _) (by simp), tangentMap_zero,
    mul_one, tangentMap_inr_one]

theorem kerMap_rho₂_tangentEps_mul (v w : pointsKer G aug₁) :
    kerMap rho₂ aug₁_comp_rho₂ (tangentEps v * tangentDel w) = w := by
  rw [map_mul, kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _)
      (by simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]),
    kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp)
      (by simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]), tangentMap_zero,
    one_mul, tangentMap_inr_one]

theorem kerHom_mul_fst (v w : pointsKer G aug₁) (a : stalkOne G) :
    (kerHom (tangentEps v * tangentDel w) a).fst = kerHom v a := by
  have h := kerHom_kerMap fst₂ aug₁_comp_fst₂ (tangentEps v * tangentDel w)
  rw [kerMap_fst₂_tangentEps_mul] at h
  exact (congrArg (· a) h).symm

theorem kerHom_mul_snd_fst (v w : pointsKer G aug₁) (a : stalkOne G) :
    (kerHom (tangentEps v * tangentDel w) a).snd.fst = tangentCoeff w a := by
  have h := kerHom_kerMap rho₂ aug₁_comp_rho₂ (tangentEps v * tangentDel w)
  rw [kerMap_rho₂_tangentEps_mul] at h
  have h' := congrArg (fun f ↦ (f a).snd) h
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl] at h'
  rw [tangentCoeff, h']
  simp

/-- **The product formula.** For `m, n` of square zero in the maximal ideal of `A`,
`(v^{(m)} w^{(n)})^♯ = a(1) + m D_v + n D_w + mn C(v, w)`. -/
theorem kerHom_tangentMap_mul_tangentMap (m n : A) (hm : m * m = 0) (hn : n * n = 0)
    (hπm : π m = 0) (hπn : π n = 0) (v w : pointsKer G aug₁) (a : stalkOne G) :
    kerHom (tangentMap m hm hπm v * tangentMap n hn hπn w) a =
      algebraMap k A (counit G a) + algebraMap k A (tangentCoeff v a) * m +
        algebraMap k A (tangentCoeff w a) * n + algebraMap k A (mulCoeff v w a) * (m * n) := by
  have e : tangentMap m hm hπm v * tangentMap n hn hπn w =
      kerMap (A := DualNumber (DualNumber k)) (πA := aug₂) (πB := π) (lift₂ m n hm hn)
        (aug_comp_lift₂ m n hm hn hπm hπn) (tangentEps v * tangentDel w) := by
    rw [map_mul, kerMap_tangentMap _ _ _ _ _ m hm hπm (by simp [lift₂_apply,
      DualNumber.liftElem_apply]), kerMap_tangentMap _ _ _ _ _ n hn hπn (by simp [lift₂_apply,
      DualNumber.liftElem_apply])]
  rw [e, kerHom_kerMap, RingHom.comp_apply]
  have h1 := kerHom_mul_fst v w a
  have h2 := kerHom_mul_snd_fst v w a
  have h3 : (kerHom (tangentEps v * tangentDel w) a).snd.snd = mulCoeff v w a := rfl
  generalize kerHom (tangentEps v * tangentDel w) a = X at h1 h2 h3
  change (lift₂ m n hm hn) X = _
  rw [lift₂_apply, DualNumber.liftElem_apply, DualNumber.liftElem_apply, h1, h2, h3,
    kerHom_tangent]
  simp only [fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr, zero_add]
  ring
/-! ### Points killing the maximal ideal are central -/

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem dualAug_comp_inlAlgHom : (dualAug π).comp (inlAlgHom k A A) = π := by
  ext
  simp

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem dualAug_inr_one : dualAug π (inr 1 : DualNumber A) = 0 := by
  simp

omit [IsLocalRing A] in
theorem inr_one_mul_self' : (inr 1 : DualNumber A) * inr 1 = 0 := by
  ext <;> simp

/-- The map `A[τ] → k[ε]`, `x + yτ ↦ π(x) + π(y) ε`. -/
def resDual (π : A →ₐ[k] k) : DualNumber A →ₐ[k] DualNumber k :=
  DualNumber.lift ⟨((Algebra.ofId k (DualNumber k)).comp π, inr 1), inr_one_mul_self,
    fun _ ↦ Commute.all _ _⟩

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem resDual_apply (x : DualNumber A) :
    resDual π x = inl (π x.fst) + inr (π x.snd) := by
  rw [resDual, DualNumber.lift_apply_apply]
  ext <;> simp [algebraMap_eq_inl]

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem aug₁_comp_resDual : aug₁.comp (resDual π) = dualAug π := by
  refine AlgHom.ext fun x ↦ ?_
  simp [resDual_apply]

/-- The map `A[τ] → A`, `τ ↦ m`. -/
def substDual (m : A) (hm : m * m = 0) : DualNumber A →ₐ[k] A :=
  DualNumber.lift ⟨(AlgHom.id k A, m), hm, fun _ ↦ Commute.all _ _⟩

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem substDual_apply (m : A) (hm : m * m = 0) (x : DualNumber A) :
    substDual (k := k) m hm x = x.fst + x.snd * m :=
  rfl

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem aug_comp_substDual (m : A) (hm : m * m = 0) (hπ : π m = 0) :
    π.comp (substDual m hm) = dualAug π := by
  refine AlgHom.ext fun x ↦ ?_
  simp [substDual_apply, hπ]

/-- A point `P` over `A[τ]` whose reduction `τ ↦ 0` is `q` and whose residue in `k[ε]` is `u`
becomes `q + m D_u` after the substitution `τ ↦ m`, when `m` kills the maximal ideal. -/
theorem kerHom_kerMap_substDual (m : A) (hπm : π m = 0) (hm : ∀ x, π x = 0 → m * x = 0)
    (P : pointsKer G (dualAug π)) (q : pointsKer G π) (u : pointsKer G aug₁)
    (hq : kerMap (πA := dualAug π) (πB := π) (fstHom k A A) rfl P = q)
    (hu : kerMap (resDual π) aug₁_comp_resDual P = u)
    (a : stalkOne G) :
    kerHom (kerMap (substDual m (hm m hπm)) (aug_comp_substDual m (hm m hπm) hπm) P) a =
      kerHom q a + algebraMap k A (tangentCoeff u a) * m := by
  rw [kerHom_kerMap, RingHom.comp_apply]
  have h1 : (kerHom P a).fst = kerHom q a := by
    rw [← hq, kerHom_kerMap]
    rfl
  have h2 : π (kerHom P a).snd = tangentCoeff u a := by
    rw [← hu, tangentCoeff, kerHom_kerMap, RingHom.comp_apply]
    change _ = (resDual π (kerHom P a)).snd
    simp [resDual_apply]
  generalize kerHom P a = Y at h1 h2
  change substDual m _ Y = _
  rw [substDual_apply, h1, ← h2]
  congr 1
  have : m * (Y.snd - algebraMap k A (π Y.snd)) = 0 := hm _ (by simp)
  rw [mul_sub] at this
  rw [mul_comm, sub_eq_zero.mp this, mul_comm]

/-- If `m` kills the maximal ideal, `(u^{(m)} q)^♯ = q^♯ + m D_u`. -/
theorem kerHom_tangentMap_mul (m : A) (hπm : π m = 0) (hm : ∀ x, π x = 0 → m * x = 0)
    (u : pointsKer G aug₁) (q : pointsKer G π) (a : stalkOne G) :
    kerHom (tangentMap m (hm m hπm) hπm u * q) a =
      kerHom q a + algebraMap k A (tangentCoeff u a) * m := by
  set uτ := tangentMap (A := DualNumber A) (π := dualAug π) (inr 1) inr_one_mul_self'
    dualAug_inr_one u
  set q' := kerMap (inlAlgHom k A A) dualAug_comp_inlAlgHom q
  have e : tangentMap m (hm m hπm) hπm u * q =
      kerMap (substDual m (hm m hπm)) (aug_comp_substDual m (hm m hπm) hπm) (uτ * q') := by
    rw [map_mul, kerMap_tangentMap _ _ _ _ _ m (hm m hπm) hπm (by simp [substDual_apply]),
      kerMap_kerMap]
    congr 1
    rw [kerMap_congr (ψ' := AlgHom.id k A) (by ext; simp [substDual_apply]) _
      (AlgHom.comp_id _), kerMap_id]
  rw [e]
  refine kerHom_kerMap_substDual m hπm hm _ q u ?_ ?_ a
  · rw [map_mul, kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _) (by simp),
      tangentMap_zero, one_mul, kerMap_kerMap, kerMap_congr (ψ' := AlgHom.id k A)
        (by ext; simp) _ (AlgHom.comp_id _), kerMap_id]
  · rw [map_mul, kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp)
      (by simp [resDual_apply]), tangentMap_inr_one, kerMap_kerMap,
      kerMap_eq_one _ (by ext <;> simp [resDual_apply, algebraMap_eq_inl]), mul_one]

/-- If `m` kills the maximal ideal, `(q u^{(m)})^♯ = q^♯ + m D_u`. -/
theorem kerHom_mul_tangentMap (m : A) (hπm : π m = 0) (hm : ∀ x, π x = 0 → m * x = 0)
    (u : pointsKer G aug₁) (q : pointsKer G π) (a : stalkOne G) :
    kerHom (q * tangentMap m (hm m hπm) hπm u) a =
      kerHom q a + algebraMap k A (tangentCoeff u a) * m := by
  set uτ := tangentMap (A := DualNumber A) (π := dualAug π) (inr 1) inr_one_mul_self'
    dualAug_inr_one u
  set q' := kerMap (inlAlgHom k A A) dualAug_comp_inlAlgHom q
  have e : q * tangentMap m (hm m hπm) hπm u =
      kerMap (substDual m (hm m hπm)) (aug_comp_substDual m (hm m hπm) hπm) (q' * uτ) := by
    rw [map_mul, kerMap_tangentMap _ _ _ _ _ m (hm m hπm) hπm (by simp [substDual_apply]),
      kerMap_kerMap]
    congr 1
    rw [kerMap_congr (ψ' := AlgHom.id k A) (by ext; simp [substDual_apply]) _
      (AlgHom.comp_id _), kerMap_id]
  rw [e]
  refine kerHom_kerMap_substDual m hπm hm _ q u ?_ ?_ a
  · rw [map_mul, kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _) (by simp),
      tangentMap_zero, mul_one, kerMap_kerMap, kerMap_congr (ψ' := AlgHom.id k A)
        (by ext; simp) _ (AlgHom.comp_id _), kerMap_id]
  · rw [map_mul, kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp)
      (by simp [resDual_apply]), tangentMap_inr_one, kerMap_kerMap,
      kerMap_eq_one _ (by ext <;> simp [resDual_apply, algebraMap_eq_inl]), one_mul]

/-- A point `u^{(m)}` with `m` killing the maximal ideal is central. -/
theorem commute_tangentMap (m : A) (hπm : π m = 0) (hm : ∀ x, π x = 0 → m * x = 0)
    (u : pointsKer G aug₁) (q : pointsKer G π) :
    Commute (tangentMap m (hm m hπm) hπm u) q :=
  kerHom_injective (RingHom.ext fun a ↦ by
    rw [kerHom_tangentMap_mul, kerHom_mul_tangentMap])
/-! ### The bracket -/

theorem eps₂_mul_del₂_mul (x : DualNumber (DualNumber k)) (hx : aug₂ x = 0) :
    eps₂ * del₂ * x = 0 := by
  have h : x.fst.fst = 0 := hx
  ext <;> simp [h]

theorem aug₂_eps₂_mul_del₂ : aug₂ (eps₂ * del₂ : DualNumber (DualNumber k)) = 0 := by
  simp

/-- The map `k[η] → k[ε][δ]`, `η ↦ εδ`. -/
abbrev mul₂ : DualNumber k →ₐ[k] DualNumber (DualNumber k) :=
  DualNumber.liftElem (eps₂ * del₂) eps₂_mul_del₂_mul_self

theorem mul₂_injective : Function.Injective (mul₂ (k := k)) := by
  intro x y h
  have h1 := congrArg (fun z : DualNumber (DualNumber k) ↦ z.fst.fst) h
  have h2 := congrArg (fun z : DualNumber (DualNumber k) ↦ z.snd.snd) h
  exact TrivSqZeroExt.ext (by simpa [DualNumber.liftElem_apply, algebraMap_eq_inl'] using h1)
    (by simpa [DualNumber.liftElem_apply, algebraMap_eq_inl'] using h2)

theorem aug₂_comp_mul₂ : aug₂.comp mul₂ = (aug₁ : DualNumber k →ₐ[k] k) :=
  aug_comp_liftElem _ _ aug₂_eps₂_mul_del₂

/-- The point `u^{(εδ)}` of `G` over `k[ε][δ]`. -/
noncomputable abbrev tangentMul (u : pointsKer G aug₁) : pointsKer G (aug₂ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber k)) (π := aug₂) (eps₂ * del₂)
    eps₂_mul_del₂_mul_self aug₂_eps₂_mul_del₂ u

theorem tangentMul_injective : Function.Injective (tangentMul (G := G)) :=
  kerMap_injective _ _ mul₂_injective

theorem kerMap_fst₂_commutator (v w : pointsKer G aug₁) :
    kerMap fst₂ aug₁_comp_fst₂ ⁅tangentEps v, tangentDel w⁆ = 1 := by
  rw [map_commutatorElement, kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp)
      (by simp), kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _) (by simp),
    tangentMap_zero, commutatorElement_one_right]

theorem kerMap_rho₂_commutator (v w : pointsKer G aug₁) :
    kerMap rho₂ aug₁_comp_rho₂ ⁅tangentEps v, tangentDel w⁆ = 1 := by
  rw [map_commutatorElement, kerMap_tangentMap _ _ _ _ _ 0 (mul_zero 0) (map_zero _)
      (by simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]),
    kerMap_tangentMap _ _ _ _ _ (inr 1) inr_one_mul_self (by simp)
      (by simp [lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl]),
    tangentMap_zero, commutatorElement_one_left]

/-- A point over `k[ε][δ]` trivial for `δ = 0` and for `ε = 0` has the form `a(1) + εδ B(a)`. -/
theorem kerHom_eq_mul₂ (c : pointsKer G (aug₂ (k := k))) (h₁ : kerMap fst₂ aug₁_comp_fst₂ c = 1)
    (h₂ : kerMap rho₂ aug₁_comp_rho₂ c = 1) (a : stalkOne G) :
    kerHom c a = mul₂ (inl (counit G a) + inr (kerHom c a).snd.snd) := by
  have e₁ : (kerHom c a).fst = inl (counit G a) := by
    have h := kerHom_kerMap fst₂ aug₁_comp_fst₂ c
    rw [h₁, kerHom_one] at h
    have := congrArg (· a) h
    simpa [algebraMap_eq_inl] using this.symm
  have e₂ : (kerHom c a).snd.fst = 0 := by
    have h := kerHom_kerMap rho₂ aug₁_comp_rho₂ c
    rw [h₂, kerHom_one] at h
    have h' := congrArg (fun f ↦ (f a).snd) h
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      lift₂_apply, DualNumber.liftElem_apply, algebraMap_eq_inl] at h'
    simpa using h'.symm
  generalize kerHom c a = X at e₁ e₂ ⊢
  ext
  · simp [DualNumber.liftElem_apply, algebraMap_eq_inl', e₁]
  · simp [DualNumber.liftElem_apply, algebraMap_eq_inl', e₁]
  · simp [DualNumber.liftElem_apply, algebraMap_eq_inl', e₂]
  · simp [DualNumber.liftElem_apply, algebraMap_eq_inl']

instance : IsLocalHom (counit G) :=
  inferInstanceAs (IsLocalHom (pointStalkHom _ _).hom)

/-- A point over `k[ε][δ]` trivial for `δ = 0` and for `ε = 0` is `u^{(εδ)}` for a tangent
vector `u`. -/
theorem exists_tangentMul_eq (c : pointsKer G (aug₂ (k := k)))
    (h₁ : kerMap fst₂ aug₁_comp_fst₂ c = 1) (h₂ : kerMap rho₂ aug₁_comp_rho₂ c = 1) :
    ∃ u : pointsKer G aug₁, tangentMul u = c := by
  set f : stalkOne G → DualNumber k := fun a ↦ inl (counit G a) + inr (kerHom c a).snd.snd
  have hf (a : stalkOne G) : mul₂ (f a) = kerHom c a := (kerHom_eq_mul₂ c h₁ h₂ a).symm
  let θ : stalkOne G →+* DualNumber k :=
    { toFun := f
      map_one' := mul₂_injective (by rw [hf, map_one, map_one])
      map_mul' a b := mul₂_injective (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := mul₂_injective (by rw [hf, map_zero, map_zero])
      map_add' a b := mul₂_injective (by rw [hf, map_add, map_add, hf, hf]) }
  have hθ : aug₁.toRingHom.comp θ = counit G := RingHom.ext fun a ↦ by simp [θ, f]
  have : IsLocalHom (CommRingCat.ofHom θ).hom := by
    have : IsLocalHom (aug₁.toRingHom.comp θ) := by rw [hθ]; infer_instance
    exact isLocalHom_of_comp θ aug₁.toRingHom
  have := isLocalHom_of_comp_eq (A := DualNumber k) (B := DualNumber (DualNumber k))
    (πA := aug₁) (πB := aug₂) mul₂ aug₂_comp_mul₂
  obtain ⟨p, hp, -, hpc⟩ := exists_pointStalkHom_eq mul₂ mul₂_injective c.1
    (closedPoint_eq_onePoint c.2) (CommRingCat.ofHom θ)
    (CommRingCat.hom_ext (RingHom.ext fun a ↦ by
      change kerHom c a = mul₂ (f a)
      exact (hf a).symm))
  have hp' : p ∈ pointsKer G aug₁ := by
    rw [mem_pointsKer, ← aug₂_comp_mul₂, ← points.map_map, hpc]
    exact mem_pointsKer.1 c.2
  exact ⟨⟨p, hp'⟩, Subtype.ext hpc⟩

/-- The commutator of `v_ε` and `w_δ` is `u^{(εδ)}` for a tangent vector `u`. -/
theorem exists_tangentMul_eq_commutator (v w : pointsKer G aug₁) :
    ∃ u : pointsKer G aug₁, tangentMul u = ⁅tangentEps v, tangentDel w⁆ :=
  exists_tangentMul_eq _ (kerMap_fst₂_commutator v w) (kerMap_rho₂_commutator v w)

/-- The bracket `[v, w]` of two tangent vectors: the tangent vector `u` with
`u^{(εδ)} = v_ε w_δ v_ε⁻¹ w_δ⁻¹` over `k[ε][δ]`. -/
noncomputable def tangentBracket (v w : pointsKer G aug₁) : pointsKer G aug₁ :=
  (exists_tangentMul_eq_commutator v w).choose

theorem tangentMul_tangentBracket (v w : pointsKer G aug₁) :
    tangentMul (tangentBracket v w) = ⁅tangentEps v, tangentDel w⁆ :=
  (exists_tangentMul_eq_commutator v w).choose_spec

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem tangentMap_congr {m m' : A} (h : m = m') (hm : m * m = 0) (hπ : π m = 0)
    (hm' : m' * m' = 0) (hπ' : π m' = 0) :
    tangentMap (G := G) m hm hπ = tangentMap m' hm' hπ' := by
  subst h
  rfl

omit [IsLocalRing A] [IsLocalHom π.toRingHom] in
theorem tangentMap_apply_congr {m m' : A} (h : m = m') (hm : m * m = 0) (hπ : π m = 0)
    (hm' : m' * m' = 0) (hπ' : π m' = 0) (v : pointsKer G aug₁) :
    tangentMap m hm hπ v = tangentMap m' hm' hπ' v := by
  subst h
  rfl

omit [IsLocalHom π.toRingHom] in
/-- **Substitution into the bracket.** `[v^{(m)}, w^{(n)}] = [v, w]^{(mn)}` for `m, n` of square
zero in the maximal ideal. -/
theorem commutator_tangentMap (m n : A) (hm : m * m = 0) (hn : n * n = 0) (hπm : π m = 0)
    (hπn : π n = 0) (v w : pointsKer G aug₁) :
    ⁅tangentMap m hm hπm v, tangentMap n hn hπn w⁆ =
      tangentMap (A := A) (π := π) (m * n) (by rw [mul_mul_mul_comm, hm, zero_mul])
        (by rw [map_mul, hπm, zero_mul]) (tangentBracket v w) := by
  have h := congrArg (kerMap (A := DualNumber (DualNumber k)) (πA := aug₂) (πB := π)
    (lift₂ m n hm hn) (aug_comp_lift₂ m n hm hn hπm hπn)) (tangentMul_tangentBracket v w)
  rw [map_commutatorElement, kerMap_tangentMap (m := eps₂) (m' := m) _ _ _ _ hm hπm
      (by simp [lift₂_apply, DualNumber.liftElem_apply]),
    kerMap_tangentMap (m := del₂) (m' := n) _ _ _ _ hn hπn
      (by simp [lift₂_apply, DualNumber.liftElem_apply]),
    kerMap_tangentMap (m := eps₂ * del₂) (m' := m * n) _ _ _ _
      (by rw [mul_mul_mul_comm, hm, zero_mul]) (by rw [map_mul, hπm, zero_mul])
      (by simp [lift₂_apply, DualNumber.liftElem_apply])] at h
  exact h.symm
/-! ### The laws of the bracket -/

theorem tangentCoeff_one (a : stalkOne G) : tangentCoeff (1 : pointsKer G aug₁) a = 0 := by
  rw [tangentCoeff, kerHom_one]
  simp [algebraMap_eq_inl]

/-- The group law on tangent vectors is the addition of the `D_v`. -/
theorem tangentCoeff_mul (v w : pointsKer G aug₁) (a : stalkOne G) :
    tangentCoeff (v * w) a = tangentCoeff v a + tangentCoeff w a := by
  conv_lhs => rw [← tangentMap_inr_one v, ← tangentMap_inr_one w]
  rw [tangentCoeff, kerHom_tangentMap_mul_tangentMap]
  simp [algebraMap_eq_inl]

theorem tangent_mul_comm (v w : pointsKer G aug₁) : v * w = w * v :=
  tangent_ext fun a ↦ by rw [tangentCoeff_mul, tangentCoeff_mul, add_comm]

theorem tangentCoeff_inv (v : pointsKer G aug₁) (a : stalkOne G) :
    tangentCoeff v⁻¹ a = -tangentCoeff v a := by
  have h := tangentCoeff_mul v v⁻¹ a
  rw [mul_inv_cancel, tangentCoeff_one] at h
  linear_combination -h


theorem snd_snd_algebraMap₂ (c : k) :
    (algebraMap k (DualNumber (DualNumber k)) c).snd.snd = 0 := by
  simp [algebraMap_eq_inl']

theorem snd_snd_algebraMap₂_mul_eps₂ (c : k) :
    (algebraMap k (DualNumber (DualNumber k)) c * eps₂).snd.snd = 0 := by
  simp [algebraMap_eq_inl']

theorem snd_snd_algebraMap₂_mul_del₂ (c : k) :
    (algebraMap k (DualNumber (DualNumber k)) c * del₂).snd.snd = 0 := by
  simp [algebraMap_eq_inl']

theorem snd_snd_algebraMap₂_mul_eps₂_mul_del₂ (c : k) :
    (algebraMap k (DualNumber (DualNumber k)) c * (eps₂ * del₂)).snd.snd = c := by
  simp [algebraMap_eq_inl']

theorem snd_snd_algebraMap₂_mul_del₂_mul_eps₂ (c : k) :
    (algebraMap k (DualNumber (DualNumber k)) c * (del₂ * eps₂)).snd.snd = c := by
  simp [algebraMap_eq_inl']

/-- **The bracket in coordinates.** `D_{[v, w]} = C(v, w) - C(w, v)`. -/
theorem tangentCoeff_tangentBracket (v w : pointsKer G aug₁) (a : stalkOne G) :
    tangentCoeff (tangentBracket v w) a = mulCoeff v w a - mulCoeff w v a := by
  have e : tangentMul (tangentBracket v w) * (tangentDel w * tangentEps v) =
      tangentEps v * tangentDel w := by
    rw [tangentMul_tangentBracket, commutatorElement_def]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have h := congrArg (fun p ↦ (kerHom p a).snd.snd) e
  rw [kerHom_tangentMap_mul (G := G) (π := aug₂) (eps₂ * del₂) aug₂_eps₂_mul_del₂
      eps₂_mul_del₂_mul (tangentBracket v w) (tangentDel w * tangentEps v) a,
    kerHom_tangentMap_mul_tangentMap (G := G) (π := aug₂) del₂ eps₂ del₂_mul_self
      eps₂_mul_self aug₂_del₂ aug₂_eps₂ w v a,
    kerHom_tangentMap_mul_tangentMap (G := G) (π := aug₂) eps₂ del₂ eps₂_mul_self
      del₂_mul_self aug₂_eps₂ aug₂_del₂ v w a] at h
  simp only [snd_add, snd_snd_algebraMap₂, snd_snd_algebraMap₂_mul_eps₂,
    snd_snd_algebraMap₂_mul_del₂, snd_snd_algebraMap₂_mul_eps₂_mul_del₂,
    snd_snd_algebraMap₂_mul_del₂_mul_eps₂] at h
  linear_combination h

theorem tangentBracket_self (v : pointsKer G aug₁) : tangentBracket v v = 1 :=
  tangent_ext fun a ↦ by rw [tangentCoeff_tangentBracket, sub_self, tangentCoeff_one]

theorem commute_tangentMul (u : pointsKer G aug₁) (q : pointsKer G (aug₂ (k := k))) :
    Commute (tangentMul u) q :=
  commute_tangentMap (eps₂ * del₂) aug₂_eps₂_mul_del₂ eps₂_mul_del₂_mul u q

theorem tangentBracket_mul_left (v v' w : pointsKer G aug₁) :
    tangentBracket (v * v') w = tangentBracket v w * tangentBracket v' w := by
  apply tangentMul_injective
  rw [tangentMul_tangentBracket, show tangentEps (v * v') = tangentEps v * tangentEps v' from
    map_mul _ _ _, show tangentMul (tangentBracket v w * tangentBracket v' w) =
      tangentMul (tangentBracket v w) * tangentMul (tangentBracket v' w) from map_mul _ _ _,
    tangentMul_tangentBracket, tangentMul_tangentBracket]
  have e : ∀ a b c : pointsKer G (aug₂ (k := k)), ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
    intro a b c
    simp only [commutatorElement_def]
    group
  rw [e, ← tangentMul_tangentBracket v' w, ← (commute_tangentMul _ _).eq, mul_inv_cancel_right,
    ← tangentMul_tangentBracket v w]
  exact (commute_tangentMul _ _).eq

theorem tangentBracket_mul_right (v w w' : pointsKer G aug₁) :
    tangentBracket v (w * w') = tangentBracket v w * tangentBracket v w' := by
  apply tangentMul_injective
  rw [tangentMul_tangentBracket, show tangentDel (w * w') = tangentDel w * tangentDel w' from
    map_mul _ _ _, show tangentMul (tangentBracket v w * tangentBracket v w') =
      tangentMul (tangentBracket v w) * tangentMul (tangentBracket v w') from map_mul _ _ _,
    tangentMul_tangentBracket, tangentMul_tangentBracket]
  have e : ∀ a b c : pointsKer G (aug₂ (k := k)), ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    intro a b c
    simp only [commutatorElement_def]
    group
  rw [e, ← tangentMul_tangentBracket v w', ← (commute_tangentMul _ _).eq, mul_inv_cancel_right]
/-! ### The Jacobi identity -/

/-- The residue map of `k[α][β][γ]`. -/
abbrev aug₃ : DualNumber (DualNumber (DualNumber k)) →ₐ[k] k :=
  dualAug aug₂

/-- The element `α` of `k[α][β][γ]`. -/
abbrev alp₃ : DualNumber (DualNumber (DualNumber k)) :=
  inl eps₂

/-- The element `β` of `k[α][β][γ]`. -/
abbrev bet₃ : DualNumber (DualNumber (DualNumber k)) :=
  inl del₂

/-- The element `γ` of `k[α][β][γ]`. -/
abbrev gam₃ : DualNumber (DualNumber (DualNumber k)) :=
  inr 1

theorem alp₃_mul_self : alp₃ (k := k) * alp₃ (k := k) = 0 := by
  ext <;> simp

theorem bet₃_mul_self : bet₃ (k := k) * bet₃ (k := k) = 0 := by
  ext <;> simp

theorem gam₃_mul_self : gam₃ (k := k) * gam₃ (k := k) = 0 := by
  ext <;> simp

theorem aug₃_alp₃ : aug₃ (alp₃ (k := k)) = 0 := by
  simp

theorem aug₃_bet₃ : aug₃ (bet₃ (k := k)) = 0 := by
  simp

theorem aug₃_gam₃ : aug₃ (gam₃ (k := k)) = 0 := by
  simp

/-- The product `αβγ`, which kills the maximal ideal of `k[α][β][γ]`. -/
abbrev mon₃ : DualNumber (DualNumber (DualNumber k)) :=
  alp₃ (k := k) * bet₃ * gam₃

theorem mon₃_mul (x : DualNumber (DualNumber (DualNumber k))) (hx : aug₃ x = 0) :
    mon₃ (k := k) * x = 0 := by
  have h : x.fst.fst.fst = 0 := hx
  ext <;> simp [h]

theorem aug₃_mon₃ : aug₃ (mon₃ (k := k)) = 0 := by
  simp [mon₃]

theorem liftElem_mon₃_injective :
    Function.Injective (DualNumber.liftElem (R := k) (mon₃ : DualNumber (DualNumber
      (DualNumber k))) (mon₃_mul _ aug₃_mon₃)) := by
  intro x y h
  have h1 := congrArg (fun z : DualNumber (DualNumber (DualNumber k)) ↦ z.fst.fst.fst) h
  have h2 := congrArg (fun z : DualNumber (DualNumber (DualNumber k)) ↦ z.snd.snd.snd) h
  simp only [DualNumber.liftElem_apply, algebraMap_eq_inl', fst_add, fst_mul, snd_add,
    snd_mul, fst_inl, snd_inl, fst_inr, snd_inr, smul_eq_mul, op_smul_eq_mul, mul_zero,
    zero_mul, add_zero, zero_add, mul_one] at h1 h2
  exact TrivSqZeroExt.ext h1 h2

/-- The points `u^{(αβγ)}`, as a homomorphism from the tangent vectors. -/
noncomputable abbrev tangentMon (u : pointsKer G aug₁) : pointsKer G (aug₃ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber (DualNumber k))) (π := aug₃) mon₃
    (mon₃_mul _ aug₃_mon₃) aug₃_mon₃ u

theorem tangentMon_injective : Function.Injective (tangentMon (G := G)) :=
  kerMap_injective _ _ liftElem_mon₃_injective

omit [IsLocalHom π.toRingHom] in
theorem commutator_commutator_tangentMap (m₁ m₂ m₃ : A) (h₁ : m₁ * m₁ = 0) (h₂ : m₂ * m₂ = 0)
    (h₃ : m₃ * m₃ = 0) (hπ₁ : π m₁ = 0) (hπ₂ : π m₂ = 0) (hπ₃ : π m₃ = 0) (m : A)
    (hm : m * m = 0) (hπ : π m = 0) (h : m₁ * m₂ * m₃ = m) (x y z : pointsKer G aug₁) :
    ⁅⁅tangentMap m₁ h₁ hπ₁ x, tangentMap m₂ h₂ hπ₂ y⁆, tangentMap m₃ h₃ hπ₃ z⁆ =
      tangentMap m hm hπ (tangentBracket (tangentBracket x y) z) := by
  rw [commutator_tangentMap, commutator_tangentMap, tangentMap_congr (G := G) h _ _ hm hπ]

/-- The point `x^{(α)}` over `k[α][β][γ]`. -/
noncomputable abbrev tangentAlp (x : pointsKer G aug₁) : pointsKer G (aug₃ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber (DualNumber k))) (π := aug₃) alp₃ alp₃_mul_self
    aug₃_alp₃ x

/-- The point `x^{(β)}` over `k[α][β][γ]`. -/
noncomputable abbrev tangentBet (x : pointsKer G aug₁) : pointsKer G (aug₃ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber (DualNumber k))) (π := aug₃) bet₃ bet₃_mul_self
    aug₃_bet₃ x

/-- The point `x^{(γ)}` over `k[α][β][γ]`. -/
noncomputable abbrev tangentGam (x : pointsKer G aug₁) : pointsKer G (aug₃ (k := k)) :=
  tangentMap (A := DualNumber (DualNumber (DualNumber k))) (π := aug₃) gam₃ gam₃_mul_self
    aug₃_gam₃ x

theorem tangentMon_conj (u : pointsKer G aug₁) (q : pointsKer G (aug₃ (k := k))) :
    q * tangentMon u * q⁻¹ = tangentMon u := by
  rw [← (commute_tangentMap (A := DualNumber (DualNumber (DualNumber k))) (π := aug₃) mon₃
    aug₃_mon₃ mon₃_mul u q).eq, mul_inv_cancel_right]

/-- The Hall–Witt identity after substitution into a local algebra, when the product of the
three square-zero parameters kills the maximal ideal. -/
private theorem tangentMap_tangentBracket_hallWitt (m₁ m₂ m₃ : A) (h₁ : m₁ * m₁ = 0)
    (h₂ : m₂ * m₂ = 0) (h₃ : m₃ * m₃ = 0) (hπ₁ : π m₁ = 0) (hπ₂ : π m₂ = 0)
    (hπ₃ : π m₃ = 0) (m : A) (hπ : π m = 0) (hm : ∀ a, π a = 0 → m * a = 0)
    (h : m₁ * m₂ * m₃ = m) (x y z : pointsKer G aug₁) :
    tangentMap m (hm m hπ) hπ
      (tangentBracket (tangentBracket x⁻¹ y) z * tangentBracket (tangentBracket z⁻¹ x) y *
        tangentBracket (tangentBracket y⁻¹ z) x) = 1 := by
  let f₁ := tangentMap (G := G) m₁ h₁ hπ₁
  let f₂ := tangentMap (G := G) m₂ h₂ hπ₂
  let f₃ := tangentMap (G := G) m₃ h₃ hπ₃
  let t := tangentMap (G := G) m (hm m hπ) hπ
  have hw := conj_commutatorElement_left_commutatorElement_mul (f₁ x) (f₂ y) (f₃ z)
  have e₁ : ⁅⁅(f₁ x)⁻¹, f₂ y⁆, f₃ z⁆ =
      t (tangentBracket (tangentBracket x⁻¹ y) z) := by
    rw [← map_inv]
    exact commutator_commutator_tangentMap m₁ m₂ m₃ h₁ h₂ h₃ hπ₁ hπ₂ hπ₃ m
      (hm m hπ) hπ h _ _ _
  have e₂ : ⁅⁅(f₃ z)⁻¹, f₁ x⁆, f₂ y⁆ =
      t (tangentBracket (tangentBracket z⁻¹ x) y) := by
    rw [← map_inv]
    exact commutator_commutator_tangentMap m₃ m₁ m₂ h₃ h₁ h₂ hπ₃ hπ₁ hπ₂ m
      (hm m hπ) hπ (by rw [mul_comm m₃ m₁, mul_right_comm, h]) _ _ _
  have e₃ : ⁅⁅(f₂ y)⁻¹, f₃ z⁆, f₁ x⁆ =
      t (tangentBracket (tangentBracket y⁻¹ z) x) := by
    rw [← map_inv]
    exact commutator_commutator_tangentMap m₂ m₃ m₁ h₂ h₃ h₁ hπ₂ hπ₃ hπ₁ m
      (hm m hπ) hπ (by rw [mul_comm _ m₁, ← mul_assoc, h]) _ _ _
  rw [e₁, e₂, e₃] at hw
  have hc (u : pointsKer G aug₁) (q : pointsKer G π) : q * t u * q⁻¹ = t u := by
    rw [← (commute_tangentMap m hπ hm u q).eq, mul_inv_cancel_right]
  have key : ∀ {P : Type u} [Group P] (a b c t₁ t₂ t₃ : P), a * t₁ * a⁻¹ = t₁ →
      c * t₂ * c⁻¹ = t₂ → b * t₃ * b⁻¹ = t₃ →
      a * t₁ * a⁻¹ * c * t₂ * c⁻¹ * b * t₃ * b⁻¹ = 1 → t₁ * t₂ * t₃ = 1 := by
    intro P _ a b c t₁ t₂ t₃ h₁ h₂ h₃ h
    rw [← h₁, ← h₂, ← h₃, ← h]
    group
  exact (map_mul t _ _).trans ((congrArg (· * t _) (map_mul t _ _)).trans
    (key _ _ _ _ _ _ (hc _ _) (hc _ _) (hc _ _) hw))

/-- The Hall–Witt identity for tangent vectors: the Hall–Witt identity of the group of points
over `k[α][β][γ]`, applied to `x^{(α)}`, `y^{(β)}` and `z^{(γ)}`. -/
theorem tangentBracket_hallWitt (x y z : pointsKer G aug₁) :
    tangentBracket (tangentBracket x⁻¹ y) z * tangentBracket (tangentBracket z⁻¹ x) y *
      tangentBracket (tangentBracket y⁻¹ z) x = 1 := by
  apply tangentMon_injective
  exact (tangentMap_tangentBracket_hallWitt
    (A := DualNumber (DualNumber (DualNumber k))) (π := aug₃) (G := G)
    alp₃ bet₃ gam₃ alp₃_mul_self bet₃_mul_self gam₃_mul_self
    aug₃_alp₃ aug₃_bet₃ aug₃_gam₃ mon₃ aug₃_mon₃ mon₃_mul rfl x y z).trans
    (map_one _).symm
/-! ### The Lie algebra -/

theorem tangentBracket_one_left (w : pointsKer G aug₁) : tangentBracket 1 w = 1 := by
  have h := tangentBracket_mul_left (1 : pointsKer G aug₁) 1 w
  rw [one_mul] at h
  exact left_eq_mul.mp h

theorem tangentBracket_inv_left (v w : pointsKer G aug₁) :
    tangentBracket v⁻¹ w = (tangentBracket v w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← tangentBracket_mul_left, inv_mul_cancel,
    tangentBracket_one_left]


variable (G) in
/-- The Lie algebra of `G` is the group of tangent vectors: `Lie(G) ≃ ker(G(k[ε]) → G(k))`. -/
noncomputable def lieEquivTangent : Lie G ≃ pointsKer G (aug₁ (k := k)) :=
  (lieEquiv G).symm.trans (infPointsEquivTangentGroup G).toEquiv

theorem lieEquivTangent_add (x y : Lie G) :
    lieEquivTangent G (x + y) = lieEquivTangent G x * lieEquivTangent G y := by
  simp only [lieEquivTangent, Equiv.trans_apply, lieEquiv_symm_add, MulEquiv.toEquiv_eq_coe]
  exact map_mul (infPointsEquivTangentGroup G) _ _

theorem lieEquivTangent_symm_mul (p q : pointsKer G (aug₁ (k := k))) :
    (lieEquivTangent G).symm (p * q) =
      (lieEquivTangent G).symm p + (lieEquivTangent G).symm q :=
  (lieEquivTangent G).injective (by simp [lieEquivTangent_add])

theorem lieEquivTangent_symm_one : (lieEquivTangent G).symm 1 = 0 := by
  have h := lieEquivTangent_symm_mul (G := G) 1 1
  rw [one_mul] at h
  exact left_eq_add.mp h

/-- The Lie bracket on `Lie(G)` of a group scheme over a field: the mixed term `[v, w]` of the
commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` of two tangent vectors over `k[ε][δ]`.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable instance : Bracket (Lie G) (Lie G) where
  bracket x y := (lieEquivTangent G).symm
    (tangentBracket (lieEquivTangent G x) (lieEquivTangent G y))

theorem lie_def (x y : Lie G) :
    ⁅x, y⁆ = (lieEquivTangent G).symm
      (tangentBracket (lieEquivTangent G x) (lieEquivTangent G y)) :=
  rfl

theorem lieEquivTangent_lie (x y : Lie G) :
    lieEquivTangent G ⁅x, y⁆ = tangentBracket (lieEquivTangent G x) (lieEquivTangent G y) :=
  (lieEquivTangent G).apply_symm_apply _

theorem lie_add_left (x y z : Lie G) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  rw [lie_def, lieEquivTangent_add, tangentBracket_mul_left, lieEquivTangent_symm_mul]
  rfl

theorem lie_add_right (x y z : Lie G) : ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  rw [lie_def, lieEquivTangent_add, tangentBracket_mul_right, lieEquivTangent_symm_mul]
  rfl

theorem lie_self' (x : Lie G) : ⁅x, x⁆ = 0 := by
  rw [lie_def, tangentBracket_self, lieEquivTangent_symm_one]

theorem lie_neg_left' (x y : Lie G) : ⁅-x, y⁆ = -⁅x, y⁆ := by
  rw [eq_neg_iff_add_eq_zero, ← lie_add_left, neg_add_cancel, lie_def,
    show lieEquivTangent G 0 = 1 by
      rw [← lieEquivTangent_symm_one (G := G), Equiv.apply_symm_apply],
    tangentBracket_one_left, lieEquivTangent_symm_one]

theorem lie_antisymm' (x y : Lie G) : ⁅x, y⁆ = -⁅y, x⁆ := by
  have h := lie_self' (x + y)
  rw [lie_add_left, lie_add_right, lie_add_right, lie_self', lie_self', zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem lie_neg_right' (x y : Lie G) : ⁅x, -y⁆ = -⁅x, y⁆ := by
  rw [lie_antisymm', lie_neg_left', neg_neg, lie_antisymm' x y, neg_neg]


theorem lieEquivTangent_neg (x : Lie G) : lieEquivTangent G (-x) = (lieEquivTangent G x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← lieEquivTangent_add, neg_add_cancel,
    ← lieEquivTangent_symm_one (G := G), Equiv.apply_symm_apply]

theorem lie_jacobi' (x y z : Lie G) : ⁅⁅x, y⁆, z⁆ + ⁅⁅z, x⁆, y⁆ + ⁅⁅y, z⁆, x⁆ = 0 := by
  have h := tangentBracket_hallWitt (lieEquivTangent G x) (lieEquivTangent G y)
    (lieEquivTangent G z)
  simp only [← lieEquivTangent_lie, ← lieEquivTangent_neg, ← lieEquivTangent_add] at h
  have h' := congrArg (lieEquivTangent G).symm h
  rw [Equiv.symm_apply_apply, lieEquivTangent_symm_one] at h'
  simp only [lie_neg_left'] at h'
  rw [← neg_add, ← neg_add, neg_eq_zero] at h'
  exact h'

theorem leibniz_lie' (x y z : Lie G) : ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  have j := lie_jacobi' x y z
  have a₂ : ⁅⁅z, x⁆, y⁆ = ⁅y, ⁅x, z⁆⁆ := by
    rw [lie_antisymm' z x, lie_neg_left', lie_antisymm' ⁅x, z⁆ y, neg_neg]
  rw [lie_antisymm' x ⁅y, z⁆, ← a₂]
  exact (eq_neg_of_add_eq_zero_left j).symm

/-- `Lie(G)` is a Lie ring. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable instance : LieRing (Lie G) where
  add_lie := lie_add_left
  lie_add := lie_add_right
  lie_self := lie_self'
  leibniz_lie := leibniz_lie'

theorem inr_mul_self (c : k) : (inr c : DualNumber k) * inr c = 0 := by
  ext <;> simp

/-- The rescaling `v ↦ v^{(cε)}` of tangent vectors. -/
noncomputable abbrev tangentScale (c : k) : pointsKer G aug₁ →* pointsKer G (aug₁ (k := k)) :=
  tangentMap (A := DualNumber k) (π := aug₁) (inr c) (inr_mul_self c) (by simp)

theorem lieEquivTangent_smul (c : k) (x : Lie G) :
    lieEquivTangent G (c • x) = tangentScale c (lieEquivTangent G x) := by
  apply Subtype.ext
  change inv dualNumbersToSpecOver ≫ ((lieEquiv G).symm ((Scheme.ΓSpecIso (.of k)).inv c • x)).1 =
    points.map G _ (inv dualNumbersToSpecOver ≫ ((lieEquiv G).symm x).1)
  rw [lieEquiv_symm_smul, points.map]
  change inv dualNumbersToSpecOver ≫ Scheme.dualNumbersScaleOver _ _ ≫ _ = _
  have e : DualNumber.liftElem (R := k) (inr c) (inr_mul_self c) = DualNumber.scale c := by
    ext <;> simp [DualNumber.liftElem_apply, algebraMap_eq_inl]
  have key : inv dualNumbersToSpecOver ≫
      Scheme.dualNumbersScaleOver (Spec (.of k)) ((Scheme.ΓSpecIso (.of k)).inv c) =
      (Spec.map (CommRingCat.ofHom (DualNumber.liftElem (R := k) (inr c)
        (inr_mul_self c)).toRingHom)).asOver (Spec (.of k)) ≫ inv dualNumbersToSpecOver := by
    rw [e, IsIso.inv_comp_eq, ← Category.assoc, ← dualNumbersScaleOver_comp_dualNumbersToSpecOver,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, key, Category.assoc]

theorem tangentBracket_tangentScale (c : k) (v w : pointsKer G aug₁) :
    tangentBracket v (tangentScale c w) = tangentScale c (tangentBracket v w) := by
  apply tangentMul_injective
  rw [tangentMul_tangentBracket]
  have e₁ : tangentDel (tangentScale c w) = tangentMap (A := DualNumber (DualNumber k))
      (π := aug₂) (algebraMap k _ c * del₂) (by ext <;> simp [algebraMap_eq_inl']) (by simp) w :=
    kerMap_tangentMap _ _ _ _ _ _ _ _
      (by simp [DualNumber.liftElem_apply, Algebra.smul_def, algebraMap_eq_inl]) w
  have e₂ : tangentMul (tangentScale c (tangentBracket v w)) =
      tangentMap (A := DualNumber (DualNumber k)) (π := aug₂) (algebraMap k _ c * (eps₂ * del₂))
        (by ext <;> simp [algebraMap_eq_inl']) (by simp) (tangentBracket v w) :=
    kerMap_tangentMap _ _ _ _ _ _ _ _
      (by simp [DualNumber.liftElem_apply, Algebra.smul_def, algebraMap_eq_inl]) _
  rw [e₁, e₂, commutator_tangentMap]
  exact tangentMap_apply_congr (mul_left_comm _ _ _) _ _ _ _ _

theorem lie_smul' (c : k) (x y : Lie G) : ⁅x, c • y⁆ = c • ⁅x, y⁆ := by
  apply (lieEquivTangent G).injective
  rw [lieEquivTangent_lie, lieEquivTangent_smul, lieEquivTangent_smul, lieEquivTangent_lie,
    tangentBracket_tangentScale]

/-- `Lie(G)` is a Lie algebra over `k`. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable instance : LieAlgebra k (Lie G) where
  lie_smul := lie_smul'
end AlgebraicGeometry.GrpObj
