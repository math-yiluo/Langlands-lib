import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Solvable
import Langlands.TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Langlands.GroupScheme.Absolute.RationalPointClosureProof
import Langlands.GroupScheme.Absolute.BorelFieldExtensionHeight

/-! # Descent and specialization of solvable groups of points -/

noncomputable section

namespace Langlands.GroupScheme.BorelFieldExtension

open TensorProduct WithConv
open scoped commutatorElement

section Res

variable {k K H C : Type*} [Field k] [Field K] [Algebra k K] [CommRing H] [HopfAlgebra k H]
  [CommRing C] [Algebra K C] [Algebra k C] [IsScalarTower k K C]

/-- Restriction of a `K`-algebra map `K ⊗[k] H → C` to `H`. -/
def resFun (φ : K ⊗[k] H →ₐ[K] C) : H →ₐ[k] C :=
  (φ.restrictScalars k).comp Algebra.TensorProduct.includeRight

@[simp]
theorem resFun_apply (φ : K ⊗[k] H →ₐ[K] C) (h : H) : resFun φ h = φ (1 ⊗ₜ h) := rfl

theorem resFun_injective : Function.Injective (resFun (k := k) (K := K) (H := H) (C := C)) := by
  intro φ ψ h
  apply Algebra.TensorProduct.ext_ring
  ext x
  exact congrArg (fun f : H →ₐ[k] C => f x) h

theorem resFun_mul (φ ψ : WithConv (K ⊗[k] H →ₐ[K] C)) :
    resFun (φ * ψ).ofConv = (toConv (resFun φ.ofConv) * toConv (resFun ψ.ofConv)).ofConv := by
  ext h
  rw [resFun_apply, AlgHom.convMul_apply, AlgHom.convMul_apply]
  rw [TensorProduct.comul_tmul]
  induction (Coalgebra.comul (R := k) h : H ⊗[k] H) using TensorProduct.inductionOn with
  | tmul a b =>
    simp [Algebra.TensorProduct.lift_tmul]
  | add x y hx hy =>
    simp only [tmul_add, map_add] at hx hy ⊢
    rw [hx, hy]

theorem resFun_one :
    resFun (1 : WithConv (K ⊗[k] H →ₐ[K] C)).ofConv =
      (1 : WithConv (H →ₐ[k] C)).ofConv := by
  ext h
  rw [resFun_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul]
  simp [Algebra.algebraMap_eq_smul_one, IsScalarTower.algebraMap_apply k K C]

variable (k K H C) in
/-- Restriction to `H`, as a group homomorphism of convolution groups. -/
def res : WithConv (K ⊗[k] H →ₐ[K] C) →* WithConv (H →ₐ[k] C) where
  toFun φ := toConv (resFun φ.ofConv)
  map_one' := congrArg toConv resFun_one
  map_mul' φ ψ := congrArg toConv (resFun_mul φ ψ)

theorem res_injective : Function.Injective (res k K H C) := by
  intro φ ψ h
  exact WithConv.ofConv_injective (resFun_injective (congrArg ofConv h))

end Res

section Basic

variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]

/-- The `K`-linear extension `K ⊗[k] M → K` of a `k`-algebra map `x : M → K`. -/
def extPoint {M : Type*} [CommRing M] [Algebra k M] (x : M →ₐ[k] K) : K ⊗[k] M →ₐ[K] K :=
  Algebra.TensorProduct.lift (Algebra.ofId K K) x fun _ _ => Commute.all _ _

@[simp]
theorem extPoint_tmul {M : Type*} [CommRing M] [Algebra k M] (x : M →ₐ[k] K) (a : K) (m : M) :
    extPoint x (a ⊗ₜ m) = a * x m := by
  simp [extPoint, Algebra.TensorProduct.lift_tmul]

/-- The base change `K ⊗[k] M → K ⊗[k] N` of a `k`-algebra map `g : M → N`. -/
def baseMap {M N : Type*} [CommRing M] [Algebra k M] [CommRing N] [Algebra k N]
    (g : M →ₐ[k] N) : K ⊗[k] M →ₐ[K] K ⊗[k] N :=
  Algebra.TensorProduct.map (AlgHom.id K K) g

@[simp]
theorem baseMap_tmul {M N : Type*} [CommRing M] [Algebra k M] [CommRing N] [Algebra k N]
    (g : M →ₐ[k] N) (a : K) (m : M) : baseMap g (a ⊗ₜ m) = a ⊗ₜ g m := rfl

theorem extPoint_comp_baseMap {M N : Type*} [CommRing M] [Algebra k M] [CommRing N] [Algebra k N]
    (y : N →ₐ[k] K) (g : M →ₐ[k] N) :
    (extPoint y).comp (baseMap g) = extPoint (y.comp g) := by
  apply Algebra.TensorProduct.ext'
  intro a m
  simp

theorem extPoint_baseMap {M N : Type*} [CommRing M] [Algebra k M] [CommRing N] [Algebra k N]
    (y : N →ₐ[k] K) (g : M →ₐ[k] N) (f : K ⊗[k] M) :
    extPoint y (baseMap g f) = extPoint (y.comp g) f :=
  AlgHom.congr_fun (extPoint_comp_baseMap y g) f

/-- The pair of points `(x, y)`, as a `k`-algebra map `M ⊗[k] M → K`. -/
def pairLift {M : Type*} [CommRing M] [Algebra k M] (x y : M →ₐ[k] K) : M ⊗[k] M →ₐ[k] K :=
  Algebra.TensorProduct.lift x y fun _ _ => Commute.all _ _

@[simp]
theorem pairLift_tmul {M : Type*} [CommRing M] [Algebra k M] (x y : M →ₐ[k] K) (a b : M) :
    pairLift x y (a ⊗ₜ b) = x a * y b := by
  simp [pairLift, Algebra.TensorProduct.lift_tmul]

theorem pairLift_comp_includeLeft {M : Type*} [CommRing M] [Algebra k M] (x y : M →ₐ[k] K) :
    (pairLift x y).comp (Algebra.TensorProduct.includeLeft : M →ₐ[k] M ⊗[k] M) = x := by
  ext a
  simp

theorem pairLift_comp_includeRight {M : Type*} [CommRing M] [Algebra k M] (x y : M →ₐ[k] K) :
    (pairLift x y).comp (Algebra.TensorProduct.includeRight : M →ₐ[k] M ⊗[k] M) = y := by
  ext a
  simp

variable {H : Type*} [CommRing H] [Algebra k H]

variable (K) in
/-- The ideal of `K ⊗[k] (H ⊗[k] H)` generated by the two pullbacks of an ideal `I` of
`K ⊗[k] H` along the two projections. -/
def pairIdeal (I : Ideal (K ⊗[k] H)) : Ideal (K ⊗[k] (H ⊗[k] H)) :=
  I.map (baseMap (K := K) (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H)) ⊔
    I.map (baseMap (K := K) (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H))

end Basic

section Separation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The ideal of `K ⊗[k] M` of functions vanishing at every point of `Γ`. -/
def vanishingIdeal {M : Type*} [CommRing M] [Algebra k M] (Γ : Set (M →ₐ[k] K)) :
    Ideal (K ⊗[k] M) where
  carrier := {f | ∀ x ∈ Γ, extPoint x f = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := map_zero _
  smul_mem' c f hf x hx := by rw [smul_eq_mul, map_mul, hf x hx, mul_zero]

theorem mem_vanishingIdeal {M : Type*} [CommRing M] [Algebra k M] {Γ : Set (M →ₐ[k] K)}
    {f : K ⊗[k] M} : f ∈ vanishingIdeal Γ ↔ ∀ x ∈ Γ, extPoint x f = 0 := Iff.rfl

theorem vanishingIdeal_anti {M : Type*} [CommRing M] [Algebra k M] {Γ Γ' : Set (M →ₐ[k] K)}
    (h : Γ ⊆ Γ') : vanishingIdeal Γ' ≤ vanishingIdeal Γ :=
  fun _ hf x hx => hf x (h hx)

variable {H : Type*} [CommRing H] [Algebra k H]

/-- **Separation.** If a law `w : H → H ⊗[k] H` sends every pair of points of `Γ₁` into `Γ₂`, then
it pulls the vanishing ideal of `Γ₂` back into the ideal generated by the two pullbacks of the
vanishing ideal of `Γ₁`. -/
theorem baseMap_mem_pairIdeal {Γ₁ Γ₂ : Set (H →ₐ[k] K)} (w : H →ₐ[k] H ⊗[k] H)
    (hw : ∀ x ∈ Γ₁, ∀ y ∈ Γ₁, (pairLift x y).comp w ∈ Γ₂) {f : K ⊗[k] H}
    (hf : f ∈ vanishingIdeal Γ₂) :
    baseMap w f ∈ pairIdeal K (vanishingIdeal Γ₁) := by
  set I := vanishingIdeal Γ₁ with hI
  set N := pairIdeal K I with hN
  let q : H →ₐ[k] (K ⊗[k] H) ⧸ I :=
    ((Ideal.Quotient.mkₐ K I).restrictScalars k).comp Algebra.TensorProduct.includeRight
  let Φ₀ : H ⊗[k] H →ₐ[k] ((K ⊗[k] H) ⧸ I) ⊗[K] ((K ⊗[k] H) ⧸ I) :=
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : _ →ₐ[k] ((K ⊗[k] H) ⧸ I) ⊗[K] ((K ⊗[k] H) ⧸ I)).comp q)
      ((Algebra.TensorProduct.includeRight.restrictScalars k).comp q)
      fun _ _ => Commute.all (S := ((K ⊗[k] H) ⧸ I) ⊗[K] ((K ⊗[k] H) ⧸ I)) _ _
  let Φ : K ⊗[k] (H ⊗[k] H) →ₐ[K] ((K ⊗[k] H) ⧸ I) ⊗[K] ((K ⊗[k] H) ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId K _) Φ₀
      fun _ _ => Commute.all (S := ((K ⊗[k] H) ⧸ I) ⊗[K] ((K ⊗[k] H) ⧸ I)) _ _
  have hl : I.map (baseMap (K := K) (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H)) ≤ N :=
    le_sup_left
  have hr : I.map (baseMap (K := K) (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)) ≤
      N := le_sup_right
  let u₁ : (K ⊗[k] H) ⧸ I →ₐ[K] (K ⊗[k] (H ⊗[k] H)) ⧸ N :=
    Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ K N).comp (baseMap Algebra.TensorProduct.includeLeft))
      fun a ha => by
        rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hl (Ideal.mem_map_of_mem _ ha)
  let u₂ : (K ⊗[k] H) ⧸ I →ₐ[K] (K ⊗[k] (H ⊗[k] H)) ⧸ N :=
    Ideal.Quotient.liftₐ I
      ((Ideal.Quotient.mkₐ K N).comp (baseMap Algebra.TensorProduct.includeRight))
      fun a ha => by
        rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hr (Ideal.mem_map_of_mem _ ha)
  let L := Algebra.TensorProduct.lift u₁ u₂
    fun _ _ => Commute.all (S := (K ⊗[k] (H ⊗[k] H)) ⧸ N) _ _
  have hΦ_tmul : ∀ a b : H, Φ (1 ⊗ₜ (a ⊗ₜ b)) =
      Ideal.Quotient.mk I (1 ⊗ₜ a) ⊗ₜ Ideal.Quotient.mk I (1 ⊗ₜ b) := by
    intro a b
    simp only [Φ, Φ₀, q, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk, one_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [Algebra.ofId_apply, map_one]
    exact one_mul (M := ((K ⊗[k] H) ⧸ I) ⊗[K] ((K ⊗[k] H) ⧸ I)) _
  have hLΦ : L.comp Φ = Ideal.Quotient.mkₐ K N := by
    apply Algebra.TensorProduct.ext_ring
    apply Algebra.TensorProduct.ext'
    intro a b
    change L (Φ (1 ⊗ₜ (a ⊗ₜ b))) = Ideal.Quotient.mk N (1 ⊗ₜ (a ⊗ₜ b))
    rw [hΦ_tmul, Algebra.TensorProduct.lift_tmul]
    change Ideal.Quotient.mk N (baseMap Algebra.TensorProduct.includeLeft (1 ⊗ₜ a)) *
      Ideal.Quotient.mk N (baseMap Algebra.TensorProduct.includeRight (1 ⊗ₜ b)) = _
    rw [baseMap_tmul, baseMap_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let χ : Γ₁ → ((K ⊗[k] H) ⧸ I) →ₐ[K] K := fun x =>
    Ideal.Quotient.liftₐ I (extPoint x.1) fun a ha => ha x.1 x.2
  have hχ : ∀ t, (∀ x, χ x t = 0) → t = 0 := by
    intro t ht
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [Ideal.Quotient.eq_zero_iff_mem]
    intro x hx
    exact ht ⟨x, hx⟩
  have hΦ : Φ (baseMap w f) = 0 := by
    refine RationalPointClosure.tensor_eq_zero_of_separating χ hχ _ fun x y => ?_
    have hcomp : (Algebra.TensorProduct.lift (χ x) (χ y)
        fun _ _ => Commute.all (S := K) _ _).comp Φ =
        extPoint (pairLift x.1 y.1) := by
      apply Algebra.TensorProduct.ext_ring
      apply Algebra.TensorProduct.ext'
      intro a b
      change Algebra.TensorProduct.lift (χ x) (χ y) (fun _ _ => Commute.all (S := K) _ _)
          (Φ (1 ⊗ₜ (a ⊗ₜ b))) =
        extPoint (pairLift x.1 y.1) (1 ⊗ₜ (a ⊗ₜ b))
      rw [hΦ_tmul, Algebra.TensorProduct.lift_tmul]
      change extPoint x.1 (1 ⊗ₜ a) * extPoint y.1 (1 ⊗ₜ b) = _
      simp
    rw [← AlgHom.comp_apply, hcomp, extPoint_baseMap]
    exact hf _ (hw x.1 x.2 y.1 y.2)
  have h := AlgHom.congr_fun hLΦ (baseMap w f)
  rw [AlgHom.comp_apply, hΦ, map_zero, Ideal.Quotient.mkₐ_eq_mk, eq_comm,
    Ideal.Quotient.eq_zero_iff_mem] at h
  exact h

end Separation

section Words

variable (k H : Type*) [Field k] [CommRing H] [HopfAlgebra k H]

/-- The universal first point `h ↦ h ⊗ 1` of `H` with values in `H ⊗[k] H`. -/
def univL : WithConv (H →ₐ[k] H ⊗[k] H) :=
  toConv (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H)

/-- The universal second point `h ↦ 1 ⊗ h` of `H` with values in `H ⊗[k] H`. -/
def univR : WithConv (H →ₐ[k] H ⊗[k] H) :=
  toConv (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H)

/-- The product law `(x, y) ↦ x * y`. -/
def wMul : WithConv (H →ₐ[k] H ⊗[k] H) := univL k H * univR k H

/-- The inverse law `(x, y) ↦ x⁻¹`. -/
def wInv : WithConv (H →ₐ[k] H ⊗[k] H) := (univL k H)⁻¹

/-- The commutator law `(x, y) ↦ ⁅x, y⁆`. -/
def wComm : WithConv (H →ₐ[k] H ⊗[k] H) := ⁅univL k H, univR k H⁆

variable {k H} {K : Type*} [CommRing K] [Algebra k K]

theorem mapValue_pairLift_univL (x y : H →ₐ[k] K) :
    AlgHom.mapValue (pairLift x y) (univL k H) = toConv x := by
  rw [AlgHom.mapValue_apply, univL, ofConv_toConv, pairLift_comp_includeLeft]

theorem mapValue_pairLift_univR (x y : H →ₐ[k] K) :
    AlgHom.mapValue (pairLift x y) (univR k H) = toConv y := by
  rw [AlgHom.mapValue_apply, univR, ofConv_toConv, pairLift_comp_includeRight]

theorem pairLift_comp_wMul (x y : H →ₐ[k] K) :
    (pairLift x y).comp (wMul k H).ofConv = (toConv x * toConv y).ofConv := by
  have h : AlgHom.mapValue (pairLift x y) (wMul k H) = toConv x * toConv y := by
    rw [wMul, map_mul, mapValue_pairLift_univL, mapValue_pairLift_univR]
  rw [← h, AlgHom.mapValue_apply, ofConv_toConv]

theorem pairLift_comp_wInv (x y : H →ₐ[k] K) :
    (pairLift x y).comp (wInv k H).ofConv = (toConv x)⁻¹.ofConv := by
  have h : AlgHom.mapValue (pairLift x y) (wInv k H) = (toConv x)⁻¹ := by
    rw [wInv, map_inv, mapValue_pairLift_univL]
  rw [← h, AlgHom.mapValue_apply, ofConv_toConv]

theorem pairLift_comp_wComm (x y : H →ₐ[k] K) :
    (pairLift x y).comp (wComm k H).ofConv = ⁅toConv x, toConv y⁆.ofConv := by
  have h : AlgHom.mapValue (pairLift x y) (wComm k H) = ⁅toConv x, toConv y⁆ := by
    rw [wComm, map_commutatorElement, mapValue_pairLift_univL, mapValue_pairLift_univR]
  rw [← h, AlgHom.mapValue_apply, ofConv_toConv]

end Words

section LawSystem

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
variable {R : Type*} [CommRing R] [Algebra k R]

/-- The pullbacks of a family of functions along the two projections `H ⊗[k] H → H`. -/
def pairFam {ι : Type*} (v : ι → R ⊗[k] H) : ι ⊕ ι → R ⊗[k] (H ⊗[k] H) :=
  Sum.elim (fun i => baseMap (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H) (v i))
    (fun i => baseMap (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H) (v i))

variable (R) in
/-- A *law system* of length `n` over `R`: finite families `g j` of functions on `H` with
coefficients in `R`, for `j ≤ n`, such that the point sets they cut out are closed under the
group laws, the commutators of the `j`-th set lie in the `(j+1)`-th set, and the `n`-th family
generates an ideal containing `1 ⊗ h - ε h` for all `h ∈ s`. -/
structure IsLawSystem (n : ℕ) (s : Set H) {r : ℕ → ℕ} (g : (j : ℕ) → Fin (r j) → R ⊗[k] H) :
    Prop where
  one : ∀ j ≤ n, ∀ i, extPoint (1 : WithConv (H →ₐ[k] R)).ofConv (g j i) = 0
  mul : ∀ j ≤ n, ∀ i,
    baseMap (K := R) (wMul k H).ofConv (g j i) ∈ Ideal.span (Set.range (pairFam (g j)))
  inv : ∀ j ≤ n, ∀ i,
    baseMap (K := R) (wInv k H).ofConv (g j i) ∈ Ideal.span (Set.range (pairFam (g j)))
  comm : ∀ j < n, ∀ i,
    baseMap (K := R) (wComm k H).ofConv (g (j + 1) i) ∈ Ideal.span (Set.range (pairFam (g j)))
  fin : ∀ h ∈ s, (1 : R) ⊗ₜ[k] h - algebraMap k (R ⊗[k] H) (Coalgebra.counit h) ∈
    Ideal.span (Set.range (g n))

/-- If `x` and `y` vanish on a family `v` and a law `w` sends `t` into the ideal generated by
the two pullbacks of `v`, then the point `(x, y) ∘ w` vanishes on `t`. -/
theorem extPoint_pairLift_eq_zero {ι : Type*} {v : ι → R ⊗[k] H} {x y : H →ₐ[k] R}
    (hx : ∀ i, extPoint x (v i) = 0) (hy : ∀ i, extPoint y (v i) = 0)
    {w : H →ₐ[k] H ⊗[k] H} {t : R ⊗[k] H}
    (ht : baseMap w t ∈ Ideal.span (Set.range (pairFam v))) :
    extPoint ((pairLift x y).comp w) t = 0 := by
  rw [← extPoint_baseMap]
  have hle : Ideal.span (Set.range (pairFam v)) ≤ RingHom.ker (extPoint (pairLift x y)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i | i, rfl⟩
    · simp only [pairFam, Sum.elim_inl, SetLike.mem_coe, RingHom.mem_ker, extPoint_baseMap,
        pairLift_comp_includeLeft, hx]
    · simp only [pairFam, Sum.elim_inr, SetLike.mem_coe, RingHom.mem_ker, extPoint_baseMap,
        pairLift_comp_includeRight, hy]
  exact hle ht

end LawSystem

section KSide

variable {k K H : Type*} [Field k] [Field K] [Algebra k K] [CommRing H] [HopfAlgebra k H]

theorem pairIdeal_span {ι : Type*} (v : ι → K ⊗[k] H) :
    pairIdeal K (Ideal.span (Set.range v)) = Ideal.span (Set.range (pairFam v)) := by
  rw [pairIdeal, Ideal.map_span, Ideal.map_span, ← Ideal.span_union, pairFam,
    Set.Sum.elim_range, ← Set.range_comp, ← Set.range_comp]
  rfl

/-- **The law system of a solvable group of points.** The vanishing ideals of the derived
subgroups of a solvable group `S` of `K`-points form a law system over `K` whose first family
vanishes on `S`. -/
theorem exists_isLawSystem [Algebra.FiniteType k H] (S : Subgroup (WithConv (H →ₐ[k] K)))
    [Group.IsSolvable S] (s : Set H) :
    ∃ n : ℕ, ∃ r : ℕ → ℕ, ∃ g : (j : ℕ) → Fin (r j) → K ⊗[k] H, IsLawSystem K n s g ∧
      ∀ i, ∀ x : H →ₐ[k] K, toConv x ∈ S → extPoint x (g 0 i) = 0 := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def S).1 ‹_›
  have : IsNoetherianRing (K ⊗[k] H) := Algebra.FiniteType.isNoetherianRing K _
  let Γ : ℕ → Set (H →ₐ[k] K) := fun j => {x | toConv x ∈ (derivedSeries S j).map S.subtype}
  have hΓ : ∀ j (x : H →ₐ[k] K), x ∈ Γ j ↔ toConv x ∈ (derivedSeries S j).map S.subtype :=
    fun _ _ => Iff.rfl
  have hfg : ∀ j, ∃ m : ℕ, ∃ v : Fin m → K ⊗[k] H,
      Ideal.span (Set.range v) = vanishingIdeal (Γ j) := fun j =>
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian _)
  choose r g hg using hfg
  have hmem : ∀ j i, g j i ∈ vanishingIdeal (Γ j) := fun j i => hg j ▸ Ideal.subset_span ⟨i, rfl⟩
  have hspan : ∀ j, pairIdeal K (vanishingIdeal (Γ j)) = Ideal.span (Set.range (pairFam (g j))) :=
    fun j => by rw [← hg j, pairIdeal_span]
  refine ⟨n, r, g, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j _ i
    apply hmem j i
    rw [hΓ, toConv_ofConv]
    exact Subgroup.one_mem _
  · intro j _ i
    rw [← hspan]
    refine baseMap_mem_pairIdeal _ (fun x hx y hy => ?_) (hmem j i)
    rw [hΓ, pairLift_comp_wMul, toConv_ofConv]
    exact Subgroup.mul_mem _ ((hΓ j x).1 hx) ((hΓ j y).1 hy)
  · intro j _ i
    rw [← hspan]
    refine baseMap_mem_pairIdeal _ (fun x hx y _ => ?_) (hmem j i)
    rw [hΓ, pairLift_comp_wInv, toConv_ofConv]
    exact Subgroup.inv_mem _ ((hΓ j x).1 hx)
  · intro j _ i
    rw [← hspan]
    refine baseMap_mem_pairIdeal _ (fun x hx y hy => ?_) (hmem (j + 1) i)
    rw [hΓ, pairLift_comp_wComm, toConv_ofConv]
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 ((hΓ j x).1 hx)
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 ((hΓ j y).1 hy)
    rw [← hax, ← hby, ← map_commutatorElement]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator ha hb
  · intro h _
    rw [hg n]
    intro x hx
    have h1 := (hΓ n x).1 hx
    rw [hn, Subgroup.map_bot, Subgroup.mem_bot] at h1
    have h2 : x = (1 : WithConv (H →ₐ[k] K)).ofConv := by rw [← h1]
    rw [map_sub, extPoint_tmul, one_mul, Algebra.TensorProduct.algebraMap_apply, extPoint_tmul,
      map_one, mul_one, h2, AlgHom.convOne_apply, sub_self]
  · intro i x hx
    refine hmem 0 i x ((hΓ 0 x).2 (Subgroup.mem_map.2 ⟨⟨toConv x, hx⟩, ?_, rfl⟩))
    rw [derivedSeries_zero]
    exact Subgroup.mem_top _

end KSide

section Transfer

variable {k : Type*} [Field k]
variable {R R' : Type*} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']

/-- Change of coefficients `R ⊗[k] M → R' ⊗[k] M` along `ψ : R → R'`. -/
def coeffMap (ψ : R →ₐ[k] R') {M : Type*} [CommRing M] [Algebra k M] :
    R ⊗[k] M →ₐ[k] R' ⊗[k] M :=
  Algebra.TensorProduct.map ψ (AlgHom.id k M)

@[simp]
theorem coeffMap_tmul (ψ : R →ₐ[k] R') {M : Type*} [CommRing M] [Algebra k M] (a : R) (m : M) :
    coeffMap ψ (a ⊗ₜ m) = ψ a ⊗ₜ m := rfl

theorem coeffMap_baseMap (ψ : R →ₐ[k] R') {M N : Type*} [CommRing M] [Algebra k M] [CommRing N]
    [Algebra k N] (w : M →ₐ[k] N) (t : R ⊗[k] M) :
    coeffMap ψ (baseMap w t) = baseMap w (coeffMap ψ t) := by
  induction t with
  | tmul a m => rfl
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

theorem extPoint_coeffMap (ψ : R →ₐ[k] R') {M : Type*} [CommRing M] [Algebra k M]
    (x : M →ₐ[k] R) (t : R ⊗[k] M) :
    ψ (extPoint x t) = extPoint (ψ.comp x) (coeffMap ψ t) := by
  induction t with
  | tmul a m => simp
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

theorem comp_one_ofConv {H : Type*} [CommRing H] [HopfAlgebra k H] (ψ : R →ₐ[k] R') :
    ψ.comp (1 : WithConv (H →ₐ[k] R)).ofConv = (1 : WithConv (H →ₐ[k] R')).ofConv := by
  ext h
  simp [AlgHom.convOne_apply]

theorem coeffMap_injective (ψ : R →ₐ[k] R') (hψ : Function.Injective ψ) (M : Type*)
    [CommRing M] [Algebra k M] : Function.Injective (coeffMap (M := M) ψ) := by
  have heq : (coeffMap (M := M) ψ).toLinearMap = ψ.toLinearMap.rTensor M :=
    TensorProduct.ext' fun _ _ => rfl
  intro x y hxy
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) ψ.toLinearMap hψ
  rw [← heq]
  exact hxy

theorem map_mem_span {B C F : Type*} [CommRing B] [CommRing C] [FunLike F B C]
    [RingHomClass F B C] (f : F) {ι : Type*} {v : ι → B} {t : B}
    (ht : t ∈ Ideal.span (Set.range v)) : f t ∈ Ideal.span (Set.range fun i => f (v i)) := by
  have h := Ideal.mem_map_of_mem f ht
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h

theorem mem_span_of_injective {B C F : Type*} [CommRing B] [CommRing C] [FunLike F B C]
    [RingHomClass F B C] (f : F) (hf : Function.Injective f) {ι : Type*} [Fintype ι] {t : B}
    {v : ι → B} {c : ι → C} (hc : ∀ l, c l ∈ Set.range f) (h : f t = ∑ l, c l * f (v l)) :
    t ∈ Ideal.span (Set.range v) := by
  choose c' hc' using hc
  have ht : t = ∑ l, c' l * v l := hf (by simp only [map_sum, map_mul, hc', h])
  rw [ht]
  exact Ideal.mem_span_range_iff_exists_fun.2 ⟨c', rfl⟩

variable {H : Type*} [CommRing H] [HopfAlgebra k H]

theorem coeffMap_pairFam (ψ : R →ₐ[k] R') {ι : Type*} (v : ι → R ⊗[k] H) (l : ι ⊕ ι) :
    coeffMap ψ (pairFam v l) = pairFam (fun i => coeffMap ψ (v i)) l := by
  cases l <;> simp [pairFam, coeffMap_baseMap]

/-- Law systems are stable under change of coefficients. -/
theorem IsLawSystem.map {n : ℕ} {s : Set H} {r : ℕ → ℕ} {g : (j : ℕ) → Fin (r j) → R ⊗[k] H}
    (hg : IsLawSystem R n s g) (ψ : R →ₐ[k] R') :
    IsLawSystem R' n s (fun j i => coeffMap ψ (g j i)) where
  one j hj i := by
    rw [← comp_one_ofConv ψ, ← extPoint_coeffMap, hg.one j hj i, map_zero]
  mul j hj i := by
    have h := map_mem_span (coeffMap ψ) (hg.mul j hj i)
    rw [coeffMap_baseMap] at h
    simpa only [coeffMap_pairFam] using h
  inv j hj i := by
    have h := map_mem_span (coeffMap ψ) (hg.inv j hj i)
    rw [coeffMap_baseMap] at h
    simpa only [coeffMap_pairFam] using h
  comm j hj i := by
    have h := map_mem_span (coeffMap ψ) (hg.comm j hj i)
    rw [coeffMap_baseMap] at h
    simpa only [coeffMap_pairFam] using h
  fin h hh := by
    have h' := map_mem_span (coeffMap ψ) (hg.fin h hh)
    rwa [map_sub, coeffMap_tmul, map_one, AlgHom.commutes] at h'

end Transfer

section Descent

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem eventually_mem_range {M : Type*} [CommRing M] [Algebra k M] (t : K ⊗[k] M) :
    ∀ᶠ F : Finset K in Filter.atTop,
      t ∈ (coeffMap (M := M) (Algebra.adjoin k (F : Set K)).val).range := by
  induction t with
  | tmul a m =>
    refine Filter.eventually_atTop.2 ⟨{a}, fun F hF => (AlgHom.mem_range _).2
      ⟨⟨a, Algebra.subset_adjoin (Finset.mem_coe.2 (hF (Finset.mem_singleton_self a)))⟩ ⊗ₜ m,
        rfl⟩⟩
  | add t₁ t₂ h₁ h₂ => exact (h₁.and h₂).mono fun F h => add_mem h.1 h.2

theorem eventually_coeffs {M : Type*} [CommRing M] [Algebra k M] {ι : Type*} [Fintype ι]
    {v : ι → K ⊗[k] M} {t : K ⊗[k] M} (ht : t ∈ Ideal.span (Set.range v)) :
    ∀ᶠ F : Finset K in Filter.atTop, ∃ c : ι → K ⊗[k] M,
      (∀ l, c l ∈ Set.range (coeffMap (M := M) (Algebra.adjoin k (F : Set K)).val)) ∧
        ∑ l, c l * v l = t := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 ht
  exact (Filter.eventually_all.2 fun l => eventually_mem_range (c l)).mono fun F hF =>
    ⟨c, fun l => (AlgHom.mem_range _).1 (hF l), hc⟩

variable {H : Type*} [CommRing H] [HopfAlgebra k H]

/-- **Descent.** A law system over `K` with finitely many conditions in its last family comes
from a law system over a finitely generated `k`-subalgebra of `K`. -/
theorem IsLawSystem.descend {n : ℕ} {s : Set H} (hs : s.Finite) {r : ℕ → ℕ}
    {g : (j : ℕ) → Fin (r j) → K ⊗[k] H} (hg : IsLawSystem K n s g) :
    ∃ F : Finset K, ∃ g' : (j : ℕ) → Fin (r j) → Algebra.adjoin k (F : Set K) ⊗[k] H,
      IsLawSystem (Algebra.adjoin k (F : Set K)) n s g' ∧
        ∀ j ≤ n, ∀ i, coeffMap (Algebra.adjoin k (F : Set K)).val (g' j i) = g j i := by
  have e1 : ∀ᶠ F : Finset K in Filter.atTop, ∀ j ∈ Set.Iic n, ∀ i,
      g j i ∈ (coeffMap (M := H) (Algebra.adjoin k (F : Set K)).val).range :=
    (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j _ =>
      Filter.eventually_all.2 fun i => eventually_mem_range _
  have e2 := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j hj =>
    Filter.eventually_all.2 fun i => eventually_coeffs (hg.mul j hj i)
  have e3 := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun j hj =>
    Filter.eventually_all.2 fun i => eventually_coeffs (hg.inv j hj i)
  have e4 := (Filter.eventually_all_finite (Set.finite_Iio n)).2 fun j hj =>
    Filter.eventually_all.2 fun i => eventually_coeffs (hg.comm j hj i)
  have e5 := (Filter.eventually_all_finite hs).2 fun h hh => eventually_coeffs (hg.fin h hh)
  obtain ⟨F, h1, h2, h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  set A := Algebra.adjoin k (F : Set K)
  let g' : (j : ℕ) → Fin (r j) → A ⊗[k] H := fun j i =>
    Function.invFun (coeffMap (M := H) A.val) (g j i)
  have hgg' : ∀ j ≤ n, ∀ i, coeffMap A.val (g' j i) = g j i := fun j hj i =>
    Function.invFun_eq ((AlgHom.mem_range _).1 (h1 j hj i))
  have hinj := coeffMap_injective (M := H ⊗[k] H) A.val Subtype.val_injective
  have hpair : ∀ j ≤ n, ∀ l, coeffMap A.val (pairFam (g' j) l) = pairFam (g j) l := by
    intro j hj l
    rw [coeffMap_pairFam]
    simp only [hgg' j hj]
  refine ⟨F, g', ⟨fun j hj i => ?_, fun j hj i => ?_, fun j hj i => ?_, fun j hj i => ?_,
    fun h hh => ?_⟩, hgg'⟩
  · have h := extPoint_coeffMap A.val (1 : WithConv (H →ₐ[k] A)).ofConv (g' j i)
    rw [comp_one_ofConv, hgg' j hj i, hg.one j hj i] at h
    exact Subtype.ext h
  · obtain ⟨c, hc, hsum⟩ := h2 j hj i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' j hj i, ← hsum]
    simp only [hpair j hj]
  · obtain ⟨c, hc, hsum⟩ := h3 j hj i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' j hj i, ← hsum]
    simp only [hpair j hj]
  · obtain ⟨c, hc, hsum⟩ := h4 j hj i
    refine mem_span_of_injective _ hinj hc ?_
    rw [coeffMap_baseMap, hgg' (j + 1) hj i, ← hsum]
    simp only [hpair j (Nat.le_of_lt hj)]
  · obtain ⟨c, hc, hsum⟩ := h5 h hh
    refine mem_span_of_injective _ (coeffMap_injective (M := H) A.val Subtype.val_injective) hc ?_
    rw [map_sub, coeffMap_tmul, map_one, AlgHom.commutes, ← hsum]
    simp only [hgg' n le_rfl]

end Descent

section Specialization

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- Specialization `A ⊗[k] M → M` at a `k`-point `φ` of `A`. -/
def specMap (φ : A →ₐ[k] k) {M : Type*} [CommRing M] [Algebra k M] : A ⊗[k] M →ₐ[k] M :=
  (Algebra.TensorProduct.lid k M).toAlgHom.comp (coeffMap φ)

@[simp]
theorem specMap_tmul (φ : A →ₐ[k] k) {M : Type*} [CommRing M] [Algebra k M] (a : A) (m : M) :
    specMap φ (a ⊗ₜ m) = φ a • m := rfl

theorem extPoint_eq_lid {H : Type*} [CommRing H] [Algebra k H] (x : H →ₐ[k] k) (u : k ⊗[k] H) :
    extPoint x u = x (Algebra.TensorProduct.lid k H u) := by
  induction u with
  | tmul a h => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, h₁, h₂]

theorem sub_specMap_mem {H : Type*} [CommRing H] [Algebra k H] (φ : A →ₐ[k] k)
    (d : A ⊗[k] H) :
    d - Algebra.TensorProduct.includeRight (specMap φ d) ∈
      (RingHom.ker φ).map (algebraMap A (A ⊗[k] H)) := by
  induction d with
  | tmul a h =>
    have e : a ⊗ₜ[k] h - Algebra.TensorProduct.includeRight (specMap φ (a ⊗ₜ h)) =
        algebraMap A (A ⊗[k] H) (a - algebraMap k A (φ a)) * (1 ⊗ₜ h) := by
      rw [specMap_tmul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, sub_tmul,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  | add x y hx hy =>
    have h := Ideal.add_mem _ hx hy
    rwa [← add_sub_add_comm, ← map_add, ← map_add] at h

theorem nonempty_algHom_of_finiteType [IsAlgClosed k] (B : Type*) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [Nontrivial B] : Nonempty (B →ₐ[k] k) := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  let : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite k (B ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ 𝔪)
  have hbij : Function.Bijective (algebraMap k (B ⧸ 𝔪)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨((AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ 𝔪)) hbij).symm : (B ⧸ 𝔪) →ₐ[k] k).comp
    (Ideal.Quotient.mkₐ k 𝔪)⟩

variable {K H : Type*} [Field K] [Algebra k K] [CommRing H] [Algebra k H]

/-- **Specialization.** Let `ι : A → K` be injective with `A` Noetherian, `φ` a `k`-point of
`A`, `Q` a prime of `K ⊗[k] H` inside the extension of a prime `P` of `H` but not containing
it. Then some prime `𝔭 < P` of `H` contains the specializations at `φ` of all elements of
`A ⊗[k] H` whose image lies in `Q`. -/
theorem exists_isPrime_lt_specMap [IsNoetherianRing A] [Algebra.FiniteType k H]
    (ι : A →ₐ[k] K) (hι : Function.Injective ι) (φ : A →ₐ[k] k)
    (Q : Ideal (K ⊗[k] H)) [Q.IsPrime] (P : Ideal H) [P.IsPrime]
    (hQP : ∀ q ∈ Q, baseMap (K := K) (Ideal.Quotient.mkₐ k P) q = 0)
    (hlt : ∃ p ∈ P, (1 : K) ⊗ₜ[k] p ∉ Q) :
    ∃ 𝔭 : Ideal H, 𝔭.IsPrime ∧ 𝔭 < P ∧ ∀ d : A ⊗[k] H, coeffMap ι d ∈ Q → specMap φ d ∈ 𝔭 := by
  have : IsNoetherianRing (A ⊗[k] H) := Algebra.FiniteType.isNoetherianRing A _
  let QA : Ideal (A ⊗[k] H) := Q.comap (coeffMap ι)
  let PA : Ideal (A ⊗[k] H) := RingHom.ker (baseMap (K := A) (Ideal.Quotient.mkₐ k P))
  let M : Ideal (A ⊗[k] H) := P.comap (specMap φ)
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : QA.IsPrime := Ideal.comap_isPrime _ _
  have : M.IsPrime := Ideal.comap_isPrime _ _
  have hQA : QA < PA := by
    obtain ⟨p, hp, hpQ⟩ := hlt
    refine lt_of_le_of_ne (fun q hq => ?_) fun h => ?_
    · rw [RingHom.mem_ker]
      apply coeffMap_injective ι hι (H ⧸ P)
      rw [map_zero, coeffMap_baseMap]
      exact hQP _ hq
    · have hpA : (1 : A) ⊗ₜ[k] p ∈ PA := by
        rw [RingHom.mem_ker, baseMap_tmul, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.2 hp, TensorProduct.tmul_zero]
      rw [← h] at hpA
      apply hpQ
      have h' : coeffMap ι ((1 : A) ⊗ₜ[k] p) ∈ Q := hpA
      rwa [coeffMap_tmul, map_one] at h'
  have hPM : PA ≤ M := by
    intro d hd
    rw [RingHom.mem_ker] at hd
    change specMap φ d ∈ P
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have key : ∀ d : A ⊗[k] H, Ideal.Quotient.mk P (specMap φ d) =
        specMap φ (baseMap (K := A) (Ideal.Quotient.mkₐ k P) d) := by
      intro d
      induction d with
      | tmul a h => simp [Algebra.smul_def]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [key, hd, map_zero]
  have hM : M.comap (algebraMap A (A ⊗[k] H)) = RingHom.ker φ := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change specMap φ (algebraMap A (A ⊗[k] H) a) ∈ P ↔ φ a = 0
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, specMap_tmul]
    constructor
    · intro h
      by_contra hne
      apply (‹P.IsPrime›).ne_top
      rw [Ideal.eq_top_iff_one]
      have h' := P.smul_of_tower_mem (φ a)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h'
    · intro h
      rw [h, zero_smul]
      exact P.zero_mem
  have hsurj : Function.Surjective (baseMap (K := A) (Ideal.Quotient.mkₐ k P)) := by
    intro y
    induction y with
    | tmul a z =>
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨a ⊗ₜ h, rfl⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  have : Module.Flat A ((A ⊗[k] H) ⧸ PA) :=
    Module.Flat.of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).toLinearEquiv
  obtain ⟨q, hq, hQq, hqM⟩ := exists_isPrime_lt_of_flat (RingHom.ker φ) hQA hPM hM
  have hkey : ∀ d : A ⊗[k] H, d ∈ q ↔ Algebra.TensorProduct.includeRight (specMap φ d) ∈ q := by
    intro d
    have hd : d - Algebra.TensorProduct.includeRight (specMap φ d) ∈ q :=
      hQq (Ideal.mem_sup_right (sub_specMap_mem φ d))
    constructor
    · intro h
      have h' := q.sub_mem h hd
      rwa [sub_sub_cancel] at h'
    · intro h
      have h' := q.add_mem hd h
      rwa [sub_add_cancel] at h'
  refine ⟨q.comap (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H),
    Ideal.comap_isPrime _ _, lt_of_le_of_ne (fun h hh => ?_) fun heq => ?_, fun d hd => ?_⟩
  · have h' : specMap φ (Algebra.TensorProduct.includeRight h) ∈ P := hqM.le hh
    rwa [Algebra.TensorProduct.includeRight_apply, specMap_tmul, map_one, one_smul] at h'
  · obtain ⟨d, hdM, hdq⟩ := SetLike.exists_of_lt hqM
    apply hdq
    rw [hkey]
    change specMap φ d ∈ q.comap (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H)
    rw [heq]
    exact hdM
  · change Algebra.TensorProduct.includeRight (specMap φ d) ∈ q
    rw [← hkey]
    exact hQq (Ideal.mem_sup_left hd)

end Specialization

section Rational

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The `k`-points vanishing on the `j`-th family of a law system over `k`. -/
def lawSubgroup {n : ℕ} {s : Set H} {r : ℕ → ℕ} {g : (j : ℕ) → Fin (r j) → k ⊗[k] H}
    (hg : IsLawSystem k n s g) (j : ℕ) (hj : j ≤ n) : Subgroup (WithConv (H →ₐ[k] k)) where
  carrier := {z | ∀ i, extPoint z.ofConv (g j i) = 0}
  one_mem' := hg.one j hj
  mul_mem' {a b} ha hb i := by
    have h := extPoint_pairLift_eq_zero ha hb (hg.mul j hj i)
    rwa [pairLift_comp_wMul, toConv_ofConv, toConv_ofConv] at h
  inv_mem' {a} ha i := by
    have h := extPoint_pairLift_eq_zero ha ha (hg.inv j hj i)
    rwa [pairLift_comp_wInv, toConv_ofConv] at h

theorem mem_lawSubgroup {n : ℕ} {s : Set H} {r : ℕ → ℕ} {g : (j : ℕ) → Fin (r j) → k ⊗[k] H}
    (hg : IsLawSystem k n s g) {j : ℕ} (hj : j ≤ n) {z : WithConv (H →ₐ[k] k)} :
    z ∈ lawSubgroup hg j hj ↔ ∀ i, extPoint z.ofConv (g j i) = 0 := Iff.rfl

theorem commutator_mem_lawSubgroup {n : ℕ} {s : Set H} {r : ℕ → ℕ}
    {g : (j : ℕ) → Fin (r j) → k ⊗[k] H} (hg : IsLawSystem k n s g) {j : ℕ} (hj : j < n)
    {a b : WithConv (H →ₐ[k] k)} (ha : a ∈ lawSubgroup hg j hj.le)
    (hb : b ∈ lawSubgroup hg j hj.le) : ⁅a, b⁆ ∈ lawSubgroup hg (j + 1) hj := by
  intro i
  have h := extPoint_pairLift_eq_zero ha hb (hg.comm j hj i)
  rwa [pairLift_comp_wComm, toConv_ofConv, toConv_ofConv] at h

/-- **Solvability over `k`.** If `s` generates `H`, a law system over `k` defines a solvable
group of `k`-points containing every point that vanishes on the first family. -/
theorem exists_solvable_of_isLawSystem {n : ℕ} {s : Set H} {r : ℕ → ℕ}
    {g : (j : ℕ) → Fin (r j) → k ⊗[k] H} (hg : IsLawSystem k n s g)
    (hs : Algebra.adjoin k s = ⊤) :
    ∃ Γ : Subgroup (WithConv (H →ₐ[k] k)), Group.IsSolvable Γ ∧
      ∀ x : H →ₐ[k] k, (∀ i, extPoint x (g 0 i) = 0) → toConv x ∈ Γ := by
  let Γ := lawSubgroup hg 0 (Nat.zero_le n)
  have hD : ∀ j (hj : j ≤ n), ∀ z ∈ derivedSeries Γ j,
      (z : WithConv (H →ₐ[k] k)) ∈ lawSubgroup hg j hj := by
    intro j
    induction j with
    | zero => intro _ z _; exact z.2
    | succ j ih =>
      intro hj z hz
      rw [derivedSeries_succ] at hz
      have hle : ⁅derivedSeries Γ j, derivedSeries Γ j⁆ ≤
          (lawSubgroup hg (j + 1) hj).comap Γ.subtype := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_comap, map_commutatorElement]
        exact commutator_mem_lawSubgroup hg (Nat.lt_of_succ_le hj) (ih _ a ha) (ih _ b hb)
      exact hle hz
  refine ⟨Γ, (Group.isSolvable_def _).2 ⟨n, ?_⟩, fun x hx => hx⟩
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hz' := hD n le_rfl z hz
  change (z : WithConv (H →ₐ[k] k)) = 1
  apply WithConv.ofConv_injective
  refine AlgHom.ext_of_adjoin_eq_top hs fun h hh => ?_
  have hker : Ideal.span (Set.range (g n)) ≤
      RingHom.ker (extPoint (z : WithConv (H →ₐ[k] k)).ofConv) :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz' i)
  have h' := hker (hg.fin h hh)
  rw [RingHom.mem_ker, map_sub, extPoint_tmul, one_mul, Algebra.TensorProduct.algebraMap_apply,
    extPoint_tmul, map_one, mul_one, sub_eq_zero] at h'
  rw [h', AlgHom.convOne_apply]

end Rational

section Core

/-- **The algebraic core of maximality.** Let `k ⊆ K` with `k` algebraically closed, `H` a
finitely generated commutative Hopf algebra over `k`, `S` a solvable group of `K`-points of `H`
whose vanishing ideal `Q ⊆ K ⊗[k] H` is prime, and `P` a prime of `H` such that `Q` lies in the
extension of `P` without containing `1 ⊗ P`. Then there is a prime `𝔭 < P` of `H` and a
solvable group of `k`-points containing every `k`-point on which `𝔭` vanishes. -/
theorem exists_isPrime_lt_of_solvable {k K H : Type*} [Field k] [IsAlgClosed k] [Field K]
    [Algebra k K] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (S : Subgroup (WithConv (H →ₐ[k] K))) [Group.IsSolvable S]
    (Q : Ideal (K ⊗[k] H)) [Q.IsPrime]
    (hSQ : ∀ q, q ∈ Q ↔ ∀ x : H →ₐ[k] K, toConv x ∈ S → extPoint x q = 0)
    (P : Ideal H) [P.IsPrime]
    (hQP : ∀ q ∈ Q, baseMap (K := K) (Ideal.Quotient.mkₐ k P) q = 0)
    (hlt : ∃ p ∈ P, (1 : K) ⊗ₜ[k] p ∉ Q) :
    ∃ 𝔭 : Ideal H, 𝔭.IsPrime ∧ 𝔭 < P ∧ ∃ Γ : Subgroup (WithConv (H →ₐ[k] k)),
      Group.IsSolvable Γ ∧ ∀ x : H →ₐ[k] k, 𝔭 ≤ RingHom.ker x → toConv x ∈ Γ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
  obtain ⟨n, r, g, hg, hg0⟩ := exists_isLawSystem S (s : Set H)
  obtain ⟨F, g', hg', hgg'⟩ := hg.descend s.finite_toSet
  have : Algebra.FiniteType k (Algebra.adjoin k (F : Set K)) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset F)
  have : IsNoetherianRing (Algebra.adjoin k (F : Set K)) :=
    Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨φ⟩ := nonempty_algHom_of_finiteType (k := k) (Algebra.adjoin k (F : Set K))
  obtain ⟨𝔭, h𝔭, h𝔭P, h𝔭d⟩ :=
    exists_isPrime_lt_specMap (Algebra.adjoin k (F : Set K)).val Subtype.val_injective φ Q P hQP hlt
  obtain ⟨Γ, hΓ, hΓx⟩ := exists_solvable_of_isLawSystem (hg'.map φ) hs
  refine ⟨𝔭, h𝔭, h𝔭P, Γ, hΓ, fun x hx => hΓx x fun i => ?_⟩
  have hQ : coeffMap (Algebra.adjoin k (F : Set K)).val (g' 0 i) ∈ Q := by
    rw [hgg' 0 (Nat.zero_le n) i, hSQ]
    exact fun x hx => hg0 i x hx
  rw [extPoint_eq_lid]
  exact hx (h𝔭d _ hQ)

end Core

end Langlands.GroupScheme.BorelFieldExtension
