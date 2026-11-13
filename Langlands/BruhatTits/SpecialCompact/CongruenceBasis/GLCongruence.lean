import Langlands.GroupScheme.Dynamic.GeneralLinearCell
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit

/-! # Principal congruence subgroups of `GL_N` and their block factorizations -/

noncomputable section

open Matrix

namespace Langlands.BruhatTits.SpecialCompact.CongruenceGL

open Langlands.GroupScheme.GeneralLinear

variable {N : ℕ}

section Ring

variable (R : Type*) [CommRing R] (I : Ideal R)

/-- The principal congruence subgroup of level `I`: the kernel of reduction modulo `I`. -/
def kernel : Subgroup (GL (Fin N) R) :=
  (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk I)).ker

variable {R I}

omit [CommRing R] in
theorem ringHom_one_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i j : Fin N) : f ((1 : Matrix (Fin N) (Fin N) R) i j) = (1 : Matrix (Fin N) (Fin N) S) i j :=
  congrFun (congrFun (Matrix.map_one f (map_zero f) (map_one f)) i) j

theorem mem_kernel_iff {C : GL (Fin N) R} :
    C ∈ kernel R I ↔
      ∀ i j, (C : Matrix (Fin N) (Fin N) R) i j - (1 : Matrix (Fin N) (Fin N) R) i j ∈ I := by
  rw [kernel, MonoidHom.mem_ker, Units.ext_iff]
  constructor
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [Units.val_one] at h'
    rw [← Ideal.Quotient.eq]
    rw [ringHom_one_apply]
    exact h'
  · intro h
    ext i j
    rw [Units.val_one]
    have h' := (Ideal.Quotient.eq (I := I)).2 (h i j)
    rw [ringHom_one_apply] at h'
    exact h'

end Ring

section Block

variable {A : Type*} [CommRing A] (e : Fin N → ℤ)

theorem blockLeviSubgroup_le_blockParabolicSubgroup :
    blockLeviSubgroup A e ≤ blockParabolicSubgroup A e :=
  fun _ hg i j hij => hg i j (ne_of_lt (show e i < e j from hij))

theorem blockUnipotentSubgroup_le_blockParabolicSubgroup :
    blockUnipotentSubgroup A e ≤ blockParabolicSubgroup A e := by
  intro g hg i j hij
  rw [hg i j hij.le]
  exact Matrix.one_apply_ne fun h => hij.ne (congrArg e h.symm)

theorem disjoint_blockLeviSubgroup_blockUnipotentSubgroup :
    Disjoint (blockLeviSubgroup A e) (blockUnipotentSubgroup A e) := by
  rw [Subgroup.disjoint_def]
  intro g hL hU
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  rcases le_or_gt (e i) (e j) with h | h
  · exact hU i j h
  · rw [hL i j h.ne']
    exact (Matrix.one_apply_ne fun hij => h.ne' (congrArg e hij)).symm

theorem disjoint_blockUnipotentSubgroup_neg_blockParabolicSubgroup :
    Disjoint (blockUnipotentSubgroup A (-e)) (blockParabolicSubgroup A e) :=
  disjoint_iff.2 (blockUnipotentSubgroup_neg_inf_blockParabolicSubgroup e)

/-- Uniqueness of the ordered opposite-unipotent, Levi, unipotent factorization in `GL_N(A)`. -/
theorem blockTriple_injective :
    Function.Injective (fun t : blockUnipotentSubgroup A (-e) × blockLeviSubgroup A e ×
        blockUnipotentSubgroup A e => (t.1 : GL (Fin N) A) * t.2.1 * t.2.2) := by
  intro a b hab
  let P := blockParabolicSubgroup A e
  let toPair (t : blockUnipotentSubgroup A (-e) × blockLeviSubgroup A e ×
      blockUnipotentSubgroup A e) : blockUnipotentSubgroup A (-e) × P :=
    (t.1, ⟨(t.2.1 : GL (Fin N) A) * (t.2.2 : GL (Fin N) A),
      P.mul_mem (blockLeviSubgroup_le_blockParabolicSubgroup e t.2.1.property)
        (blockUnipotentSubgroup_le_blockParabolicSubgroup e t.2.2.property)⟩)
  have hp : toPair a = toPair b :=
    Subgroup.mul_injective_of_disjoint
      (disjoint_blockUnipotentSubgroup_neg_blockParabolicSubgroup e) (by
        simpa only [toPair, mul_assoc] using hab)
  have hfirst : a.1 = b.1 := congrArg (fun t : blockUnipotentSubgroup A (-e) × P => t.1) hp
  have hlast : a.2 = b.2 :=
    Subgroup.mul_injective_of_disjoint (disjoint_blockLeviSubgroup_blockUnipotentSubgroup e)
      (congrArg (fun t : blockUnipotentSubgroup A (-e) × P => (t.2 : GL (Fin N) A)) hp)
  exact Prod.ext hfirst hlast

/-- If an ordered block product is the identity, so is each factor. -/
theorem eq_one_of_blockTriple_eq_one {u d v : GL (Fin N) A}
    (hu : u ∈ blockUnipotentSubgroup A (-e)) (hd : d ∈ blockLeviSubgroup A e)
    (hv : v ∈ blockUnipotentSubgroup A e) (h : u * d * v = 1) :
    u = 1 ∧ d = 1 ∧ v = 1 := by
  have key : ((⟨u, hu⟩, ⟨d, hd⟩, ⟨v, hv⟩) : blockUnipotentSubgroup A (-e) ×
      blockLeviSubgroup A e × blockUnipotentSubgroup A e) = (1, 1, 1) :=
    blockTriple_injective e (by simpa using h)
  simp only [Prod.mk.injEq, Subtype.ext_iff, Subgroup.coe_one] at key
  exact key

/-- The block diagonal part of a block diagonal matrix is the matrix itself. -/
theorem blockDiagonalPart_blockDiagonalPart (M : Matrix (Fin N) (Fin N) A) :
    blockDiagonalPart A e (blockDiagonalPart A e M) = blockDiagonalPart A e M := by
  ext i j
  simp only [blockDiagonalPart_apply]
  split_ifs <;> rfl

theorem blockLeviProjection_mem (p : blockParabolicSubgroup A e) :
    blockLeviProjection A e p ∈ blockLeviSubgroup A e := by
  intro i j hij
  rw [coe_blockLeviProjection, blockDiagonalPart_apply]
  simp [hij]

/-- The Levi projection of a block parabolic matrix leaves a block unipotent quotient. -/
theorem inv_blockLeviProjection_mul_mem (p : blockParabolicSubgroup A e) :
    (blockLeviProjection A e p)⁻¹ * (p : GL (Fin N) A) ∈ blockUnipotentSubgroup A e := by
  have hL := blockLeviProjection_mem e p
  have hLinv := (blockLeviSubgroup A e).inv_mem hL
  have hLinvP := blockLeviSubgroup_le_blockParabolicSubgroup e hLinv
  refine (blockUnipotent_iff A e _).2 ⟨(blockParabolicSubgroup A e).mul_mem hLinvP p.property, ?_⟩
  rw [Units.val_mul, blockDiagonalPart_mul A e hLinvP p.property]
  have hdiag : blockDiagonalPart A e
      (((blockLeviProjection A e p)⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) =
      (((blockLeviProjection A e p)⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) := by
    ext i j
    rw [blockDiagonalPart_apply]
    split_ifs with h
    · rfl
    · exact (hLinv i j h).symm
  rw [hdiag, ← coe_blockLeviProjection, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- Images of ordered block factors are the ordered block factors of the image. -/
theorem blockTriple_eq_map {B : Type*} [CommRing B] (f : A →+* B)
    {u d v : GL (Fin N) A} (hu : u ∈ blockUnipotentSubgroup A (-e))
    (hd : d ∈ blockLeviSubgroup A e) (hv : v ∈ blockUnipotentSubgroup A e)
    {U D V : GL (Fin N) B} (hU : U ∈ blockUnipotentSubgroup B (-e))
    (hD : D ∈ blockLeviSubgroup B e) (hV : V ∈ blockUnipotentSubgroup B e)
    (h : U * D * V = Matrix.GeneralLinearGroup.map f (u * d * v)) :
    U = Matrix.GeneralLinearGroup.map f u ∧ D = Matrix.GeneralLinearGroup.map f d ∧
      V = Matrix.GeneralLinearGroup.map f v := by
  have key : ((⟨U, hU⟩, ⟨D, hD⟩, ⟨V, hV⟩) : blockUnipotentSubgroup B (-e) ×
      blockLeviSubgroup B e × blockUnipotentSubgroup B e) =
      (⟨_, map_mem_blockUnipotentSubgroup (-e) f hu⟩, ⟨_, map_mem_blockLeviSubgroup e f hd⟩,
        ⟨_, map_mem_blockUnipotentSubgroup e f hv⟩) :=
    blockTriple_injective e (by simpa only [map_mul] using h)
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at key
  exact key

theorem cellMinor_one : cellMinor e (1 : Matrix (Fin N) (Fin N) A) = 1 := by
  unfold cellMinor
  refine Finset.prod_eq_one fun c _ => ?_
  rw [thresholdBlock_one, Matrix.det_one]

end Block

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
  (hI : I ≤ IsLocalRing.maximalIdeal R) (e : Fin N → ℤ)

include hI in
/-- A congruence matrix has invertible cell minor. -/
theorem isUnit_cellMinor_of_mem_kernel {C : GL (Fin N) R} (hC : C ∈ kernel R I) :
    IsUnit (cellMinor e (C : Matrix (Fin N) (Fin N) R)) := by
  have hmap : (C : Matrix (Fin N) (Fin N) R).map (Ideal.Quotient.mk I) = 1 := by
    have h := congrArg (fun X : GL (Fin N) (R ⧸ I) => (X : Matrix (Fin N) (Fin N) (R ⧸ I)))
      ((MonoidHom.mem_ker).1 hC)
    simpa using h
  have h1 : Ideal.Quotient.mk I (cellMinor e (C : Matrix (Fin N) (Fin N) R)) =
      Ideal.Quotient.mk I 1 := by
    rw [map_cellMinor, hmap, cellMinor_one, map_one]
  have hmem : cellMinor e (C : Matrix (Fin N) (Fin N) R) - 1 ∈ IsLocalRing.maximalIdeal R :=
    hI ((Ideal.Quotient.eq).1 h1)
  by_contra hnot
  have hc : cellMinor e (C : Matrix (Fin N) (Fin N) R) ∈ IsLocalRing.maximalIdeal R := hnot
  have := (IsLocalRing.maximalIdeal R).sub_mem hc hmem
  rw [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    ((Ideal.eq_top_iff_one _).2 this)

include hI in
/-- **Block factorization of congruence matrices.** Over a local ring, a matrix congruent to the
identity modulo a proper ideal is an ordered opposite-unipotent, Levi, unipotent product of
three matrices that are again congruent to the identity. -/
theorem exists_kernel_blockTriple {C : GL (Fin N) R} (hC : C ∈ kernel R I) :
    ∃ u ∈ kernel R I ⊓ blockUnipotentSubgroup R (-e),
      ∃ d ∈ kernel R I ⊓ blockLeviSubgroup R e,
        ∃ v ∈ kernel R I ⊓ blockUnipotentSubgroup R e, C = u * d * v := by
  obtain ⟨u, hu, p, hp, rfl⟩ :=
    exists_cell_decomposition e C (isUnit_cellMinor_of_mem_kernel hI e hC)
  set d := blockLeviProjection R e ⟨p, hp⟩ with hd_def
  have hd : (d : GL (Fin N) R) ∈ blockLeviSubgroup R e := blockLeviProjection_mem e ⟨p, hp⟩
  have hv : (d : GL (Fin N) R)⁻¹ * p ∈ blockUnipotentSubgroup R e :=
    inv_blockLeviProjection_mul_mem e ⟨p, hp⟩
  have hprod : u * (d : GL (Fin N) R) * ((d : GL (Fin N) R)⁻¹ * p) = u * p := by
    rw [mul_assoc, mul_inv_cancel_left]
  have hred : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) u *
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (d : GL (Fin N) R) *
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) ((d : GL (Fin N) R)⁻¹ * p) = 1 := by
    rw [← map_mul, ← map_mul, hprod]
    exact (MonoidHom.mem_ker).1 hC
  obtain ⟨h1, h2, h3⟩ := eq_one_of_blockTriple_eq_one e
    (map_mem_blockUnipotentSubgroup (-e) (Ideal.Quotient.mk I) hu)
    (map_mem_blockLeviSubgroup e (Ideal.Quotient.mk I) hd)
    (map_mem_blockUnipotentSubgroup e (Ideal.Quotient.mk I) hv) hred
  exact ⟨u, ⟨h1, hu⟩, d, ⟨h2, hd⟩, _, ⟨h3, hv⟩, hprod.symm⟩

end Local

section Conjugation

variable {R K : Type*} [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
  {I : Ideal R} (e : Fin N → ℤ)

/-- The integral matrix whose image is `diag(t ^ e) X diag(t ^ e)⁻¹` for block parabolic `X`. -/
def conjMatrix (t : R) (C : Matrix (Fin N) (Fin N) R) : Matrix (Fin N) (Fin N) R :=
  fun i j => if e j ≤ e i then t ^ (e i - e j).toNat * C i j else 0

theorem map_conjMatrix (t : R) (u : Kˣ) (hu : (u : K) = f t) {C : GL (Fin N) R}
    (hP : Matrix.GeneralLinearGroup.map f C ∈ blockParabolicSubgroup K e) :
    (conjMatrix e t (C : Matrix (Fin N) (Fin N) R)).map f =
      ((diagonalUnits K e u * Matrix.GeneralLinearGroup.map f C *
        (diagonalUnits K e u)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  ext i j
  rw [diagonalUnits_conj_apply, Matrix.map_apply, conjMatrix]
  split_ifs with hij
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e i - e j = k := Int.eq_ofNat_of_zero_le (by omega)
    have hpow : ((u ^ e i : Kˣ) : K) * ((u⁻¹ ^ e j : Kˣ) : K) = (u : K) ^ k := by
      rw [← Units.val_mul, inv_zpow', ← zpow_add, ← sub_eq_add_neg, hk, zpow_natCast,
        Units.val_pow_eq_pow_val]
    rw [map_mul, map_pow, ← hu, hk, Int.toNat_natCast, mul_right_comm, hpow]
    rfl
  · have h0 : (Matrix.GeneralLinearGroup.map f C : Matrix (Fin N) (Fin N) K) i j = 0 :=
      hP (show OrderDual.toDual (e j) < OrderDual.toDual (e i) from
        (show e i < e j by omega))
    rw [map_zero]
    change 0 = _ * (Matrix.GeneralLinearGroup.map f C : Matrix (Fin N) (Fin N) K) i j * _
    rw [h0, mul_zero, zero_mul]

include hf in
/-- **Conjugation by a nonnegative diagonal power preserves integral congruence matrices that
are block parabolic.** -/
theorem diagonalUnits_conj_mem_map_kernel (t : R) (u : Kˣ) (hu : (u : K) = f t)
    {C : GL (Fin N) R} (hC : C ∈ kernel R I)
    (hP : Matrix.GeneralLinearGroup.map f C ∈ blockParabolicSubgroup K e) :
    diagonalUnits K e u * Matrix.GeneralLinearGroup.map f C * (diagonalUnits K e u)⁻¹ ∈
      (kernel R I).map (Matrix.GeneralLinearGroup.map f) := by
  have hPinv : Matrix.GeneralLinearGroup.map f C⁻¹ ∈ blockParabolicSubgroup K e := by
    rw [map_inv]
    exact (blockParabolicSubgroup K e).inv_mem hP
  have hinj : Function.Injective (fun X : Matrix (Fin N) (Fin N) R => X.map f) :=
    fun X Y h => Matrix.ext fun i j => hf (congrFun (congrFun h i) j)
  have h1 := map_conjMatrix f e t u hu hP
  have h2 := map_conjMatrix f e t u hu hPinv
  have hmul : conjMatrix e t (C : Matrix (Fin N) (Fin N) R) *
      conjMatrix e t ((C⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) = 1 := by
    apply hinj
    simp only [Matrix.map_mul, h1, h2, map_inv, ← Units.val_mul]
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, mul_inv_cancel]
    simp [Matrix.map_one]
  have hmul' : conjMatrix e t ((C⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *
      conjMatrix e t (C : Matrix (Fin N) (Fin N) R) = 1 :=
    mul_eq_one_comm.1 hmul
  let C' : GL (Fin N) R := ⟨_, _, hmul, hmul'⟩
  refine ⟨C', (show C' ∈ kernel R I from mem_kernel_iff.2 ?_), ?_⟩
  · intro i j
    have hCij := (mem_kernel_iff.1 hC) i j
    change conjMatrix e t (C : Matrix (Fin N) (Fin N) R) i j - _ ∈ I
    unfold conjMatrix
    split_ifs with hij
    · by_cases heq : i = j
      · subst heq
        simpa using hCij
      · rw [Matrix.one_apply_ne heq, sub_zero] at hCij ⊢
        exact I.mul_mem_left _ hCij
    · have hne : i ≠ j := fun h => hij (h ▸ le_rfl)
      rw [Matrix.one_apply_ne hne, sub_zero]
      exact I.zero_mem
  · apply Units.ext
    exact h1

end Conjugation

end Langlands.BruhatTits.SpecialCompact.CongruenceGL
