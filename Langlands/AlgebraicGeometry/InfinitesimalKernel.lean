import Langlands.AlgebraicGeometry.AffineChartPoints
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Infinitesimal kernels of group schemes are uniquely divisible

Let `M` be a group object over a scheme `S`, let `D` be an algebra over the sections of an affine
open `S₀` of `S`, and let `I` be an ideal of `D` with `I ^ 2 = 0`. Points of `M` over `Spec D`
that become trivial over `Spec (D / I)` form a group. If the unit section over `Spec (D / I)`
lies in one affine chart of `M` over `S₀`, then this group is uniquely divisible by every natural
number `n` that is invertible in `D`.

The proof only uses the group law through precomposition. Points of the kernel are encoded by
points over the ring `P` of pairs of elements of `D` that agree modulo `I`, and the scaling ring
maps `(a, b) ↦ (a, a + c (b - a))` of `P` act on such points by powers.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

namespace SquareZero

variable (R : Type u) {D : Type u} [CommRing R] [CommRing D] [Algebra R D] (I : Ideal D)

lemma mul_eq_zero (hI : I ^ 2 = ⊥) {u v : D} (hu : u ∈ I) (hv : v ∈ I) : u * v = 0 := by
  have h : u * v ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hu hv
  rwa [hI, Ideal.mem_bot] at h

/-- Pairs of elements of `D` that agree modulo `I`. -/
def pairs : Subalgebra R (D × D) where
  carrier := {x | x.2 - x.1 ∈ I}
  mul_mem' {x y} hx hy := by
    change (x * y).2 - (x * y).1 ∈ I
    have h : (x * y).2 - (x * y).1 = x.2 * (y.2 - y.1) + (x.2 - x.1) * y.1 := by
      simp only [Prod.snd_mul, Prod.fst_mul]
      ring
    rw [h]
    exact I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_right _ hx)
  add_mem' {x y} hx hy := by
    change (x + y).2 - (x + y).1 ∈ I
    have h : (x + y).2 - (x + y).1 = (x.2 - x.1) + (y.2 - y.1) := by
      simp only [Prod.snd_add, Prod.fst_add]
      ring
    rw [h]
    exact I.add_mem hx hy
  algebraMap_mem' r := by
    change (algebraMap R (D × D) r).2 - (algebraMap R (D × D) r).1 ∈ I
    simp

/-- Triples of elements of `D` whose last two entries agree with the first one modulo `I`. -/
def triples : Subalgebra R (D × D × D) where
  carrier := {x | x.2.1 - x.1 ∈ I ∧ x.2.2 - x.1 ∈ I}
  mul_mem' {x y} hx hy := by
    change (x * y).2.1 - (x * y).1 ∈ I ∧ (x * y).2.2 - (x * y).1 ∈ I
    have h1 : (x * y).2.1 - (x * y).1 = x.2.1 * (y.2.1 - y.1) + (x.2.1 - x.1) * y.1 := by
      simp only [Prod.snd_mul, Prod.fst_mul]
      ring
    have h2 : (x * y).2.2 - (x * y).1 = x.2.2 * (y.2.2 - y.1) + (x.2.2 - x.1) * y.1 := by
      simp only [Prod.snd_mul, Prod.fst_mul]
      ring
    rw [h1, h2]
    exact ⟨I.add_mem (I.mul_mem_left _ hy.1) (I.mul_mem_right _ hx.1),
      I.add_mem (I.mul_mem_left _ hy.2) (I.mul_mem_right _ hx.2)⟩
  add_mem' {x y} hx hy := by
    change (x + y).2.1 - (x + y).1 ∈ I ∧ (x + y).2.2 - (x + y).1 ∈ I
    have h1 : (x + y).2.1 - (x + y).1 = (x.2.1 - x.1) + (y.2.1 - y.1) := by
      simp only [Prod.snd_add, Prod.fst_add]
      ring
    have h2 : (x + y).2.2 - (x + y).1 = (x.2.2 - x.1) + (y.2.2 - y.1) := by
      simp only [Prod.snd_add, Prod.fst_add]
      ring
    rw [h1, h2]
    exact ⟨I.add_mem hx.1 hy.1, I.add_mem hx.2 hy.2⟩
  algebraMap_mem' r := by
    change (algebraMap R (D × D × D) r).2.1 - (algebraMap R (D × D × D) r).1 ∈ I ∧
      (algebraMap R (D × D × D) r).2.2 - (algebraMap R (D × D × D) r).1 ∈ I
    simp

variable {R I}

lemma mem_pairs (x : pairs R I) : (x : D × D).2 - (x : D × D).1 ∈ I := x.2

lemma mem_triples (x : triples R I) :
    (x : D × D × D).2.1 - (x : D × D × D).1 ∈ I ∧ (x : D × D × D).2.2 - (x : D × D × D).1 ∈ I :=
  x.2

lemma pairs_ext {x y : pairs R I} (h1 : (x : D × D).1 = (y : D × D).1)
    (h2 : (x : D × D).2 = (y : D × D).2) : x = y :=
  Subtype.ext (Prod.ext h1 h2)

lemma triples_ext {x y : triples R I} (h1 : (x : D × D × D).1 = (y : D × D × D).1)
    (h2 : (x : D × D × D).2.1 = (y : D × D × D).2.1)
    (h3 : (x : D × D × D).2.2 = (y : D × D × D).2.2) : x = y :=
  Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

variable (R I)

/-- The first entry of a pair. -/
def fst : pairs R I →ₐ[R] D := (AlgHom.fst R D D).comp (pairs R I).val

/-- The second entry of a pair. -/
def snd : pairs R I →ₐ[R] D := (AlgHom.snd R D D).comp (pairs R I).val

/-- The first entry of a triple. -/
def t₁ : triples R I →ₐ[R] D := (AlgHom.fst R D (D × D)).comp (triples R I).val

/-- The second entry of a triple. -/
def t₂ : triples R I →ₐ[R] D :=
  (AlgHom.fst R D D).comp ((AlgHom.snd R D (D × D)).comp (triples R I).val)

/-- The third entry of a triple. -/
def t₃ : triples R I →ₐ[R] D :=
  (AlgHom.snd R D D).comp ((AlgHom.snd R D (D × D)).comp (triples R I).val)

variable {R I}

@[simp] lemma fst_apply (x : pairs R I) : fst R I x = (x : D × D).1 := rfl
@[simp] lemma snd_apply (x : pairs R I) : snd R I x = (x : D × D).2 := rfl
@[simp] lemma t₁_apply (x : triples R I) : t₁ R I x = (x : D × D × D).1 := rfl
@[simp] lemma t₂_apply (x : triples R I) : t₂ R I x = (x : D × D × D).2.1 := rfl
@[simp] lemma t₃_apply (x : triples R I) : t₃ R I x = (x : D × D × D).2.2 := rfl

variable {E : Type u} [CommRing E] [Algebra R E]

/-- An algebra map into pairs, from its two entries. -/
def pairsLift (g₁ g₂ : E →ₐ[R] D) (h : ∀ x, g₂ x - g₁ x ∈ I) : E →ₐ[R] pairs R I :=
  (g₁.prod g₂).codRestrict (pairs R I) h

/-- An algebra map into triples, from its three entries. -/
def triplesLift (g₁ g₂ g₃ : E →ₐ[R] D) (h₂ : ∀ x, g₂ x - g₁ x ∈ I)
    (h₃ : ∀ x, g₃ x - g₁ x ∈ I) : E →ₐ[R] triples R I :=
  (g₁.prod (g₂.prod g₃)).codRestrict (triples R I) fun x => ⟨h₂ x, h₃ x⟩

@[simp] lemma pairsLift_apply (g₁ g₂ : E →ₐ[R] D) (h : ∀ x, g₂ x - g₁ x ∈ I) (x : E) :
    (pairsLift g₁ g₂ h x : D × D) = (g₁ x, g₂ x) := rfl

@[simp] lemma triplesLift_apply (g₁ g₂ g₃ : E →ₐ[R] D) (h₂ : ∀ x, g₂ x - g₁ x ∈ I)
    (h₃ : ∀ x, g₃ x - g₁ x ∈ I) (x : E) :
    (triplesLift g₁ g₂ g₃ h₂ h₃ x : D × D × D) = (g₁ x, g₂ x, g₃ x) := rfl

lemma pairs_hom_ext {f f' : E →ₐ[R] pairs R I} (h₁ : (fst R I).comp f = (fst R I).comp f')
    (h₂ : (snd R I).comp f = (snd R I).comp f') : f = f' :=
  AlgHom.ext fun x => pairs_ext (AlgHom.congr_fun h₁ x) (AlgHom.congr_fun h₂ x)

lemma triples_hom_ext {f f' : E →ₐ[R] triples R I} (h₁ : (t₁ R I).comp f = (t₁ R I).comp f')
    (h₂ : (t₂ R I).comp f = (t₂ R I).comp f') (h₃ : (t₃ R I).comp f = (t₃ R I).comp f') :
    f = f' :=
  AlgHom.ext fun x =>
    triples_ext (AlgHom.congr_fun h₁ x) (AlgHom.congr_fun h₂ x) (AlgHom.congr_fun h₃ x)

variable (R I)

/-- The diagonal embedding of `D` into pairs. -/
def diag : D →ₐ[R] pairs R I :=
  pairsLift (AlgHom.id R D) (AlgHom.id R D) fun x => by simp

/-- The algebra map `(a, b) ↦ a + c (b - a)` on pairs; it is multiplicative as `I ^ 2 = 0`. -/
def lin (hI : I ^ 2 = ⊥) (c : D) : pairs R I →ₐ[R] D where
  toFun x := (x : D × D).1 + c * ((x : D × D).2 - (x : D × D).1)
  map_one' := by simp
  map_mul' x y := by
    have h := mul_eq_zero I hI (mem_pairs x) (mem_pairs y)
    simp only [Subalgebra.coe_mul, Prod.fst_mul, Prod.snd_mul]
    linear_combination (c - c ^ 2) * h
  map_zero' := by simp
  map_add' x y := by
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add]
    ring
  commutes' r := by simp

/-- The scaling map `(a, b) ↦ (a, a + c (b - a))` on pairs. -/
def scale (hI : I ^ 2 = ⊥) (c : D) : pairs R I →ₐ[R] pairs R I :=
  pairsLift (fst R I) (lin R I hI c) fun x => by
    change (x : D × D).1 + c * ((x : D × D).2 - (x : D × D).1) - (x : D × D).1 ∈ I
    rw [add_sub_cancel_left]
    exact I.mul_mem_left c (mem_pairs x)

/-- The algebra map `(a, b, b') ↦ b + b' - a` on triples; it is multiplicative as `I ^ 2 = 0`. -/
def sumSnd (hI : I ^ 2 = ⊥) : triples R I →ₐ[R] D where
  toFun x := (x : D × D × D).2.1 + (x : D × D × D).2.2 - (x : D × D × D).1
  map_one' := by simp
  map_mul' x y := by
    have h₁ := mul_eq_zero I hI (mem_triples x).1 (mem_triples y).2
    have h₂ := mul_eq_zero I hI (mem_triples x).2 (mem_triples y).1
    simp only [Subalgebra.coe_mul, Prod.fst_mul, Prod.snd_mul]
    linear_combination -h₁ - h₂
  map_zero' := by simp
  map_add' x y := by
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add]
    ring
  commutes' r := by simp

/-- The projection `(a, b, b') ↦ (a, b)`. -/
def pr₁ : triples R I →ₐ[R] pairs R I :=
  pairsLift (t₁ R I) (t₂ R I) fun x => (mem_triples x).1

/-- The projection `(a, b, b') ↦ (a, b')`. -/
def pr₂ : triples R I →ₐ[R] pairs R I :=
  pairsLift (t₁ R I) (t₃ R I) fun x => (mem_triples x).2

/-- The sum `(a, b, b') ↦ (a, b + b' - a)`. -/
def sum (hI : I ^ 2 = ⊥) : triples R I →ₐ[R] pairs R I :=
  pairsLift (t₁ R I) (sumSnd R I hI) fun x => by
    change (x : D × D × D).2.1 + (x : D × D × D).2.2 - (x : D × D × D).1 - (x : D × D × D).1 ∈ I
    have h : (x : D × D × D).2.1 + (x : D × D × D).2.2 - (x : D × D × D).1 -
        (x : D × D × D).1 =
        ((x : D × D × D).2.1 - (x : D × D × D).1) + ((x : D × D × D).2.2 - (x : D × D × D).1) := by
      ring
    rw [h]
    exact I.add_mem (mem_triples x).1 (mem_triples x).2

variable {R I}

/-- Two maps into pairs with the same first entry give a map into triples. -/
def pair (g₁ g₂ : E →ₐ[R] pairs R I) (h : (fst R I).comp g₁ = (fst R I).comp g₂) :
    E →ₐ[R] triples R I :=
  triplesLift ((fst R I).comp g₁) ((snd R I).comp g₁) ((snd R I).comp g₂)
    (fun x => mem_pairs (g₁ x))
    (fun x => by
      change (g₂ x : D × D).2 - (g₁ x : D × D).1 ∈ I
      rw [show (g₁ x : D × D).1 = (g₂ x : D × D).1 from AlgHom.congr_fun h x]
      exact mem_pairs (g₂ x))

@[simp] lemma lin_apply (hI : I ^ 2 = ⊥) (c : D) (x : pairs R I) :
    lin R I hI c x = (x : D × D).1 + c * ((x : D × D).2 - (x : D × D).1) := rfl

@[simp] lemma sumSnd_apply (hI : I ^ 2 = ⊥) (x : triples R I) :
    sumSnd R I hI x = (x : D × D × D).2.1 + (x : D × D × D).2.2 - (x : D × D × D).1 := rfl

@[simp] lemma diag_apply (d : D) : (diag R I d : D × D) = (d, d) := rfl

@[simp] lemma scale_apply (hI : I ^ 2 = ⊥) (c : D) (x : pairs R I) :
    (scale R I hI c x : D × D) =
      ((x : D × D).1, (x : D × D).1 + c * ((x : D × D).2 - (x : D × D).1)) := rfl

@[simp] lemma pr₁_apply (x : triples R I) :
    (pr₁ R I x : D × D) = ((x : D × D × D).1, (x : D × D × D).2.1) := rfl

@[simp] lemma pr₂_apply (x : triples R I) :
    (pr₂ R I x : D × D) = ((x : D × D × D).1, (x : D × D × D).2.2) := rfl

@[simp] lemma sum_apply (hI : I ^ 2 = ⊥) (x : triples R I) :
    (sum R I hI x : D × D) = ((x : D × D × D).1,
      (x : D × D × D).2.1 + (x : D × D × D).2.2 - (x : D × D × D).1) := rfl

@[simp] lemma pair_apply (g₁ g₂ : E →ₐ[R] pairs R I) (h : (fst R I).comp g₁ = (fst R I).comp g₂)
    (x : E) : (pair g₁ g₂ h x : D × D × D) =
      ((g₁ x : D × D).1, (g₁ x : D × D).2, (g₂ x : D × D).2) := rfl

lemma fst_comp_diag : (fst R I).comp (diag R I) = AlgHom.id R D := rfl

lemma fst_comp_diag_comp_fst : (fst R I).comp ((diag R I).comp (fst R I)) = fst R I := rfl

lemma fst_comp_pairsLift (g₁ g₂ : E →ₐ[R] D) (h : ∀ x, g₂ x - g₁ x ∈ I) :
    (fst R I).comp (pairsLift g₁ g₂ h) = g₁ := AlgHom.ext fun _ => rfl

lemma snd_comp_pairsLift (g₁ g₂ : E →ₐ[R] D) (h : ∀ x, g₂ x - g₁ x ∈ I) :
    (snd R I).comp (pairsLift g₁ g₂ h) = g₂ := AlgHom.ext fun _ => rfl

lemma fst_comp_scale (hI : I ^ 2 = ⊥) (c : D) : (fst R I).comp (scale R I hI c) = fst R I := rfl

lemma scale_zero (hI : I ^ 2 = ⊥) : scale R I hI 0 = (diag R I).comp (fst R I) :=
  AlgHom.ext fun x => pairs_ext (by simp) (by simp)

lemma scale_one (hI : I ^ 2 = ⊥) : scale R I hI 1 = AlgHom.id R (pairs R I) :=
  AlgHom.ext fun x => pairs_ext (by simp) (by simp)

lemma scale_comp_scale (hI : I ^ 2 = ⊥) (c c' : D) :
    (scale R I hI c).comp (scale R I hI c') = scale R I hI (c * c') :=
  AlgHom.ext fun x => pairs_ext (by simp) (by simp; ring)

lemma pr₁_comp_pair (g₁ g₂ : E →ₐ[R] pairs R I) (h : (fst R I).comp g₁ = (fst R I).comp g₂) :
    (pr₁ R I).comp (pair g₁ g₂ h) = g₁ :=
  AlgHom.ext fun x => pairs_ext (by simp) (by simp)

lemma pr₂_comp_pair (g₁ g₂ : E →ₐ[R] pairs R I) (h : (fst R I).comp g₁ = (fst R I).comp g₂) :
    (pr₂ R I).comp (pair g₁ g₂ h) = g₂ :=
  AlgHom.ext fun x => pairs_ext (by simpa using AlgHom.congr_fun h x) (by simp)

lemma t₁_comp_pair (g₁ g₂ : E →ₐ[R] pairs R I) (h : (fst R I).comp g₁ = (fst R I).comp g₂) :
    (t₁ R I).comp (pair g₁ g₂ h) = (fst R I).comp g₁ := rfl

lemma fst_comp_scale_eq (hI : I ^ 2 = ⊥) (c c' : D) :
    (fst R I).comp (scale R I hI c) = (fst R I).comp (scale R I hI c') := by
  rw [fst_comp_scale, fst_comp_scale]

lemma sum_comp_pair_scale (hI : I ^ 2 = ⊥) (c c' : D) :
    (sum R I hI).comp (pair (scale R I hI c) (scale R I hI c') (fst_comp_scale_eq hI c c')) =
      scale R I hI (c + c') :=
  AlgHom.ext fun x => pairs_ext rfl (by
    change (x : D × D).1 + c * ((x : D × D).2 - (x : D × D).1) +
      ((x : D × D).1 + c' * ((x : D × D).2 - (x : D × D).1)) - (x : D × D).1 =
      (x : D × D).1 + (c + c') * ((x : D × D).2 - (x : D × D).1)
    ring)

lemma fst_comp_id_eq : (fst R I).comp (AlgHom.id R (pairs R I)) =
    (fst R I).comp ((diag R I).comp (fst R I)) := rfl

lemma sum_comp_pair_id_diag (hI : I ^ 2 = ⊥) :
    (sum R I hI).comp (pair (AlgHom.id R (pairs R I)) ((diag R I).comp (fst R I))
      fst_comp_id_eq) = AlgHom.id R (pairs R I) :=
  AlgHom.ext fun x => pairs_ext (by simp) (by simp)

lemma sum_comp_pair_diag_id (hI : I ^ 2 = ⊥) :
    (sum R I hI).comp (pair ((diag R I).comp (fst R I)) (AlgHom.id R (pairs R I))
      fst_comp_id_eq.symm) = AlgHom.id R (pairs R I) :=
  AlgHom.ext fun x => pairs_ext (by simp) (by simp)

lemma mk_comp_snd :
    (Ideal.Quotient.mkₐ R I).comp (snd R I) = (Ideal.Quotient.mkₐ R I).comp (fst R I) :=
  AlgHom.ext fun x => Ideal.Quotient.eq.mpr (mem_pairs x)

lemma mk_comp_fst_surjective :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp (fst R I)) := by
  intro z
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨diag R I d, rfl⟩

lemma mk_comp_t₁_surjective :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp (t₁ R I)) := by
  intro z
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨triplesLift (AlgHom.id R D) (AlgHom.id R D) (AlgHom.id R D) (by simp) (by simp) d, rfl⟩

lemma sq_eq_zero (hI : I ^ 2 = ⊥) {d : D} (hd : d ∈ I) : d ^ 2 = 0 := by
  rw [pow_two]
  exact mul_eq_zero I hI hd hd

lemma isNilpotent_ker_mk (hI : I ^ 2 = ⊥) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.mkₐ R I : D →+* D ⧸ I), IsNilpotent x := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  exact ⟨2, sq_eq_zero hI (Ideal.Quotient.eq_zero_iff_mem.mp hx)⟩

lemma isNilpotent_ker_mk_comp_fst (hI : I ^ 2 = ⊥) :
    ∀ x ∈ RingHom.ker ((Ideal.Quotient.mkₐ R I).comp (fst R I) : pairs R I →+* D ⧸ I),
      IsNilpotent x := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have h₁ : (x : D × D).1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
  have h₂ : (x : D × D).2 ∈ I := by
    have := I.add_mem (mem_pairs x) h₁
    rwa [sub_add_cancel] at this
  refine ⟨2, pairs_ext ?_ ?_⟩
  · simpa using sq_eq_zero hI h₁
  · simpa using sq_eq_zero hI h₂

lemma isNilpotent_ker_mk_comp_t₁ (hI : I ^ 2 = ⊥) :
    ∀ x ∈ RingHom.ker ((Ideal.Quotient.mkₐ R I).comp (t₁ R I) : triples R I →+* D ⧸ I),
      IsNilpotent x := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have h₁ : (x : D × D × D).1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
  have h₂ : (x : D × D × D).2.1 ∈ I := by
    have := I.add_mem (mem_triples x).1 h₁
    rwa [sub_add_cancel] at this
  have h₃ : (x : D × D × D).2.2 ∈ I := by
    have := I.add_mem (mem_triples x).2 h₁
    rwa [sub_add_cancel] at this
  refine ⟨2, triples_ext ?_ ?_ ?_⟩
  · simpa using sq_eq_zero hI h₁
  · simpa using sq_eq_zero hI h₂
  · simpa using sq_eq_zero hI h₃

end SquareZero

namespace InfinitesimalKernel

open SquareZero

variable {S : Scheme.{u}} {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)

lemma testHom_comp_assoc {C C' C'' : Type u} [CommRing C] [CommRing C'] [CommRing C'']
    [Algebra Γ(S, S₀) C] [Algebra Γ(S, S₀) C'] [Algebra Γ(S, S₀) C''] {Y : Over S}
    (q : C →ₐ[Γ(S, S₀)] C') (q' : C' →ₐ[Γ(S, S₀)] C'') (x : testObj hS₀ C ⟶ Y) :
    testHom hS₀ q' ≫ testHom hS₀ q ≫ x = testHom hS₀ (q'.comp q) ≫ x := by
  rw [testHom_comp, Category.assoc]

variable {M : Over S} [GrpObj M] {D : Type u} [CommRing D] [Algebra Γ(S, S₀) D] {I : Ideal D}
  (hI : I ^ 2 = ⊥) (W : Chart S₀ M)
  (hW : Set.range (1 : testObj hS₀ (D ⧸ I) ⟶ M).left ⊆ W.U)

include hW in
/-- A point that is trivial on a nil-thickening of `Spec (D / I)` lies in the chart `W`. -/
lemma exists_pt_of_comp_eq_one {E : Type u} [CommRing E] [Algebra Γ(S, S₀) E]
    (q : E →ₐ[Γ(S, S₀)] D ⧸ I) (hq : Function.Surjective q)
    (hnil : ∀ x ∈ RingHom.ker (q : E →+* D ⧸ I), IsNilpotent x)
    (x : testObj hS₀ E ⟶ M) (hx : testHom hS₀ q ≫ x = 1) :
    ∃ ψ : W.Ring →ₐ[Γ(S, S₀)] E, W.pt hS₀ ψ = x :=
  W.exists_pt hS₀ x (by rw [← range_testHom_comp hS₀ q hq hnil x, hx]; exact hW)

include hI hW in
lemma exists_pt_pairs (p : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M)
    (hp : testHom hS₀ (fst Γ(S, S₀) I) ≫ p = 1) :
    ∃ ψ : W.Ring →ₐ[Γ(S, S₀)] pairs Γ(S, S₀) I, W.pt hS₀ ψ = p :=
  exists_pt_of_comp_eq_one hS₀ W hW _ mk_comp_fst_surjective (isNilpotent_ker_mk_comp_fst hI) p
    (by rw [testHom_comp, Category.assoc, hp, MonObj.comp_one])

include hI hW in
lemma exists_pt_triples (x : testObj hS₀ (triples Γ(S, S₀) I) ⟶ M)
    (hx : testHom hS₀ (t₁ Γ(S, S₀) I) ≫ x = 1) :
    ∃ ψ : W.Ring →ₐ[Γ(S, S₀)] triples Γ(S, S₀) I, W.pt hS₀ ψ = x :=
  exists_pt_of_comp_eq_one hS₀ W hW _ mk_comp_t₁_surjective (isNilpotent_ker_mk_comp_t₁ hI) x
    (by rw [testHom_comp, Category.assoc, hx, MonObj.comp_one])

include hI hW in
/-- Points over pairs that are trivial on the first entry are determined by the second entry. -/
lemma pairs_point_ext {p p' : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M}
    (hp : testHom hS₀ (fst Γ(S, S₀) I) ≫ p = 1) (hp' : testHom hS₀ (fst Γ(S, S₀) I) ≫ p' = 1)
    (h : testHom hS₀ (snd Γ(S, S₀) I) ≫ p = testHom hS₀ (snd Γ(S, S₀) I) ≫ p') : p = p' := by
  obtain ⟨ψ, rfl⟩ := exists_pt_pairs hS₀ hI W hW p hp
  obtain ⟨ψ', rfl⟩ := exists_pt_pairs hS₀ hI W hW p' hp'
  simp only [Chart.testHom_comp_pt] at hp hp' h
  congr 1
  exact pairs_hom_ext (W.pt_injective hS₀ (hp.trans hp'.symm)) (W.pt_injective hS₀ h)

include hI hW in
/-- Points over triples that are trivial on the first entry are determined by their two
projections to pairs. -/
lemma triples_point_ext {x y : testObj hS₀ (triples Γ(S, S₀) I) ⟶ M}
    (hx : testHom hS₀ (t₁ Γ(S, S₀) I) ≫ x = 1) (hy : testHom hS₀ (t₁ Γ(S, S₀) I) ≫ y = 1)
    (h₁ : testHom hS₀ (pr₁ Γ(S, S₀) I) ≫ x = testHom hS₀ (pr₁ Γ(S, S₀) I) ≫ y)
    (h₂ : testHom hS₀ (pr₂ Γ(S, S₀) I) ≫ x = testHom hS₀ (pr₂ Γ(S, S₀) I) ≫ y) : x = y := by
  obtain ⟨ψ, rfl⟩ := exists_pt_triples hS₀ hI W hW x hx
  obtain ⟨ψ', rfl⟩ := exists_pt_triples hS₀ hI W hW y hy
  simp only [Chart.testHom_comp_pt] at hx hy h₁ h₂
  have e₁ := W.pt_injective hS₀ h₁
  have e₂ := W.pt_injective hS₀ h₂
  congr 1
  refine triples_hom_ext (W.pt_injective hS₀ (hx.trans hy.symm)) ?_ ?_
  · exact AlgHom.ext fun a => congrArg (fun f : W.Ring →ₐ[Γ(S, S₀)] pairs Γ(S, S₀) I =>
      (f a : D × D).2) e₁
  · exact AlgHom.ext fun a => congrArg (fun f : W.Ring →ₐ[Γ(S, S₀)] pairs Γ(S, S₀) I =>
      (f a : D × D).2) e₂

include hW in
/-- The sum map on triples computes the product of the two projections. -/
lemma sum_comp_eq_mul {Q Q' : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M}
    (hQ : testHom hS₀ (fst Γ(S, S₀) I) ≫ Q = 1) (hQ' : testHom hS₀ (fst Γ(S, S₀) I) ≫ Q' = 1)
    {x : testObj hS₀ (triples Γ(S, S₀) I) ⟶ M} (hx : testHom hS₀ (t₁ Γ(S, S₀) I) ≫ x = 1)
    (hx₁ : testHom hS₀ (pr₁ Γ(S, S₀) I) ≫ x = Q) (hx₂ : testHom hS₀ (pr₂ Γ(S, S₀) I) ≫ x = Q') :
    testHom hS₀ (sum Γ(S, S₀) I hI) ≫ x = Q * Q' := by
  have hy : x = testHom hS₀ (pair (AlgHom.id Γ(S, S₀) (pairs Γ(S, S₀) I))
      ((diag Γ(S, S₀) I).comp (fst Γ(S, S₀) I)) fst_comp_id_eq) ≫ Q *
      testHom hS₀ (pair ((diag Γ(S, S₀) I).comp (fst Γ(S, S₀) I))
      (AlgHom.id Γ(S, S₀) (pairs Γ(S, S₀) I)) fst_comp_id_eq.symm) ≫ Q' := by
    have hd : ∀ {Q'' : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M},
        testHom hS₀ (fst Γ(S, S₀) I) ≫ Q'' = 1 →
          testHom hS₀ ((diag Γ(S, S₀) I).comp (fst Γ(S, S₀) I)) ≫ Q'' = 1 := by
      intro Q'' h
      rw [testHom_comp, Category.assoc, h, MonObj.comp_one]
    refine triples_point_ext hS₀ hI W hW hx ?_ ?_ ?_
    · rw [MonObj.comp_mul, testHom_comp_assoc, testHom_comp_assoc, t₁_comp_pair, t₁_comp_pair,
        AlgHom.comp_id, fst_comp_diag_comp_fst, hQ, hQ', mul_one]
    · rw [MonObj.comp_mul, testHom_comp_assoc, testHom_comp_assoc, pr₁_comp_pair, pr₁_comp_pair,
        testHom_id, Category.id_comp, hd hQ', mul_one, hx₁]
    · rw [MonObj.comp_mul, testHom_comp_assoc, testHom_comp_assoc, pr₂_comp_pair, pr₂_comp_pair,
        testHom_id, Category.id_comp, hd hQ, one_mul, hx₂]
  rw [hy, MonObj.comp_mul, testHom_comp_assoc, testHom_comp_assoc, sum_comp_pair_id_diag,
    sum_comp_pair_diag_id, testHom_id, Category.id_comp, Category.id_comp]

include hW in
/-- Scaling by a sum acts as the product of the scalings on points trivial on the first entry. -/
lemma scale_add_comp {p : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M}
    (hp : testHom hS₀ (fst Γ(S, S₀) I) ≫ p = 1) (c c' : D) :
    testHom hS₀ (scale Γ(S, S₀) I hI (c + c')) ≫ p =
      (testHom hS₀ (scale Γ(S, S₀) I hI c) ≫ p) * (testHom hS₀ (scale Γ(S, S₀) I hI c') ≫ p) := by
  have hs : ∀ c'' : D, testHom hS₀ (fst Γ(S, S₀) I) ≫ testHom hS₀ (scale Γ(S, S₀) I hI c'') ≫ p
      = 1 := by
    intro c''
    rw [testHom_comp_assoc, fst_comp_scale, hp]
  rw [← sum_comp_pair_scale hI c c', ← testHom_comp_assoc]
  refine sum_comp_eq_mul hS₀ hI W hW (hs c) (hs c') ?_ ?_ ?_
  · rw [testHom_comp_assoc, t₁_comp_pair, fst_comp_scale, hp]
  · rw [testHom_comp_assoc, pr₁_comp_pair]
  · rw [testHom_comp_assoc, pr₂_comp_pair]

include hW in
/-- Scaling by a natural number acts as a power on points trivial on the first entry. -/
lemma scale_natCast_comp {p : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M}
    (hp : testHom hS₀ (fst Γ(S, S₀) I) ≫ p = 1) (m : ℕ) :
    testHom hS₀ (scale Γ(S, S₀) I hI (m : D)) ≫ p = p ^ m := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, scale_zero, testHom_comp, Category.assoc, hp, MonObj.comp_one, pow_zero]
  | succ m ih =>
    rw [Nat.cast_succ, scale_add_comp hS₀ hI W hW hp, ih, scale_one, testHom_id,
      Category.id_comp, pow_succ]

include hI hW in
/-- A point of the infinitesimal kernel is the second entry of a point over pairs. -/
lemma exists_pairs_point (k : testObj hS₀ D ⟶ M)
    (hk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ k = 1) :
    ∃ p : testObj hS₀ (pairs Γ(S, S₀) I) ⟶ M,
      testHom hS₀ (fst Γ(S, S₀) I) ≫ p = 1 ∧ testHom hS₀ (snd Γ(S, S₀) I) ≫ p = k := by
  have hmk := Ideal.Quotient.mkₐ_surjective Γ(S, S₀) I
  obtain ⟨ψ, rfl⟩ := exists_pt_of_comp_eq_one hS₀ W hW _ hmk (isNilpotent_ker_mk hI) k hk
  obtain ⟨ε, hε⟩ := exists_pt_of_comp_eq_one hS₀ W hW _ hmk (isNilpotent_ker_mk hI)
    (1 : testObj hS₀ D ⟶ M) (MonObj.comp_one _)
  have h : (Ideal.Quotient.mkₐ Γ(S, S₀) I).comp ψ = (Ideal.Quotient.mkₐ Γ(S, S₀) I).comp ε := by
    apply W.pt_injective hS₀
    rw [← W.testHom_comp_pt, ← W.testHom_comp_pt, hk, hε, MonObj.comp_one]
  refine ⟨W.pt hS₀ (pairsLift ε ψ fun a => Ideal.Quotient.eq.mp (AlgHom.congr_fun h a)), ?_, ?_⟩
  · rw [W.testHom_comp_pt, fst_comp_pairsLift, hε]
  · rw [W.testHom_comp_pt, snd_comp_pairsLift]

include hI hW in
/-- Every point of the infinitesimal kernel has an `n`-th root in the kernel. -/
theorem exists_pow_eq (n : ℕ) (hn : IsUnit (n : D)) (k : testObj hS₀ D ⟶ M)
    (hk : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ k = 1) :
    ∃ r : testObj hS₀ D ⟶ M,
      testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ r = 1 ∧ r ^ n = k := by
  obtain ⟨u, hu⟩ := hn.exists_right_inv
  obtain ⟨p, hp, rfl⟩ := exists_pairs_point hS₀ hI W hW k hk
  have hp' : testHom hS₀ (fst Γ(S, S₀) I) ≫ testHom hS₀ (scale Γ(S, S₀) I hI u) ≫ p = 1 := by
    rw [testHom_comp_assoc, fst_comp_scale, hp]
  refine ⟨testHom hS₀ (snd Γ(S, S₀) I) ≫ testHom hS₀ (scale Γ(S, S₀) I hI u) ≫ p, ?_, ?_⟩
  · rw [testHom_comp_assoc, mk_comp_snd, testHom_comp, Category.assoc, hp', MonObj.comp_one]
  · rw [← MonObj.comp_pow, ← scale_natCast_comp hS₀ hI W hW hp',
      testHom_comp_assoc hS₀ (scale Γ(S, S₀) I hI u) (scale Γ(S, S₀) I hI (n : D)),
      scale_comp_scale, hu, scale_one, testHom_id, Category.id_comp]

include hI hW in
/-- The infinitesimal kernel has no nontrivial `n`-torsion. -/
theorem eq_one_of_pow_eq_one (n : ℕ) (hn : IsUnit (n : D)) (r : testObj hS₀ D ⟶ M)
    (hr : testHom hS₀ (Ideal.Quotient.mkₐ Γ(S, S₀) I) ≫ r = 1) (hrn : r ^ n = 1) : r = 1 := by
  obtain ⟨u, hu⟩ := hn.exists_left_inv
  obtain ⟨p, hp, rfl⟩ := exists_pairs_point hS₀ hI W hW r hr
  have hpn : p ^ n = 1 := pairs_point_ext hS₀ hI W hW
    (by rw [MonObj.comp_pow, hp, one_pow]) (MonObj.comp_one _)
    (by rw [MonObj.comp_pow, hrn, MonObj.comp_one])
  have h1 : p = 1 :=
    calc p = testHom hS₀ (scale Γ(S, S₀) I hI (u * n)) ≫ p := by
          rw [hu, scale_one, testHom_id, Category.id_comp]
      _ = 1 := by
          rw [← scale_comp_scale, ← testHom_comp_assoc, scale_natCast_comp hS₀ hI W hW hp, hpn,
            MonObj.comp_one]
  rw [h1, MonObj.comp_one]

end InfinitesimalKernel

end Langlands.AlgebraicGeometry
