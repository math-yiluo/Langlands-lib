import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationLength
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Adjoin.Basic

/-! # Cotangent modules of augmented algebras and of dilatations -/

noncomputable section

open Module Submodule

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type*} [CommRing R]

section Augmented

variable {C : Type*} [CommRing C] [Algebra R C] (ε : C →ₐ[R] R)

/-- The augmentation ideal of an `R`-algebra with an `R`-point. -/
abbrev augIdeal : Ideal C := RingHom.ker ε

/-- The cotangent module `I / I ^ 2` at an `R`-point. -/
abbrev Cot : Type _ := (augIdeal ε).Cotangent

theorem sub_algebraMap_mem (y : C) : y - algebraMap R C (ε y) ∈ augIdeal ε := by
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_self]

/-- The differential at the point `ε`: `y ↦ [y - ε y]`. -/
def dif : C →ₗ[R] Cot ε where
  toFun y := (augIdeal ε).toCotangent ⟨y - algebraMap R C (ε y), sub_algebraMap_mem ε y⟩
  map_add' y y' := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' r y := by
    have : (⟨r • y - algebraMap R C (ε (r • y)), sub_algebraMap_mem ε _⟩ : augIdeal ε) =
        r • ⟨y - algebraMap R C (ε y), sub_algebraMap_mem ε y⟩ := by
      ext
      simp only [map_mul, Submodule.coe_smul_of_tower, Algebra.smul_def,
        mul_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    rw [RingHom.id_apply, this, LinearMap.map_smul_of_tower]

theorem dif_apply (y : C) :
    dif ε y = (augIdeal ε).toCotangent ⟨y - algebraMap R C (ε y), sub_algebraMap_mem ε y⟩ := rfl

theorem dif_of_mem {y : C} (hy : y ∈ augIdeal ε) :
    dif ε y = (augIdeal ε).toCotangent ⟨y, hy⟩ := by
  rw [dif_apply]
  congr 2
  rw [RingHom.mem_ker.mp hy, map_zero, sub_zero]

theorem dif_algebraMap (r : R) : dif ε (algebraMap R C r) = 0 := by
  rw [dif_apply, Ideal.toCotangent_eq_zero]
  simp

theorem dif_one : dif ε 1 = 0 := by
  simpa using dif_algebraMap ε 1

/-- The differential is a derivation at the point `ε`. -/
theorem dif_mul (y y' : C) : dif ε (y * y') = ε y • dif ε y' + ε y' • dif ε y := by
  have key : y * y' - algebraMap R C (ε (y * y')) =
      (y - algebraMap R C (ε y)) * (y' - algebraMap R C (ε y')) +
        (ε y • (y' - algebraMap R C (ε y')) + ε y' • (y - algebraMap R C (ε y))) := by
    simp only [map_mul, Algebra.smul_def]
    ring
  set a : augIdeal ε := ⟨y - algebraMap R C (ε y), sub_algebraMap_mem ε y⟩
  set b : augIdeal ε := ⟨y' - algebraMap R C (ε y'), sub_algebraMap_mem ε y'⟩
  set p : augIdeal ε := ⟨y * y' - algebraMap R C (ε (y * y')), sub_algebraMap_mem ε _⟩
  rw [dif_apply, dif_apply, dif_apply]
  change (augIdeal ε).toCotangent p = ε y • (augIdeal ε).toCotangent b +
    ε y' • (augIdeal ε).toCotangent a
  rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add, ← sub_eq_zero,
    ← map_sub, Ideal.toCotangent_eq_zero]
  have : ((p - (ε y • b + ε y' • a) : augIdeal ε) : C) = (a : C) * b := by
    simp only [p, a, b, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul_of_tower, key]
    ring
  rw [this, pow_two]
  exact Ideal.mul_mem_mul a.2 b.2

theorem dif_surjective : Function.Surjective (dif ε) := by
  intro t
  obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
  exact ⟨y, dif_of_mem ε hy⟩

theorem dif_eq_zero_of_mem_sq {y : C} (hy : y ∈ augIdeal ε ^ 2) : dif ε y = 0 := by
  have hy1 : y ∈ augIdeal ε := Ideal.pow_le_self two_ne_zero hy
  rw [dif_of_mem ε hy1, Ideal.toCotangent_eq_zero]
  exact hy

/-- Functoriality of the cotangent module along a map of pointed algebras. -/
def cotMap {C' : Type*} [CommRing C'] [Algebra R C'] {ε' : C' →ₐ[R] R} (φ : C →ₐ[R] C')
    (hφ : ε'.comp φ = ε) : Cot ε →ₗ[R] Cot ε' :=
  Ideal.mapCotangent (augIdeal ε) (augIdeal ε') φ (by
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, hφ]
    exact hy)

theorem cotMap_dif {C' : Type*} [CommRing C'] [Algebra R C'] {ε' : C' →ₐ[R] R}
    (φ : C →ₐ[R] C') (hφ : ε'.comp φ = ε) (y : C) :
    cotMap ε φ hφ (dif ε y) = dif ε' (φ y) := by
  rw [dif_apply, cotMap, Ideal.mapCotangent_toCotangent, dif_apply]
  congr 2
  rw [map_sub, AlgHom.commutes, ← AlgHom.comp_apply, hφ]

end Augmented

section Dilatation

variable {B : Type*} [CommRing B] [Algebra R B] (εB : B →ₐ[R] R)

/-- The point of a subalgebra induced by an ambient point. -/
abbrev subPoint (C : Subalgebra R B) : C →ₐ[R] R := εB.comp C.val

variable {εB}

theorem subPoint_comp_inclusion {C C' : Subalgebra R B} (h : C ≤ C') :
    (subPoint εB C').comp (Subalgebra.inclusion h) = subPoint εB C :=
  AlgHom.ext fun _ => rfl

variable {ϖ : R} {C : Subalgebra R B} (J : Ideal C)

/-- The quotients `j / ϖ` of elements of `J`. -/
def divSet (ϖ : R) (J : Ideal C) : Set B := {x | ∃ j ∈ J, ϖ • x = (j : B)}

/-- The dilatation `C[J/ϖ]` inside `B`. -/
def dilat (ϖ : R) (J : Ideal C) : Subalgebra R B :=
  Algebra.adjoin R ((C : Set B) ∪ divSet ϖ J)

theorem le_dilat : C ≤ dilat ϖ J := fun _ hx => Algebra.subset_adjoin (Or.inl hx)

theorem divSet_subset_dilat : divSet ϖ J ⊆ dilat ϖ J := fun _ hx =>
  Algebra.subset_adjoin (Or.inr hx)

theorem exists_pow_smul_mem {y : B} (hy : y ∈ dilat ϖ J) : ∃ m : ℕ, ϖ ^ m • y ∈ C := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨j, -, hj⟩
    · exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
    · exact ⟨1, by rw [pow_one, hj]; exact j.2⟩
  | algebraMap r => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have : ϖ ^ (m + n) • (x + y) = ϖ ^ n • (ϖ ^ m • x) + ϖ ^ m • (ϖ ^ n • y) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [this]
    exact C.add_mem (C.smul_mem hm _) (C.smul_mem hn _)
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [pow_add, ← smul_mul_smul_comm]
    exact C.mul_mem hm hn

/-- An element of the square of the augmentation ideal of the dilatation becomes, after
multiplication by a power of `ϖ`, an element of the square of the augmentation ideal of `C`. -/
theorem exists_mem_sq_of_mem_sq {y : dilat ϖ J}
    (hy : y ∈ augIdeal (subPoint εB (dilat ϖ J)) ^ 2) :
    ∃ m : ℕ, ∃ w ∈ augIdeal (subPoint εB C) ^ 2, (w : B) = ϖ ^ m • (y : B) := by
  rw [pow_two] at hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro a ha b hb
    obtain ⟨m, hm⟩ := exists_pow_smul_mem J a.2
    obtain ⟨n, hn⟩ := exists_pow_smul_mem J b.2
    have ha' : (⟨_, hm⟩ : C) ∈ augIdeal (subPoint εB C) := by
      rw [RingHom.mem_ker] at ha ⊢
      change εB (ϖ ^ m • (a : B)) = 0
      rw [map_smul]
      change ϖ ^ m • subPoint εB (dilat ϖ J) a = 0
      rw [ha, smul_zero]
    have hb' : (⟨_, hn⟩ : C) ∈ augIdeal (subPoint εB C) := by
      rw [RingHom.mem_ker] at hb ⊢
      change εB (ϖ ^ n • (b : B)) = 0
      rw [map_smul]
      change ϖ ^ n • subPoint εB (dilat ϖ J) b = 0
      rw [hb, smul_zero]
    refine ⟨m + n, _, by rw [pow_two]; exact Ideal.mul_mem_mul ha' hb', ?_⟩
    simp only [Subalgebra.coe_mul]
    rw [pow_add, ← smul_mul_smul_comm]
  · intro a b ha hb
    obtain ⟨m, w₁, hw₁, h₁⟩ := ha
    obtain ⟨n, w₂, hw₂, h₂⟩ := hb
    refine ⟨m + n, ϖ ^ n • w₁ + ϖ ^ m • w₂,
      Ideal.add_mem _ (Submodule.smul_of_tower_mem _ _ hw₁)
        (Submodule.smul_of_tower_mem _ _ hw₂), ?_⟩
    simp only [Subalgebra.coe_add, Subalgebra.coe_smul, h₁, h₂, smul_smul, smul_add, ← pow_add,
      add_comm n m]

section DilatCot

variable [IsDomain R] [Module.IsTorsionFree R B] {c : ℕ}

/-- The data of elements `z k ∈ J` of the augmentation ideal with chosen quotients
`ζ k = z k / ϖ` in the ambient algebra. -/
structure DivData (εB : B →ₐ[R] R) (ϖ : R) (J : Ideal C) (z : Fin c → C) (ζ : Fin c → B) :
    Prop where
  ne_zero : ϖ ≠ 0
  mem_J : ∀ k, z k ∈ J
  mem_aug : ∀ k, z k ∈ augIdeal (subPoint εB C)
  smul_ζ : ∀ k, ϖ • ζ k = (z k : B)

variable {J} {z : Fin c → C} {ζ : Fin c → B} (hd : DivData εB ϖ J z ζ)
include hd

/-- The quotients `z k / ϖ` as elements of the dilatation. -/
def DivData.ζD (k : Fin c) : dilat ϖ J :=
  ⟨ζ k, divSet_subset_dilat J ⟨z k, hd.mem_J k, hd.smul_ζ k⟩⟩

omit [Module.IsTorsionFree R B] in
theorem DivData.εB_ζ (k : Fin c) : εB (ζ k) = 0 := by
  have h : ϖ • εB (ζ k) = 0 := by
    rw [← map_smul, hd.smul_ζ k]
    exact hd.mem_aug k
  rcases smul_eq_zero.mp h with h | h
  · exact absurd h hd.ne_zero
  · exact h

omit [IsDomain R] [Module.IsTorsionFree R B] in
theorem DivData.inclusion_z (k : Fin c) :
    Subalgebra.inclusion (le_dilat J) (z k) = ϖ • hd.ζD k :=
  Subtype.ext (hd.smul_ζ k).symm

/-- The comparison map from the pushout to the cotangent module of the dilatation. -/
def DivData.toCot :
    Pushout ϖ (fun k => dif (subPoint εB C) (z k)) →ₗ[R] Cot (subPoint εB (dilat ϖ J)) :=
  (pushoutRel ϖ (fun k => dif (subPoint εB C) (z k))).liftQ
    (LinearMap.coprod
      (cotMap (subPoint εB C) (Subalgebra.inclusion (le_dilat J)) (subPoint_comp_inclusion _))
      (Fintype.linearCombination R (fun k => dif (subPoint εB (dilat ϖ J)) (hd.ζD k))))
    (by
      classical
      rw [pushoutRel, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hs : -(ϖ • Pi.single k (1 : R)) = Pi.single k (-ϖ) := by
        ext l
        simp only [Pi.neg_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        split_ifs <;> simp
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coprod_apply]
      dsimp only
      rw [cotMap_dif, hd.inclusion_z, map_smul, hs, Fintype.linearCombination_apply_single,
        neg_smul, add_neg_cancel])

omit [Module.IsTorsionFree R B] in
theorem DivData.toCot_ι (t : Cot (subPoint εB C)) :
    hd.toCot ((pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))).ι t) =
      cotMap (subPoint εB C) (Subalgebra.inclusion (le_dilat J)) (subPoint_comp_inclusion _) t := by
  simp [DivData.toCot, pushout]

omit [Module.IsTorsionFree R B] in
theorem DivData.toCot_ζ (k : Fin c) :
    hd.toCot ((pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))).ζ k) =
      dif (subPoint εB (dilat ϖ J)) (hd.ζD k) := by
  classical
  simp [DivData.toCot, pushout, Fintype.linearCombination_apply_single]

/-- A relation `ϖ² g₀ + ϖ ∑ z_k g_k + ∑ z_k z_l g_{kl} = 0` in `C` gives an element of the kernel
of the comparison map. -/
theorem DivData.toCot_relation (g0 : C) (g1 : Fin c → C) (g2 : Fin c → Fin c → C)
    (hrel : ϖ ^ 2 • g0 + ϖ • ∑ k, z k * g1 k + ∑ k, ∑ l, z k * z l * g2 k l = 0) :
    hd.toCot ((pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))).ι
        (dif (subPoint εB C) g0) +
      ∑ k, subPoint εB C (g1 k) •
        (pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))).ζ k) = 0 := by
  set D := dilat ϖ J
  set ι := Subalgebra.inclusion (le_dilat J)
  have hz' : ∀ k, ((z k : C) : B) = ϖ • ζ k := fun k => (hd.smul_ζ k).symm
  -- the relation divided by `ϖ ^ 2`, as an identity in `D`
  have hY : ι g0 + ∑ k, hd.ζD k * ι (g1 k) + ∑ k, ∑ l, hd.ζD k * hd.ζD l * ι (g2 k l) = 0 := by
    have h2 : (ϖ ^ 2 : R) ≠ 0 := pow_ne_zero 2 hd.ne_zero
    have hB : C.val (ϖ ^ 2 • g0 + ϖ • ∑ k, z k * g1 k + ∑ k, ∑ l, z k * z l * g2 k l) = 0 := by
      rw [hrel, map_zero]
    have hz'' : ∀ k, C.val (z k) = ϖ • ζ k := fun k => (hd.smul_ζ k).symm
    simp only [map_add, map_smul, map_sum, map_mul, hz''] at hB
    apply Subtype.val_injective
    apply smul_right_injective B h2
    beta_reduce
    have hι : ∀ x, ((ι x : D) : B) = C.val x := fun x => rfl
    have hζv : ∀ k, ((hd.ζD k : D) : B) = ζ k := fun k => rfl
    simp only [Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
      Subalgebra.coe_zero, smul_zero, hι, hζv]
    rw [← hB]
    simp only [Algebra.smul_def, map_pow, mul_add, Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hζ0 : ∀ k, subPoint εB D (hd.ζD k) = 0 := fun k => hd.εB_ζ k
  have hdY := congrArg (dif (subPoint εB D)) hY
  simp only [map_zero, map_add, map_sum, dif_mul, hζ0, map_mul, mul_zero, zero_smul,
    smul_zero, add_zero, zero_add, Finset.sum_const_zero] at hdY
  rw [map_add, map_sum, DivData.toCot_ι, cotMap_dif]
  simp only [map_smul, DivData.toCot_ζ]
  exact hdY

omit [Module.IsTorsionFree R B] in
theorem ker_cotMap_le_torsion :
    LinearMap.ker (cotMap (subPoint εB C) (Subalgebra.inclusion (le_dilat (ϖ := ϖ) J))
      (subPoint_comp_inclusion _)) ≤ torsion R (Cot (subPoint εB C)) := by
  intro t ht
  obtain ⟨⟨i, hi⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
  rw [LinearMap.mem_ker, cotMap, Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at ht
  obtain ⟨m, w, hw, hwi⟩ := exists_mem_sq_of_mem_sq J ht
  have hϖm : ϖ ^ m ≠ 0 := pow_ne_zero m hd.ne_zero
  refine (mem_torsion_iff _).mpr ⟨⟨ϖ ^ m, mem_nonZeroDivisors_of_ne_zero hϖm⟩, ?_⟩
  rw [Submonoid.smul_def, ← LinearMap.map_smul_of_tower, Ideal.toCotangent_eq_zero]
  have : ((ϖ ^ m • (⟨i, hi⟩ : augIdeal (subPoint εB C)) : augIdeal (subPoint εB C)) : C) = w := by
    apply Subtype.ext
    rw [hwi]
    rfl
  rw [this]
  exact hw

omit [Module.IsTorsionFree R B] in
theorem DivData.ker_toCot_le_torsion :
    LinearMap.ker hd.toCot ≤ torsion R (Pushout ϖ (fun k => dif (subPoint εB C) (z k))) := by
  intro u hu
  set E := pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))
  obtain ⟨t, a, rfl⟩ := E.span u
  have h1 : hd.toCot (E.ι (ϖ • t + ∑ k, a k • dif (subPoint εB C) (z k))) = 0 := by
    rw [← E.smul_eq_ι, map_smul, LinearMap.mem_ker.mp hu, smul_zero]
  rw [DivData.toCot_ι] at h1
  obtain ⟨s, hs⟩ := (mem_torsion_iff _).mp (ker_cotMap_le_torsion hd h1)
  refine (mem_torsion_iff _).mpr ⟨s * ⟨ϖ, mem_nonZeroDivisors_of_ne_zero hd.ne_zero⟩, ?_⟩
  rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
  change (s : R) • ϖ • (E.ι t + ∑ k, a k • E.ζ k) = 0
  rw [E.smul_eq_ι, ← map_smul, ← Submonoid.smul_def, hs, map_zero]

/-- The comparison map is surjective when `J` is generated by `ϖ` and the `z k` after
multiplication by an element whose value at the point is a unit. -/
theorem DivData.toCot_surjective
    (hg : ∃ g : C, IsUnit (subPoint εB C g) ∧
      ∀ j ∈ J, ∃ (a : C) (b : Fin c → C), g * j = ϖ • a + ∑ k, z k * b k) :
    Function.Surjective hd.toCot := by
  obtain ⟨g, hgu, hg⟩ := hg
  set D := dilat ϖ J
  set ι := Subalgebra.inclusion (le_dilat (ϖ := ϖ) J)
  set E := pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))
  set Q := LinearMap.range hd.toCot
  have hε : ∀ c : C, subPoint εB D (ι c) = subPoint εB C c := fun _ => rfl
  have hζ0 : ∀ k, subPoint εB D (hd.ζD k) = 0 := fun k => hd.εB_ζ k
  have hC : ∀ c : C, dif (subPoint εB D) (ι c) ∈ Q := by
    intro c
    refine ⟨E.ι (dif (subPoint εB C) c), ?_⟩
    rw [DivData.toCot_ι, cotMap_dif]
  have hζ : ∀ k, dif (subPoint εB D) (hd.ζD k) ∈ Q := fun k => ⟨E.ζ k, hd.toCot_ζ k⟩
  let S : Subalgebra R B :=
    { carrier := {y | ∃ hy : y ∈ D, dif (subPoint εB D) ⟨y, hy⟩ ∈ Q}
      mul_mem' := by
        rintro a b ⟨ha, hqa⟩ ⟨hb, hqb⟩
        refine ⟨D.mul_mem ha hb, ?_⟩
        have : (⟨a * b, D.mul_mem ha hb⟩ : D) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [this, dif_mul]
        exact Q.add_mem (Q.smul_mem _ hqb) (Q.smul_mem _ hqa)
      add_mem' := by
        rintro a b ⟨ha, hqa⟩ ⟨hb, hqb⟩
        refine ⟨D.add_mem ha hb, ?_⟩
        have : (⟨a + b, D.add_mem ha hb⟩ : D) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add]
        exact Q.add_mem hqa hqb
      algebraMap_mem' := by
        intro r
        refine ⟨D.algebraMap_mem r, ?_⟩
        have : (⟨algebraMap R B r, D.algebraMap_mem r⟩ : D) = algebraMap R D r := rfl
        rw [this, dif_algebraMap]
        exact Q.zero_mem }
  have hDS : D ≤ S := by
    apply Algebra.adjoin_le
    rintro x (hx | ⟨j, hj, hjx⟩)
    · exact ⟨le_dilat J hx, hC ⟨x, hx⟩⟩
    · have hxD : x ∈ D := divSet_subset_dilat J ⟨j, hj, hjx⟩
      refine ⟨hxD, ?_⟩
      obtain ⟨a, b, hab⟩ := hg j hj
      have hgx : ι g * ⟨x, hxD⟩ = ι a + ∑ k, hd.ζD k * ι (b k) := by
        apply Subtype.val_injective
        apply smul_right_injective B hd.ne_zero
        beta_reduce
        have hB := congrArg (fun y : C => (y : B)) hab
        simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_smul,
          AddSubmonoidClass.coe_finsetSum] at hB
        have hι : ∀ c : C, ((ι c : D) : B) = (c : B) := fun _ => rfl
        have hζv : ∀ k, ((hd.ζD k : D) : B) = ζ k := fun _ => rfl
        simp only [Subalgebra.coe_mul, Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum, hι,
          hζv, smul_add, Finset.smul_sum]
        rw [← mul_smul_comm, hjx, hB]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hd.smul_ζ k, smul_mul_assoc]
      have hd' := congrArg (dif (subPoint εB D)) hgx
      simp only [dif_mul, map_add, map_sum, hζ0, zero_smul, zero_add, hε] at hd'
      have hmem : subPoint εB C g • dif (subPoint εB D) ⟨x, hxD⟩ ∈ Q := by
        have : subPoint εB C g • dif (subPoint εB D) ⟨x, hxD⟩ =
            dif (subPoint εB D) (ι a) + ∑ k, subPoint εB C (b k) • dif (subPoint εB D) (hd.ζD k) -
              subPoint εB D ⟨x, hxD⟩ • dif (subPoint εB D) (ι g) := by
          rw [← hd']
          abel
        rw [this]
        exact Q.sub_mem (Q.add_mem (hC a) (Q.sum_mem fun k _ => Q.smul_mem _ (hζ k)))
          (Q.smul_mem _ (hC g))
      have : dif (subPoint εB D) ⟨x, hxD⟩ =
          ((hgu.unit⁻¹ : Rˣ) : R) • (subPoint εB C g • dif (subPoint εB D) ⟨x, hxD⟩) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
      rw [this]
      exact Q.smul_mem _ hmem
  intro t
  obtain ⟨y, rfl⟩ := dif_surjective _ t
  obtain ⟨_, hq⟩ := hDS y.2
  exact hq

/-- **Defect drop for a dilatation.** If `J` is generated by `ϖ` and the `z k` after multiplication
by an element with unit value, the classes of the `z k` are independent modulo `ϖ`, and every
`ϖ`-torsion class of the cotangent module comes from a relation
`ϖ² g₀ + ϖ ∑ z_k g_k + ∑ z_k z_l g_{kl} = 0`, then the defect of the dilatation plus the length of
the `ϖ`-torsion is at most the defect of `C`. -/
theorem DivData.defect_add_le
    (hg : ∃ g : C, IsUnit (subPoint εB C g) ∧
      ∀ j ∈ J, ∃ (a : C) (b : Fin c → C), g * j = ϖ • a + ∑ k, z k * b k)
    (hz : IndepModulo ϖ (fun k => dif (subPoint εB C) (z k)))
    (hrel : ∀ τ ∈ torsionBy R (Cot (subPoint εB C)) ϖ,
      ∃ (g0 : C) (g1 : Fin c → C) (g2 : Fin c → Fin c → C),
        ϖ ^ 2 • g0 + ϖ • ∑ k, z k * g1 k + ∑ k, ∑ l, z k * z l * g2 k l = 0 ∧
        ϖ • dif (subPoint εB C) g0 + ∑ k, subPoint εB C (g1 k) • dif (subPoint εB C) (z k) = τ) :
    defect R (Cot (subPoint εB (dilat ϖ J))) + torsionByLength R (Cot (subPoint εB C)) ϖ ≤
      defect R (Cot (subPoint εB C)) := by
  set E := pushout hd.ne_zero (fun k => dif (subPoint εB C) (z k))
  refine E.defect_add_le hd.ne_zero hz hd.toCot (hd.toCot_surjective hg)
    hd.ker_toCot_le_torsion (fun τ hτ => ?_)
  obtain ⟨g0, g1, g2, hr, hτ⟩ := hrel τ hτ
  refine ⟨_, hd.toCot_relation g0 g1 g2 hr, ?_⟩
  rw [E.smul_eq_ι, hτ]

end DilatCot

end Dilatation

section Relation

variable [IsDomain R] {C : Type*} [CommRing C] [Algebra R C] (ε : C →ₐ[R] R)
  {ϖ : R} {J : Ideal C} {c : ℕ} {z : Fin c → C}

omit [IsDomain R] in
/-- Rescaling a relation and its value by a scalar. -/
theorem relation_smul (r : R) {g0 : C} {g1 : Fin c → C} {g2 : Fin c → Fin c → C} {τ : Cot ε}
    (hrel : ϖ ^ 2 • g0 + ϖ • ∑ k, z k * g1 k + ∑ k, ∑ l, z k * z l * g2 k l = 0)
    (hval : ϖ • dif ε g0 + ∑ k, ε (g1 k) • dif ε (z k) = τ) :
    ϖ ^ 2 • (r • g0) + ϖ • ∑ k, z k * (r • g1 k) + ∑ k, ∑ l, z k * z l * (r • g2 k l) = 0 ∧
      ϖ • dif ε (r • g0) + ∑ k, ε (r • g1 k) • dif ε (z k) = r • τ := by
  constructor
  · have h := congrArg (fun y => r • y) hrel
    simp only [smul_zero, smul_add] at h
    rw [← h]
    congr 1
    · congr 1
      · rw [smul_comm]
      · rw [smul_comm r ϖ]
        congr 1
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [mul_smul_comm]
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_smul_comm]
  · rw [← hval, smul_add, Finset.smul_sum, map_smul, smul_comm r ϖ]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_smul]

/-- **Torsion classes come from quadratic relations.** Suppose `ϖ C ⊆ J`, that `J` is generated
by `ϖ` and the `z k` after multiplication by an element with unit value (`hA`), that relations
`ϖ b₀ + ∑ z_k b_k = 0` have coefficients in `J` up to such a multiplier (`hQ1`), and that elements
of `I² ∩ J` lie in `ϖ I² + ∑ z_k I` up to such a multiplier (`hQ2`). Then every `ϖ`-torsion class
of `I / I²` is the value of a relation `ϖ² g₀ + ϖ ∑ z_k g_k + ∑ z_k z_l g_{kl} = 0`. -/
theorem exists_relation (hϖ : ϖ ≠ 0) (hϖJ : ∀ y : C, ϖ • y ∈ J) (hz : ∀ k, z k ∈ augIdeal ε)
    (hA : ∃ g : C, IsUnit (ε g) ∧
      ∀ j ∈ J, ∃ (a : C) (b : Fin c → C), g * j = ϖ • a + ∑ k, z k * b k)
    (hQ1 : ∀ (b0 : C) (b : Fin c → C), ϖ • b0 + ∑ k, z k * b k = 0 →
      ∃ h : C, IsUnit (ε h) ∧ h * b0 ∈ J ∧ ∀ k, h * b k ∈ J)
    (hQ2 : ∀ q ∈ augIdeal ε ^ 2, q ∈ J → ∃ h : C, IsUnit (ε h) ∧
      ∃ a ∈ augIdeal ε ^ 2, ∃ b : Fin c → C, (∀ k, b k ∈ augIdeal ε) ∧
        h * q = ϖ • a + ∑ k, z k * b k)
    (τ : Cot ε) (hτ : τ ∈ torsionBy R (Cot ε) ϖ) :
    ∃ (g0 : C) (g1 : Fin c → C) (g2 : Fin c → Fin c → C),
      ϖ ^ 2 • g0 + ϖ • ∑ k, z k * g1 k + ∑ k, ∑ l, z k * z l * g2 k l = 0 ∧
      ϖ • dif ε g0 + ∑ k, ε (g1 k) • dif ε (z k) = τ := by
  obtain ⟨g, hgu, hgJ⟩ := hA
  obtain ⟨⟨i, hi⟩, rfl⟩ := Ideal.toCotangent_surjective _ τ
  have hεi : ε i = 0 := hi
  have hτ' : ϖ • i ∈ augIdeal ε ^ 2 := by
    rw [mem_torsionBy_iff, ← LinearMap.map_smul_of_tower, Ideal.toCotangent_eq_zero] at hτ
    exact hτ
  obtain ⟨h₁, hu₁, a', ha', a'', ha'', hq⟩ := hQ2 _ hτ' (hϖJ i)
  have ha'1 : a' ∈ augIdeal ε := Ideal.pow_le_self two_ne_zero ha'
  have hεa' : ε a' = 0 := ha'1
  have hεz : ∀ k, ε (z k) = 0 := hz
  have hrel1 : ϖ • (h₁ * i - a') + ∑ k, z k * (-a'' k) = 0 := by
    have : h₁ * (ϖ • i) = ϖ • (h₁ * i) := mul_smul_comm ϖ h₁ i
    rw [smul_sub, ← this, hq]
    simp only [mul_neg, Finset.sum_neg_distrib]
    abel
  obtain ⟨h₂, hu₂, hJ0, hJk⟩ := hQ1 _ _ hrel1
  obtain ⟨e0, e0', he0⟩ := hgJ _ hJ0
  choose e e' he using fun k => hgJ _ (hJk k)
  have hεe : ∀ k, ε (e k) = 0 := by
    intro k
    have hεa'' : ε (a'' k) = 0 := ha'' k
    have := congrArg ε (he k)
    simp only [map_mul, map_neg, hεa'', neg_zero, mul_zero, map_add, map_smul, map_sum, hεz,
      zero_mul, Finset.sum_const_zero, add_zero, smul_eq_mul] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hϖ
    · exact h
  -- the relation multiplied by `g * h₂`
  have hrel2 : ϖ ^ 2 • e0 + ϖ • ∑ k, z k * (e0' k + e k) + ∑ k, ∑ l, z k * z l * e' k l = 0 := by
    have h0 := congrArg (fun y => g * (h₂ * y)) hrel1
    simp only [mul_zero] at h0
    rw [← h0]
    have hsum : g * (h₂ * ∑ k, z k * -a'' k) = ∑ k, z k * (g * (h₂ * -a'' k)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [mul_add, mul_add, hsum, mul_smul_comm, mul_smul_comm, he0]
    simp only [he, mul_add, Finset.sum_add_distrib, smul_add, Finset.smul_sum, mul_smul_comm,
      Finset.mul_sum, pow_two, mul_smul, mul_assoc]
    abel
  set u := ε g * ε h₂ * ε h₁ with hu_def
  have hu : IsUnit u := (hgu.mul hu₂).mul hu₁
  have hval : ϖ • dif ε e0 + ∑ k, ε (e0' k + e k) • dif ε (z k) =
      u • (augIdeal ε).toCotangent ⟨i, hi⟩ := by
    have hd := congrArg (dif ε) he0
    simp only [dif_mul, map_mul, map_sub, map_add, map_smul, map_sum, hεi, hεa', hεz,
      dif_eq_zero_of_mem_sq ε ha', mul_zero, sub_zero, zero_smul, add_zero, sub_self,
      zero_add] at hd
    simp only [map_add, hεe, add_zero]
    rw [← dif_of_mem ε hi, hu_def, mul_smul, mul_smul]
    exact hd.symm
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨hr, hvl⟩ := relation_smul ε v hrel2 hval
  refine ⟨v • e0, fun k => v • (e0' k + e k), fun k l => v • e' k l, hr, ?_⟩
  rw [hvl, smul_smul, hv, one_smul]

end Relation

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
