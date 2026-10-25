import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.Int
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Data.ZMod.QuotientGroup

/-! # The index of `p`-th powers in S-unit groups

For a finitely generated abelian group `A` and `n ≠ 0`, `[A : nA] = n ^ rank A · |A[n]|`.
For a number field `K` and a finite set `S` of finite places, the group of `S`-units has rank
`|S| + r₁ + r₂ - 1` (the `S`-unit theorem, derived from Dirichlet's unit theorem and the
finiteness of the class group), so `[U_S : U_S^p] = p ^ (|S| + r₁ + r₂)` when `K` contains a
primitive `p`-th root of unity.
-/

namespace Langlands.Global.Arithmetic.SUnitIndex

section PowerIndex

variable {A : Type*} [AddCommGroup A]

/-- On a finite group, the image of multiplication by `n` has index equal to the order of its
kernel. -/
theorem index_nsmul_range_of_finite [Finite A] (n : ℕ) :
    (nsmulAddMonoidHom n : A →+ A).range.index = Nat.card (nsmulAddMonoidHom n : A →+ A).ker := by
  set f := (nsmulAddMonoidHom n : A →+ A)
  have h1 := f.range.card_mul_index
  have h2 := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have : Nat.card f.range * f.range.index = Nat.card f.range * Nat.card f.ker := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem nsmul_range_prod {B C : Type*} [AddCommGroup B] [AddCommGroup C] (n : ℕ) :
    (nsmulAddMonoidHom n : B × C →+ B × C).range =
      (nsmulAddMonoidHom n : B →+ B).range.prod (nsmulAddMonoidHom n : C →+ C).range := by
  ext ⟨b, c⟩
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_prod, Prod.exists,
    Prod.smul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    exact ⟨x, y, rfl, rfl⟩

theorem natCard_nsmul_ker_prod {B C : Type*} [AddCommGroup B] [AddCommGroup C] (n : ℕ) :
    Nat.card (nsmulAddMonoidHom n : B × C →+ B × C).ker =
      Nat.card (nsmulAddMonoidHom n : B →+ B).ker * Nat.card (nsmulAddMonoidHom n : C →+ C).ker := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun x => (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · have := x.2; simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this ⊢
    exact congrArg Prod.fst this
  · have := x.2; simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this ⊢
    exact congrArg Prod.snd this
  · have h1 := y.1.2; have h2 := y.2.2
    simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at h1 h2 ⊢
    exact Prod.ext h1 h2

theorem nsmul_range_map_equiv {B : Type*} [AddCommGroup B] (e : A ≃+ B) (n : ℕ) :
    (nsmulAddMonoidHom n : A →+ A).range.map (e : A →+ B) = (nsmulAddMonoidHom n : B →+ B).range := by
  ext b
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨n • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩

theorem natCard_nsmul_ker_congr {B : Type*} [AddCommGroup B] (e : A ≃+ B) (n : ℕ) :
    Nat.card (nsmulAddMonoidHom n : A →+ A).ker = Nat.card (nsmulAddMonoidHom n : B →+ B).ker := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e x, ?_⟩
      invFun := fun y => ⟨e.symm y, ?_⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  · have := x.2; simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this ⊢
    rw [← map_nsmul, this, map_zero]
  · have := y.2; simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at this ⊢
    rw [← map_nsmul, this, map_zero]

/-- On `Fin r → ℤ` multiplication by `n > 0` has image of index `n ^ r`. -/
theorem index_nsmul_range_pi (r n : ℕ) :
    (nsmulAddMonoidHom n : (Fin r → ℤ) →+ (Fin r → ℤ)).range.index = n ^ r := by
  have : (nsmulAddMonoidHom n : (Fin r → ℤ) →+ (Fin r → ℤ)).range =
      AddSubgroup.pi Set.univ (fun _ => AddSubgroup.zmultiples (n : ℤ)) := by
    ext x
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_pi,
      Set.mem_univ, true_implies, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by simp [mul_comm]⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext fun i => by simp [← hy i]⟩
  rw [this, AddSubgroup.index_pi]
  simp [Int.index_zmultiples]

theorem natCard_nsmul_ker_pi (r n : ℕ) (hn : n ≠ 0) :
    Nat.card (nsmulAddMonoidHom n : (Fin r → ℤ) →+ (Fin r → ℤ)).ker = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨0⟩⟩
  have hx := x.2; have hy := y.2
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hx hy
  funext i
  have h1 := congrFun hx i; have h2 := congrFun hy i
  simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero, hn,
    false_or] at h1 h2
  rw [h1, h2]

theorem rank_pi_prod_of_finite (r : ℕ) (T : Type) [AddCommGroup T] [Finite T] :
    Module.rank ℤ ((Fin r → ℤ) × T) = r := by
  have hT : Module.rank ℤ T = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    refine ⟨(Nat.card T : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
    rw [natCast_zsmul]
    exact card_nsmul_eq_zero'
  have h := (LinearMap.fst ℤ (Fin r → ℤ) T).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.2 LinearMap.fst_surjective, rank_top, LinearMap.ker_fst,
    rank_range_of_injective _ LinearMap.inr_injective, hT, add_zero,
    rank_fin_fun] at h
  exact h.symm

/-- **Index of `n`-th multiples in a finitely generated abelian group.** If `A` is finitely
generated and `n ≠ 0`, then `[A : nA] = n ^ r · |A[n]|`, where `r` is the rank of `A`. -/
theorem index_nsmul_range [AddGroup.FG A] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom n : A →+ A).range.index =
      n ^ Module.finrank ℤ A * Nat.card (nsmulAddMonoidHom n : A →+ A).ker := by
  obtain ⟨r, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := DirectSum ι fun i => ZMod (p i ^ e i)
  have : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let g : A ≃+ (Fin r → ℤ) × T :=
    f.trans (AddEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)).toAddEquiv
      (AddEquiv.refl T))
  have hrank : Module.finrank ℤ A = r := by
    rw [g.toIntLinearEquiv.finrank_eq, Module.finrank, rank_pi_prod_of_finite]
    simp
  rw [hrank, ← AddSubgroup.index_map_equiv _ g, nsmul_range_map_equiv, nsmul_range_prod,
    AddSubgroup.index_prod, index_nsmul_range_pi, index_nsmul_range_of_finite,
    natCard_nsmul_ker_congr g, natCard_nsmul_ker_prod, natCard_nsmul_ker_pi r n hn, one_mul]

end PowerIndex

section MulPowerIndex

variable {G : Type*} [CommGroup G]

/-- Multiplicative form of `index_nsmul_range`: `[G : Gⁿ] = n ^ r · |G[n]|`. -/
theorem index_pow_range [Monoid.FG G] (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ Module.finrank ℤ (Additive G) * Nat.card (powMonoidHom n : G →* G).ker := by
  have : AddMonoid.FG (Additive G) := Monoid.fg_iff_add_fg.1 inferInstance
  have : AddGroup.FG (Additive G) := AddGroup.fg_iff_addMonoid_fg.2 this
  have e1 : Subgroup.toAddSubgroup (powMonoidHom n : G →* G).range =
      (nsmulAddMonoidHom n : Additive G →+ Additive G).range := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul y, ?_⟩
      rw [nsmulAddMonoidHom_apply, ← ofMul_pow]
      exact congrArg Additive.ofMul hy
    · rintro ⟨y, rfl⟩
      exact ⟨y.toMul, rfl⟩
  have e2 : Nat.card (powMonoidHom n : G →* G).ker =
      Nat.card (nsmulAddMonoidHom n : Additive G →+ Additive G).ker :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun _ => Iff.rfl)
  rw [← Subgroup.index_toAddSubgroup, e1, e2]
  exact index_nsmul_range n hn

end MulPowerIndex

section SUnits

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The `S`-units of `K`: the nonzero elements of `K` that are units at every finite place
outside the finite set `S` of finite places. -/
noncomputable abbrev sUnits : Subgroup Kˣ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K

/-- The valuation vector `x ↦ (v(x))_{v ∈ S}` of an `S`-unit. -/
noncomputable def valuationVector : sUnits K S →* (S → Multiplicative ℤ) :=
  MonoidHom.pi fun v => v.1.valuationOfNeZero.comp (sUnits K S).subtype

theorem valuationVector_apply (x : sUnits K S) (v : S) :
    valuationVector K S x v = v.1.valuationOfNeZero (x : Kˣ) := rfl

/-- The global units of `𝓞 K`, viewed as `S`-units. -/
noncomputable def unitsToSUnits : (𝓞 K)ˣ →* sUnits K S :=
  (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).codRestrict _ fun x v _ => by
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq]
    rfl

theorem unitsToSUnits_injective : Function.Injective (unitsToSUnits K S) := by
  intro x y h
  apply Units.map_injective (f := (algebraMap (𝓞 K) K : 𝓞 K →* K))
    (IsFractionRing.injective (𝓞 K) K)
  exact congrArg Subtype.val h

theorem valuation_eq_one_of_mem_ker {x : sUnits K S} (hx : x ∈ (valuationVector K S).ker)
    (v : HeightOneSpectrum (𝓞 K)) : v.valuation K ((x : Kˣ) : K) = 1 := by
  by_cases hv : v ∈ S
  · have := congrFun hx ⟨v, hv⟩
    rw [valuationVector_apply] at this
    rw [← HeightOneSpectrum.valuationOfNeZero_eq]
    simp [this]
  · exact x.2 v (by simpa using hv)

theorem range_unitsToSUnits : (unitsToSUnits K S).range = (valuationVector K S).ker := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    funext v
    rw [valuationVector_apply]
    exact HeightOneSpectrum.valuation_of_unit_eq v.1 u
  · intro hx
    have h1 := valuation_eq_one_of_mem_ker K S hx
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((x : Kˣ) : K)
      fun v => (h1 v).le
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K
      (((x : Kˣ)⁻¹ : Kˣ) : K) fun v => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, h1 v, inv_one]
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    refine ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Subtype.ext (Units.ext ?_)⟩
    exact ha

/-- The kernel of the valuation vector is the group of global units. -/
noncomputable def kerEquivUnits : (valuationVector K S).ker ≃* (𝓞 K)ˣ :=
  ((MonoidHom.ofInjective (unitsToSUnits_injective K S)).trans
    (MulEquiv.subgroupCongr (range_unitsToSUnits K S))).symm

/-- Some power of every finite place is principal, generated by an element lying in no other
finite place. -/
theorem exists_generator (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : 𝓞 K, g ≠ 0 ∧ g ∈ v.asIdeal ∧ ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → g ∉ w.asIdeal := by
  set h := Fintype.card (ClassGroup (𝓞 K))
  have hh : h ≠ 0 := Fintype.card_ne_zero
  have hI0 : v.asIdeal ≠ 0 := v.ne_bot
  have hmem := mem_nonZeroDivisors_of_ne_zero hI0
  have hprin : (v.asIdeal ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hmem h)]
    have := pow_card_eq_one (G := ClassGroup (𝓞 K)) (x := ClassGroup.mk0 ⟨v.asIdeal, hmem⟩)
    rwa [← map_pow, SubmonoidClass.mk_pow] at this
  have := hprin
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (v.asIdeal ^ h)
  have hle : v.asIdeal ^ h ≤ v.asIdeal := Ideal.pow_le_self hh
  refine ⟨g, ?_, ?_, ?_⟩
  · rintro rfl
    rw [Submodule.span_zero_singleton] at hg
    exact pow_ne_zero h hI0 hg
  · exact hle (by rw [hg]; exact Submodule.mem_span_singleton_self g)
  · intro w hw hgw
    apply hw
    have h1 : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [hg]; exact (Ideal.span_singleton_le_iff_mem _).2 hgw
    have := w.isPrime
    have h2 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h1
    exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2)).symm

/-- For `v ∈ S`, an `S`-unit whose valuation vector is supported at `v`. -/
noncomputable def generatorUnit (v : S) : sUnits K S :=
  ⟨Units.mk0 (algebraMap (𝓞 K) K (exists_generator K v.1).choose) (by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact (exists_generator K v.1).choose_spec.1), fun w hw => by
    have hwv : w ≠ v.1 := fun h => hw (h ▸ v.2)
    exact le_antisymm (w.valuation_le_one _) (not_lt.1 fun hlt =>
      (exists_generator K v.1).choose_spec.2.2 w hwv ((w.valuation_lt_one_iff_mem _).1 hlt))⟩

theorem valuationVector_generatorUnit_ne (v : S) :
    valuationVector K S (generatorUnit K S v) v ≠ 1 := by
  intro h
  rw [valuationVector_apply, ← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq] at h
  have hlt := (v.1.valuation_lt_one_iff_mem (K := K) _).2 (exists_generator K v.1).choose_spec.2.1
  exact (ne_of_lt hlt) h

theorem valuationVector_generatorUnit_of_ne (v w : S) (hwv : w ≠ v) :
    valuationVector K S (generatorUnit K S v) w = 1 := by
  rw [valuationVector_apply, ← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq]
  have hw : w.1 ≠ v.1 := fun h => hwv (Subtype.ext h)
  exact le_antisymm (w.1.valuation_le_one _) (not_lt.1 fun hlt =>
    (exists_generator K v.1).choose_spec.2.2 w.1 hw ((w.1.valuation_lt_one_iff_mem _).1 hlt))

/-- The valuation vectors of `S`-units form a subgroup of finite index. -/
theorem index_range_valuationVector_ne_zero : (valuationVector K S).range.index ≠ 0 := by
  classical
  let m : S → Multiplicative ℤ := fun v => valuationVector K S (generatorUnit K S v) v
  let H : Subgroup (S → Multiplicative ℤ) :=
    Subgroup.pi Set.univ fun v =>
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (Multiplicative.toAdd (m v) : ℤ))
  have hH : H ≤ (valuationVector K S).range := by
    intro f hf
    have hf' : ∀ v, ∃ k : ℤ, m v ^ k = f v := fun v => by
      have hv : Multiplicative.toAdd (f v) ∈
          AddSubgroup.zmultiples (Multiplicative.toAdd (m v) : ℤ) := hf v (Set.mem_univ v)
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hv
      exact ⟨k, Multiplicative.toAdd.injective (by rw [toAdd_zpow]; exact hk)⟩
    choose k hk using hf'
    rw [← Finset.univ_prod_mulSingle f]
    refine Subgroup.prod_mem _ fun v _ => ?_
    have : Pi.mulSingle v (f v) = valuationVector K S (generatorUnit K S v ^ k v) := by
      rw [map_zpow, ← hk v]
      funext w
      by_cases hw : w = v
      · subst hw
        simp [m]
      · simp [hw, valuationVector_generatorUnit_of_ne K S v w hw]
    rw [this]
    exact ⟨_, rfl⟩
  refine ne_zero_of_dvd_ne_zero ?_ (Subgroup.index_dvd_of_le hH)
  rw [Subgroup.index_pi, Finset.prod_ne_zero_iff]
  intro v _
  rw [AddSubgroup.index_toSubgroup, Int.index_zmultiples, Int.natAbs_ne_zero]
  intro h0
  apply valuationVector_generatorUnit_ne K S v
  exact Multiplicative.toAdd.injective h0

/-- The group of valuation vectors of `S`-units is free of rank `|S|`. -/
theorem nonempty_rangeEquiv :
    Nonempty ((valuationVector K S).range ≃* (S → Multiplicative ℤ)) :=
  Int.subgroup_index_ne_zero_iff.1 (index_range_valuationVector_ne_zero K S)

/-- The valuation vector as a `ℤ`-linear map on additive groups. -/
noncomputable abbrev valuationVectorLinear :
    Additive (sUnits K S) →ₗ[ℤ] Additive (S → Multiplicative ℤ) :=
  (MonoidHom.toAdditive (valuationVector K S)).toIntLinearMap

/-- The kernel of `valuationVectorLinear` is the additive group of global units. -/
noncomputable def kerLinearEquiv :
    LinearMap.ker (valuationVectorLinear K S) ≃ₗ[ℤ] Additive (𝓞 K)ˣ :=
  AddEquiv.toIntLinearEquiv <|
    ({ toFun := fun x => Additive.ofMul ⟨Additive.toMul x.1, x.2⟩
       invFun := fun y => ⟨Additive.ofMul (Additive.toMul y).1, (Additive.toMul y).2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
        LinearMap.ker (valuationVectorLinear K S) ≃+ Additive (valuationVector K S).ker).trans
      (MulEquiv.toAdditive (kerEquivUnits K S))

/-- The range of `valuationVectorLinear` is free of rank `|S|`. -/
noncomputable def rangeLinearEquiv :
    LinearMap.range (valuationVectorLinear K S) ≃ₗ[ℤ] (S → ℤ) :=
  AddEquiv.toIntLinearEquiv <|
    (({ toFun := fun x => Additive.ofMul ⟨Additive.toMul x.1, by
          obtain ⟨y, hy⟩ := x.2
          exact ⟨Additive.toMul y, congrArg Additive.toMul hy⟩⟩
        invFun := fun y => ⟨Additive.ofMul (Additive.toMul y).1, by
          obtain ⟨z, hz⟩ := (Additive.toMul y).2
          exact ⟨Additive.ofMul z, congrArg Additive.ofMul hz⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl } :
        LinearMap.range (valuationVectorLinear K S) ≃+ Additive (valuationVector K S).range).trans
      (MulEquiv.toAdditive (nonempty_rangeEquiv K S).some)).trans
    { toFun := fun x v => Multiplicative.toAdd (Additive.toMul x v)
      invFun := fun y => Additive.ofMul fun v => Multiplicative.ofAdd (y v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

instance : Module.Finite ℤ (Additive (sUnits K S)) := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (valuationVectorLinear K S) ?_ ?_⟩
  · rw [Submodule.map_top, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv (rangeLinearEquiv K S).symm
  · rw [top_inf_eq, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv (kerLinearEquiv K S).symm

instance : Monoid.FG (sUnits K S) := by
  have : AddGroup.FG (Additive (sUnits K S)) := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact Monoid.fg_iff_add_fg.2 (AddGroup.fg_iff_addMonoid_fg.1 this)

/-- **S-unit theorem (rank).** The rank of the `S`-units is `r₁ + r₂ - 1 + |S|`. -/
theorem finrank_sUnits :
    Module.finrank ℤ (Additive (sUnits K S)) = S.card + NumberField.Units.rank K := by
  apply Module.finrank_eq_of_rank_eq
  have h := (valuationVectorLinear K S).rank_range_add_rank_ker
  rw [(rangeLinearEquiv K S).rank_eq, (kerLinearEquiv K S).rank_eq, rank_fun',
    ← Module.finrank_eq_rank, NumberField.Units.finrank_eq] at h
  rw [← h, Fintype.card_coe]
  push_cast
  rfl

/-- The `p`-torsion of the `S`-units consists of the `p`-th roots of unity of `K`. -/
noncomputable def powKerEquivRootsOfUnity (p : ℕ) [NeZero p] :
    (powMonoidHom p : sUnits K S →* sUnits K S).ker ≃ rootsOfUnity p K where
  toFun x := ⟨(x.1 : Kˣ), by
    rw [mem_rootsOfUnity]
    exact congrArg Subtype.val x.2⟩
  invFun z := ⟨⟨z.1, fun v _ => by
      have hz : (z.1 : Kˣ) ^ p = 1 := (mem_rootsOfUnity p z.1).1 z.2
      have h1 : v.valuation K ((z.1 : Kˣ) : K) ^ p = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]
      exact (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne p)⟩, Subtype.ext ((mem_rootsOfUnity p z.1).1 z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Index of `p`-th powers in the `S`-units.** If `K` contains a primitive `p`-th root of
unity, then `[U_S : U_S^p] = p ^ (|S| + |S_∞|)`, where `S_∞` is the set of infinite places. -/
theorem index_pow_sUnits (p : ℕ) [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (powMonoidHom p : sUnits K S →* sUnits K S).range.index =
      p ^ (S.card + Fintype.card (NumberField.InfinitePlace K)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [index_pow_range p hp.out.ne_zero, finrank_sUnits,
    Nat.card_congr (powKerEquivRootsOfUnity K S p),
    hζ.card_rootsOfUnity, ← pow_succ, add_assoc, NumberField.Units.rank,
    Nat.sub_add_cancel Fintype.card_pos]

end SUnits

end Langlands.Global.Arithmetic.SUnitIndex
