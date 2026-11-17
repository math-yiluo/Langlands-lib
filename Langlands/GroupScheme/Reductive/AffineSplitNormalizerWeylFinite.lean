import Langlands.GroupScheme.Reductive.AffineSplitNormalizerWeylClauses
import Langlands.Group.RootPairingCoxeterProof

/-! # A finite subgroup of normalizer points inducing the Weyl group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineSplitNormalizerWeyl

/-! ### The rational root pairing of a coordinate root datum -/

section RatPairing

variable {J I : Type*}

/-- The cast `ℤ^I → ℚ^I`. -/
def castVec (m : I → ℤ) : I → ℚ := fun j => (m j : ℚ)

@[simp] theorem castVec_apply (m : I → ℤ) (j : I) : castVec m j = (m j : ℚ) := rfl

theorem castVec_injective : Function.Injective (castVec (I := I)) := by
  intro m m' h
  funext j
  have := congrFun h j
  simpa using this

@[simp] theorem castVec_sub (m m' : I → ℤ) : castVec (m - m') = castVec m - castVec m' := by
  funext j; simp

@[simp] theorem castVec_zsmul (k : ℤ) (m : I → ℤ) : castVec (k • m) = (k : ℚ) • castVec m := by
  funext j; simp

variable [Fintype I] [DecidableEq I] (P : RootDatum J (I → ℤ) (I → ℤ))

/-- The rational functional `x ↦ ⟨x, y⟩` of an integral coweight `y`. -/
def dualOf (y : I → ℤ) : Module.Dual ℚ (I → ℚ) :=
  ∑ l, ((P.toLinearMap (Pi.single l 1) y : ℤ) : ℚ) • LinearMap.proj l

theorem dualOf_castVec (y m : I → ℤ) :
    dualOf P y (castVec m) = ((P.toLinearMap m y : ℤ) : ℚ) := by
  conv_rhs => rw [← Finset.univ_sum_single m]
  simp only [dualOf, LinearMap.smul_apply, LinearMap.proj_apply, castVec_apply, smul_eq_mul,
    map_sum, LinearMap.sum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (Pi.single l (m l) : I → ℤ) = m l • Pi.single l 1 by
    ext k; by_cases h : k = l <;> simp [h]]
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, mul_comm]

theorem dualOf_sub_zsmul (y y' : I → ℤ) (k : ℤ) :
    dualOf P (y - k • y') = dualOf P y - (k : ℚ) • dualOf P y' := by
  simp only [dualOf, map_sub, map_zsmul, smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_smul,
    Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]

theorem dualOf_injective : Function.Injective (dualOf P) := by
  intro y y' h
  apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
  refine LinearMap.ext fun m => ?_
  have := LinearMap.congr_fun h (castVec m)
  rw [dualOf_castVec, dualOf_castVec] at this
  exact_mod_cast this

/-- The rational root pairing of a coordinate root datum: roots are cast to `ℚ^I` and
coroots become the corresponding functionals. -/
def ratPairing : RootPairing J ℚ (I → ℚ) (Module.Dual ℚ (I → ℚ)) where
  toLinearMap := Module.Dual.eval ℚ (I → ℚ)
  root := ⟨fun a => castVec (P.root a), castVec_injective.comp P.root.injective⟩
  coroot := ⟨fun a => dualOf P (P.coroot a), (dualOf_injective P).comp P.coroot.injective⟩
  root_coroot_two a := by
    simp [dualOf_castVec]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root a b := by
    simp only [Function.Embedding.coeFn_mk, Module.Dual.eval_apply, dualOf_castVec]
    rw [← P.reflectionPerm_root a b, castVec_sub, castVec_zsmul]
  reflectionPerm_coroot a b := by
    simp only [Function.Embedding.coeFn_mk, Module.Dual.eval_apply, dualOf_castVec]
    rw [← P.reflectionPerm_coroot a b, dualOf_sub_zsmul]

@[simp] theorem ratPairing_root (a : J) : (ratPairing P).root a = castVec (P.root a) := rfl

@[simp] theorem ratPairing_coroot (a : J) :
    (ratPairing P).coroot a = dualOf P (P.coroot a) := rfl

theorem ratPairing_pairing (a b : J) :
    (ratPairing P).pairing a b = (P.pairing a b : ℚ) := by
  change dualOf P (P.coroot b) (castVec (P.root a)) = _
  rw [dualOf_castVec, P.root_coroot_eq_pairing]

instance : (ratPairing P).IsCrystallographic where
  exists_value a b := ⟨P.pairing a b, by rw [ratPairing_pairing]; rfl⟩

theorem ratPairing_reflection_castVec (a : J) (m : I → ℤ) :
    (ratPairing P).reflection a (castVec m) = castVec (P.reflection a m) := by
  rw [RootPairing.reflection_apply, RootPairing.reflection_apply, castVec_sub, castVec_zsmul]
  change castVec m - (dualOf P (P.coroot a) (castVec m)) • castVec (P.root a) = _
  rw [dualOf_castVec]
  rfl

end RatPairing

/-! ### Comparing the Weyl groups of `P` and of its rational pairing -/

section Transfer

variable {J I : Type*} [Fintype I] [DecidableEq I] (P : RootDatum J (I → ℤ) (I → ℤ))

/-- `g` and `g'` act compatibly on integral weights. -/
def Compat (g : RootPairing.Aut P) (g' : RootPairing.Aut (ratPairing P)) : Prop :=
  ∀ m : I → ℤ, g' • castVec m = castVec (g • m)

theorem compat_one : Compat P 1 1 := fun m => by simp

variable {P} in
theorem Compat.mul {g h : RootPairing.Aut P} {g' h' : RootPairing.Aut (ratPairing P)}
    (hg : Compat P g g') (hh : Compat P h h') : Compat P (g * h) (g' * h') :=
  fun m => by rw [mul_smul, mul_smul, hh, hg]

variable {P} in
theorem Compat.inv {g : RootPairing.Aut P} {g' : RootPairing.Aut (ratPairing P)}
    (hg : Compat P g g') : Compat P g⁻¹ g'⁻¹ := fun m => by
  have h := hg (g⁻¹ • m)
  rw [smul_inv_smul] at h
  rw [← h, inv_smul_smul]

variable {P} in
theorem Compat.pow {g : RootPairing.Aut P} {g' : RootPairing.Aut (ratPairing P)}
    (hg : Compat P g g') (k : ℕ) : Compat P (g ^ k) (g' ^ k) := by
  induction k with
  | zero => simpa using compat_one P
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hg

theorem compat_reflection (a : J) :
    Compat P (RootPairing.Equiv.reflection P a)
      (RootPairing.Equiv.reflection (ratPairing P) a) := fun m => by
  simp only [RootPairing.Equiv.reflection_smul]
  exact ratPairing_reflection_castVec P a m

variable {P} in
theorem Compat.eq {g h : RootPairing.Aut P} {g' : RootPairing.Aut (ratPairing P)}
    (hg : Compat P g g') (hh : Compat P h g') : g = h := by
  apply RootPairing.Equiv.weightHom_injective P
  refine LinearEquiv.ext fun m => castVec_injective ?_
  change castVec (g • m) = castVec (h • m)
  rw [← hg, ← hh]

variable {P} in
theorem Compat.eq_one {g : RootPairing.Aut P} (hg : Compat P g 1) : g = 1 :=
  hg.eq (compat_one P)

end Transfer

/-! ### A Coxeter presentation of the Weyl group of `P` -/

section Coxeter

open IsAddIndecomposable

variable {J I : Type*} [Fintype I] [DecidableEq I] (P : RootDatum J (I → ℤ) (I → ℤ))

/-- The Weyl group of a finite reduced coordinate root datum has a set `B` of simple roots
with the following properties. The rational Weyl group is a finite Coxeter group on `B`. The
integral simple reflections satisfy its Coxeter relations. Every reflection lies in the
subgroup generated by the simple ones. Distinct simple roots have Coxeter weight `≠ 4`. -/
theorem exists_simple_coxeter [Finite J] [P.IsReduced] :
    ∃ (B : Set J) (Mx : CoxeterMatrix B) (_ : CoxeterSystem Mx (ratPairing P).weylGroup),
      Finite (ratPairing P).weylGroup ∧
      (∀ a b : B, (RootPairing.Equiv.reflection P a * RootPairing.Equiv.reflection P b) ^
        Mx a b = 1) ∧
      (∀ a : J, RootPairing.Equiv.reflection P a ∈
        Subgroup.closure (Set.range fun b : B => RootPairing.Equiv.reflection P b)) ∧
      (∀ a b : B, a ≠ b → P.coxeterWeight a b ≠ 4) := by
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℚ (I → ℚ), ∀ a, f ((ratPairing P).root a) ≠ 0 :=
    Module.exists_dual_forall_apply_ne_zero (ratPairing P).root fun a => (ratPairing P).ne_zero a
  obtain ⟨hfin, Mx, cs, hsimple, -, -⟩ :=
    Langlands.Group.rootPairingWeylCoxeterStatement_proof J ℚ (I → ℚ)
      (Module.Dual ℚ (I → ℚ)) (ratPairing P) f hf
  refine ⟨_, Mx, cs, hfin, fun a b => ?_, fun a => ?_, fun a b hab => ?_⟩
  · have h := cs.simple_mul_simple_pow a b
    rw [hsimple, hsimple] at h
    have hc : Compat P ((RootPairing.Equiv.reflection P a *
        RootPairing.Equiv.reflection P b) ^ Mx a b)
        (((RootPairing.weylGroup.ofIdx (ratPairing P) a *
          RootPairing.weylGroup.ofIdx (ratPairing P) b) ^ Mx a b :
            (ratPairing P).weylGroup) : RootPairing.Aut (ratPairing P)) :=
      ((compat_reflection P a).mul (compat_reflection P b)).pow _
    rw [h] at hc
    exact hc.eq_one
  · have key : ∀ x ∈ Subgroup.closure (Set.range cs.simple),
        ∃ g ∈ Subgroup.closure (Set.range fun b : ↥(baseOf (ratPairing P).root
          (f : (I → ℚ) →+ ℚ)) => RootPairing.Equiv.reflection P (b : J)),
          Compat P g (x : RootPairing.Aut (ratPairing P)) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        refine ⟨RootPairing.Equiv.reflection P b, Subgroup.subset_closure ⟨b, rfl⟩, ?_⟩
        rw [hsimple]
        exact compat_reflection P b
      | one => exact ⟨1, one_mem _, compat_one P⟩
      | mul x y _ _ hx hy =>
        obtain ⟨g, hg, hgc⟩ := hx
        obtain ⟨h, hh, hhc⟩ := hy
        exact ⟨g * h, mul_mem hg hh, hgc.mul hhc⟩
      | inv x _ hx =>
        obtain ⟨g, hg, hgc⟩ := hx
        exact ⟨g⁻¹, inv_mem hg, hgc.inv⟩
    obtain ⟨g, hg, hgc⟩ := key (RootPairing.weylGroup.ofIdx (ratPairing P) a)
      (by rw [cs.subgroup_closure_range_simple]; trivial)
    rwa [← hgc.eq (compat_reflection P a)]
  · apply P.coxeterWeight_ne_four_of_linearIndependent
    by_contra hli
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) a b hli with h | h
    · exact hab (Subtype.ext (P.root.injective h))
    · have ha := baseOf_subset_pos (ratPairing P).root (f : (I → ℚ) →+ ℚ) a.2
      have hb := baseOf_subset_pos (ratPairing P).root (f : (I → ℚ) →+ ℚ) b.2
      change 0 < f ((ratPairing P).root a) at ha
      change 0 < f ((ratPairing P).root b) at hb
      have he : f ((ratPairing P).root a) = - f ((ratPairing P).root b) := by
        rw [ratPairing_root, ratPairing_root, h,
          show castVec (-P.root b) = -castVec (P.root b) by funext j; simp, map_neg]
      linarith

end Coxeter

/-! ### Torsion lemmas -/

section Torsion

variable {A : Type*} [CommGroup A]

/-- An element with a torsion nonzero integer power is torsion. -/
theorem isOfFinOrder_of_zpow {x : A} {k : ℤ} (h : IsOfFinOrder (x ^ k)) (hk : k ≠ 0) :
    IsOfFinOrder x := by
  have h' : IsOfFinOrder (x ^ k.natAbs) := by
    rcases Int.natAbs_eq k with hk' | hk'
    · rw [hk', zpow_natCast] at h
      exact h
    · rw [hk', zpow_neg, zpow_natCast] at h
      exact isOfFinOrder_inv_iff.mp h
  exact h'.of_pow (Int.natAbs_ne_zero.mpr hk)

/-- **Sign lemma.** If `y² x⁻ᵖ` and `x² y⁻ᵠ` are torsion and `p q ≠ 4`, then `x` is
torsion: `(x² y⁻ᵠ)² (y² x⁻ᵖ)ᵠ = x^(4 - p q)`. -/
theorem isOfFinOrder_of_pair {x y : A} {p q : ℤ} (hpq : p * q ≠ 4)
    (h₁ : IsOfFinOrder (y ^ (2 : ℤ) * x ^ (-p))) (h₂ : IsOfFinOrder (x ^ (2 : ℤ) * y ^ (-q))) :
    IsOfFinOrder x := by
  have h : (x ^ (2 : ℤ) * y ^ (-q)) ^ (2 : ℤ) * (y ^ (2 : ℤ) * x ^ (-p)) ^ q =
      x ^ (4 - p * q) := by
    rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    group
  have h₃ : IsOfFinOrder (x ^ (4 - p * q)) := by
    rw [← h]
    exact h₂.zpow.mul h₁.zpow
  exact isOfFinOrder_of_zpow h₃ (by omega)

variable {I : Type*} [Fintype I]

/-- The value `∏ⱼ tⱼ ^ mⱼ` of the character `m` at `t`. -/
def charValue (t : I → A) (m : I → ℤ) : A := ∏ j, t j ^ m j

theorem charValue_add (t : I → A) (m m' : I → ℤ) :
    charValue t (m + m') = charValue t m * charValue t m' := by
  simp only [charValue, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem charValue_neg (t : I → A) (m : I → ℤ) : charValue t (-m) = (charValue t m)⁻¹ := by
  simp only [charValue, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem charValue_zsmul (t : I → A) (k : ℤ) (m : I → ℤ) :
    charValue t (k • m) = charValue t m ^ k := by
  simp only [charValue, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm, zpow_mul]

theorem charValue_single [DecidableEq I] (t : I → A) (j : I) :
    charValue t (Pi.single j 1) = t j := by
  rw [charValue, Finset.prod_eq_single j (fun l _ hl => by simp [hl]) (by simp)]
  simp

variable {J : Type*}

theorem charValue_reflection_mul (P : RootDatum J (I → ℤ) (I → ℤ)) (t : I → A) (a : J)
    (m : I → ℤ) :
    charValue t (P.reflection a m) * charValue t m =
      charValue t m ^ (2 : ℤ) * charValue t (P.root a) ^ (-P.toLinearMap m (P.coroot a)) := by
  rw [RootPairing.reflection_apply, sub_eq_add_neg, charValue_add, charValue_neg,
    charValue_zsmul, zpow_neg, zpow_two, mul_right_comm]
  rfl

/-- If `χ_{s_a m} χ_m` and `χ_{s_b m} χ_m` are torsion at `t` for every character `m`, and
the Coxeter weight of `a, b` is not `4`, then every coordinate of `t` is torsion. -/
theorem isOfFinOrder_of_reflection_pair [DecidableEq I] (P : RootDatum J (I → ℤ) (I → ℤ))
    {a b : J} (hab : P.coxeterWeight a b ≠ 4) (t : I → A)
    (ha : ∀ m, IsOfFinOrder (charValue t (P.reflection a m) * charValue t m))
    (hb : ∀ m, IsOfFinOrder (charValue t (P.reflection b m) * charValue t m)) (j : I) :
    IsOfFinOrder (t j) := by
  have hx : IsOfFinOrder (charValue t (P.root a)) := by
    have h₁ := ha (P.root b)
    have h₂ := hb (P.root a)
    rw [charValue_reflection_mul] at h₁ h₂
    refine isOfFinOrder_of_pair (p := P.toLinearMap (P.root b) (P.coroot a))
      (q := P.toLinearMap (P.root a) (P.coroot b)) ?_ h₁ h₂
    rw [RootPairing.root_coroot_eq_pairing, RootPairing.root_coroot_eq_pairing, mul_comm]
    exact hab
  have hm := ha (Pi.single j 1)
  rw [charValue_reflection_mul, charValue_single] at hm
  have h₂ : IsOfFinOrder (t j ^ (2 : ℤ)) := by
    have := hm.mul (hx.zpow (i := P.toLinearMap (Pi.single j 1) (P.coroot a)))
    rwa [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one] at this
  exact isOfFinOrder_of_zpow h₂ two_ne_zero

end Torsion

/-! ### A finiteness criterion -/

/-- Let `H` be a finitely generated subgroup of `Gt` and `f : H →* Q` a homomorphism with
finite range. Suppose every element of the kernel of `f` is the image of a torsion element
under an injective homomorphism `τ : A →* Gt` from a commutative group. Then `H` is finite. -/
theorem finite_of_ker_torsion {Gt Q A : Type*} [Group Gt] [Group Q] [CommGroup A]
    {H : Subgroup Gt} [Group.FG H] (f : H →* Q) [Finite f.range] (τ : A →* Gt)
    (hτ : Function.Injective τ) (hker : ∀ g ∈ f.ker, ∃ a, IsOfFinOrder a ∧ τ a = (g : Gt)) :
    Finite H := by
  have : f.ker.FiniteIndex := ⟨by rw [Subgroup.index_ker]; exact Nat.card_pos.ne'⟩
  have hfg : Group.FG f.ker := Subgroup.fg_of_index_ne_zero f.ker
  let κ : f.ker →* τ.range := (H.subtype.comp f.ker.subtype).codRestrict τ.range fun g => by
    obtain ⟨a, -, ha⟩ := hker g g.2
    exact ⟨a, ha⟩
  let ψ : f.ker →* A := (MonoidHom.ofInjective hτ).symm.toMonoidHom.comp κ
  have hτψ : ∀ g, τ (ψ g) = ((g : H) : Gt) := by
    intro g
    have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hτ).apply_symm_apply (κ g))
    rw [MonoidHom.ofInjective_apply] at h1
    exact h1
  have hψ : Function.Injective ψ := by
    intro g g' h
    have h' := congrArg τ h
    rw [hτψ, hτψ] at h'
    exact Subtype.ext (Subtype.ext h')
  have hfgr : Group.FG ψ.range := Group.fg_of_surjective ψ.rangeRestrict_surjective
  have hrt : IsMulTorsion ψ.range := by
    rintro ⟨_, g, rfl⟩
    rw [← Submonoid.isOfFinOrder_coe (H := ψ.range.toSubmonoid)]
    change IsOfFinOrder (ψ g)
    obtain ⟨a, ha, hag⟩ := hker g g.2
    have hga : ψ g = a := hτ (by rw [hτψ, hag])
    rw [hga]
    exact ha
  have : Finite ψ.range := CommGroup.finite_of_fg_isMulTorsion (G := ψ.range) hrt
  have hkf : Finite f.ker :=
    Finite.of_injective ψ.rangeRestrict fun g g' h => hψ (congrArg Subtype.val h)
  exact (Subgroup.finite_iff_finite_and_finiteIndex f.ker).2 ⟨hkf, inferInstance⟩

/-- In a group, if `x² = y² = 1` then conjugating `(x y)^m` by `x` or by `y` inverts it. -/
theorem conj_pow_mul_eq_one {Γ : Type*} [Group Γ] {x y : Γ} (hx : x * x = 1) (hy : y * y = 1)
    (m : ℕ) :
    x * (x * y) ^ m * x⁻¹ * (x * y) ^ m = 1 ∧ y * (x * y) ^ m * y⁻¹ * (x * y) ^ m = 1 := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hyx : y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hx', hy']
  have h1 : x * (x * y) * x⁻¹ = y * x := by
    rw [← mul_assoc, hx, one_mul, hx']
  have h2 : y * (x * y) * y⁻¹ = y * x := by
    rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← conj_pow, h1, hyx, inv_pow, inv_mul_cancel]
  · rw [← conj_pow, h2, hyx, inv_pow, inv_mul_cancel]

/-! ### The relation `Induces` under products -/

section InducesLemmas

variable {S : Scheme.{u}} {G : GroupScheme S} {I : Type u} [Fintype I]
  {i : splitTorus S I ⟶ G} {J : Type*} {P : RootDatum J (I → ℤ) (I → ℤ)}

theorem groupHom_id_comp {U : Over S} (x : U ⟶ (splitTorus S I).X) :
    x ≫ (CommGroupScheme.groupHom (𝟙 (splitTorus.commGroupScheme S I))).hom.hom = x :=
  Category.comp_id x

variable (i P) in
theorem induces_one : Induces i (P := P) 1 1 :=
  ⟨Iso.refl _, IsNormalizingPoint.one, fun U x m => by
    rw [one_smul]
    exact congrArg (fun y => ∏ j, splitTorus.pointsEquiv I U y j ^ m j) (groupHom_id_comp x)⟩

theorem Induces.mul {n n' : Over.mk (𝟙 S) ⟶ G.X} {w w' : RootPairing.Aut P}
    (h : Induces i n w) (h' : Induces i n' w') : Induces i (n * n') (w' * w) := by
  obtain ⟨σ, hσ, hc⟩ := h
  obtain ⟨σ', hσ', hc'⟩ := h'
  refine ⟨σ' ≪≫ σ, hσ.mul hσ', fun U x m => ?_⟩
  have hx : x ≫ (CommGroupScheme.groupHom (σ' ≪≫ σ).hom).hom.hom =
      (x ≫ (CommGroupScheme.groupHom σ'.hom).hom.hom) ≫
        (CommGroupScheme.groupHom σ.hom).hom.hom :=
    comp_groupHom_comp x σ'.hom σ.hom
  rw [hx, hc U _ m, hc' U x (w • m), mul_smul]

theorem Induces.inv {n : Over.mk (𝟙 S) ⟶ G.X} {w : RootPairing.Aut P}
    (h : Induces i n w) : Induces i n⁻¹ w⁻¹ := by
  obtain ⟨σ, hσ, hc⟩ := h
  refine ⟨σ.symm, hσ.inv, fun U x m => ?_⟩
  have hy : (x ≫ (CommGroupScheme.groupHom σ.inv).hom.hom) ≫
      (CommGroupScheme.groupHom σ.hom).hom.hom = x := by
    have h1 := comp_groupHom_comp x σ.inv σ.hom
    rw [Iso.inv_hom_id, groupHom_id_comp] at h1
    exact h1.symm
  have := hc U (x ≫ (CommGroupScheme.groupHom σ.inv).hom.hom) (w⁻¹ • m)
  rw [hy, smul_inv_smul] at this
  exact this.symm

theorem Induces.pow {n : Over.mk (𝟙 S) ⟶ G.X} {w : RootPairing.Aut P}
    (h : Induces i n w) (k : ℕ) : Induces i (n ^ k) (w ^ k) := by
  induction k with
  | zero => simpa using induces_one i P
  | succ k ih => rw [pow_succ', pow_succ]; exact h.mul ih

/-- A point inducing the identity centralizes the torus. -/
theorem Induces.mem_centralizerPoints {n : Over.mk (𝟙 S) ⟶ G.X} [DecidableEq I]
    (h : Induces i (P := P) n 1) :
    n ∈ centralizerPoints (T := splitTorus.commGroupScheme S I) i := by
  obtain ⟨σ, hσ, hc⟩ := h
  have hid : σ.hom = 𝟙 _ := by
    refine CommGroupScheme.hom_ext_points fun U x => ?_
    rw [groupHom_id_comp]
    apply (splitTorus.pointsEquiv I U).injective
    funext j
    have := hc U x (Pi.single j 1)
    rw [one_smul] at this
    change charValue _ _ = charValue _ _ at this
    rwa [charValue_single, charValue_single] at this
  have hσ' : σ = Iso.refl _ := Iso.ext hid
  exact (Langlands.GroupScheme.mem_centralizerPoints
    (T := splitTorus.commGroupScheme S I) i).2 (isNormalizingPoint_refl_iff.1 (hσ' ▸ hσ))

end InducesLemmas

/-! ### The finite subgroup -/

section Main

variable {S : Scheme.{u}} {G : GroupScheme S} {I : Type u} [Fintype I]
  {i : splitTorus S I ⟶ G} {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

theorem charValue_mul {A : Type*} [CommGroup A] (x y : I → A) (m : I → ℤ) :
    charValue (x * y) m = charValue x m * charValue y m := by
  simp only [charValue, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

variable (i) in
/-- Points of a fibrewise maximal closed split torus normalize it. -/
theorem torusPoint_mem_normalizerPoints (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    (t : Over.mk (𝟙 S) ⟶ (splitTorus S I).X) :
    t ≫ i.hom.hom ∈ normalizerPoints (T := splitTorus.commGroupScheme S I) i := by
  have hrange := splitTorusCentralizer_eq_range_of_fibrewiseMaximal hG
    (T := splitTorus.commGroupScheme S I) (isSplitTorus_splitTorus I) i hi hmax
  apply centralizerPoints_le_normalizerPoints (T := splitTorus.commGroupScheme S I) i
  have h : t ≫ i.hom.hom ∈ (torusCentralizer (T := splitTorus.commGroupScheme S I) i).carrier
      (Over.mk (𝟙 S)) := by
    rw [hrange]
    exact SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩
  exact (Langlands.GroupScheme.mem_centralizerPoints
    (T := splitTorus.commGroupScheme S I) i).2
    ((mem_torusCentralizer_base_iff (T := splitTorus.commGroupScheme S I) i _).1 h)

/-- Conjugating a torus point by a normalizing point applies the automorphism `σ`. -/
theorem conj_torusPoint {g : Over.mk (𝟙 S) ⟶ G.X}
    {σ : splitTorus.commGroupScheme S I ≅ splitTorus.commGroupScheme S I}
    (hσ : IsNormalizingPoint (T := splitTorus.commGroupScheme S I) i g σ)
    (t : Over.mk (𝟙 S) ⟶ (splitTorus S I).X) :
    g * (t ≫ i.hom.hom) * g⁻¹ = (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom := by
  have h := hσ.conj_comp (Over.mk (𝟙 S)) t
  rwa [constantPoint_self] at h

variable (i) in
/-- The torus points, in coordinates, as a subgroup of the normalizer points. -/
def torusHom (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i) :
    (I → (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ) →* normalizerPoints (T := splitTorus.commGroupScheme S I) i :=
  (MonoidHom.mk' (fun x => (splitTorus.pointsEquiv I (Over.mk (𝟙 S))).symm x ≫ i.hom.hom)
    fun x y => by rw [map_mul, MonObj.mul_comp]).codRestrict _ fun x =>
      torusPoint_mem_normalizerPoints i hG hi hmax _

theorem torusHom_val (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    (x : I → (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ) :
    (torusHom i hG hi hmax x : Over.mk (𝟙 S) ⟶ G.X) =
      (splitTorus.pointsEquiv I (Over.mk (𝟙 S))).symm x ≫ i.hom.hom := rfl

theorem torusHom_injective (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i) :
    Function.Injective (torusHom i hG hi hmax) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  intro x y h
  have h' := congrArg Subtype.val h
  rw [torusHom_val, torusHom_val] at h'
  exact (splitTorus.pointsEquiv I (Over.mk (𝟙 S))).symm.injective
    ((cancel_mono i.hom.hom).1 h')

variable (i) in
/-- The torsion torus points, as a subgroup of the normalizer points. -/
def torsionPoints (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i) :
    Subgroup (normalizerPoints (T := splitTorus.commGroupScheme S I) i) :=
  (CommGroup.torsion (I → (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ)).map (torusHom i hG hi hmax)

theorem torsionPoints_normal (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i) :
    (torsionPoints i hG hi hmax).Normal := by
  refine ⟨fun k hk g => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hk
  obtain ⟨σ, hσ⟩ := (mem_normalizerPoints (T := splitTorus.commGroupScheme S I) i).1 g.2
  let pe := splitTorus.pointsEquiv I (Over.mk (𝟙 S))
  let φ : (I → (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ) →* (I → (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ) :=
    MonoidHom.mk' (fun x => pe (pe.symm x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom))
      fun x y => by rw [map_mul, MonObj.mul_comp, map_mul]
  refine Subgroup.mem_map.mpr ⟨φ a, φ.isOfFinOrder ha, Subtype.ext ?_⟩
  rw [torusHom_val]
  change pe.symm (pe (pe.symm a ≫ (CommGroupScheme.groupHom σ.hom).hom.hom)) ≫ i.hom.hom =
    (g : Over.mk (𝟙 S) ⟶ G.X) * (pe.symm a ≫ i.hom.hom) * (g : Over.mk (𝟙 S) ⟶ G.X)⁻¹
  rw [conj_torusPoint hσ, MulEquiv.symm_apply_apply]

theorem mem_torsionPoints_of_sq (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    (g : normalizerPoints (T := splitTorus.commGroupScheme S I) i)
    (t : Over.mk (𝟙 S) ⟶ (splitTorus S I).X) (ht : t * t = 1)
    (hg : (g : Over.mk (𝟙 S) ⟶ G.X) = t ≫ i.hom.hom) : g ∈ torsionPoints i hG hi hmax := by
  refine Subgroup.mem_map.mpr ⟨splitTorus.pointsEquiv I (Over.mk (𝟙 S)) t,
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, ?_⟩, Subtype.ext ?_⟩
  · rw [pow_two, ← map_mul, ht, map_one]
  · rw [torusHom_val, MulEquiv.symm_apply_apply]
    exact hg.symm

/-- The key step. Let `z` be a normalizer point inducing the identity, and let `n_a`, `n_b`
induce the reflections `s_a`, `s_b` of roots with Coxeter weight `≠ 4`. If `n_a z n_a⁻¹ z` and
`n_b z n_b⁻¹ z` are torsion torus points, then so is `z`. -/
theorem mem_torsionPoints_of_conj [DecidableEq I] (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    {a b : J} (hab : P.coxeterWeight a b ≠ 4)
    {na nb z : normalizerPoints (T := splitTorus.commGroupScheme S I) i}
    (ha : Induces i (na : Over.mk (𝟙 S) ⟶ G.X) (RootPairing.Equiv.reflection P a))
    (hb : Induces i (nb : Over.mk (𝟙 S) ⟶ G.X) (RootPairing.Equiv.reflection P b))
    (hz : Induces i (P := P) (z : Over.mk (𝟙 S) ⟶ G.X) 1)
    (hza : na * z * na⁻¹ * z ∈ torsionPoints i hG hi hmax)
    (hzb : nb * z * nb⁻¹ * z ∈ torsionPoints i hG hi hmax) :
    z ∈ torsionPoints i hG hi hmax := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let pe := splitTorus.pointsEquiv I (Over.mk (𝟙 S))
  obtain ⟨t, ht⟩ := exists_eq_of_mem_centralizerPoints hG i hi hmax hz.mem_centralizerPoints
  have key : ∀ (c : J) (nc : normalizerPoints (T := splitTorus.commGroupScheme S I) i),
      Induces i (nc : Over.mk (𝟙 S) ⟶ G.X) (RootPairing.Equiv.reflection P c) →
      nc * z * nc⁻¹ * z ∈ torsionPoints i hG hi hmax →
      ∀ m, IsOfFinOrder (charValue (pe t) (P.reflection c m) * charValue (pe t) m) := by
    intro c nc hc hmem m
    obtain ⟨σ, hσ, hcc⟩ := hc
    obtain ⟨c', hc', hc'e⟩ := Subgroup.mem_map.mp hmem
    have hval := congrArg Subtype.val hc'e
    rw [torusHom_val] at hval
    have h2 : ((nc * z * nc⁻¹ * z : normalizerPoints (T := splitTorus.commGroupScheme S I) i) :
        Over.mk (𝟙 S) ⟶ G.X) =
        ((t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) * t) ≫ i.hom.hom := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ht, conj_torusPoint hσ, MonObj.mul_comp]
    rw [h2] at hval
    have hc'eq : c' = pe (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) * pe t := by
      have h3 := (cancel_mono i.hom.hom).1 hval
      rw [← map_mul, ← h3, MulEquiv.apply_symm_apply]
    let χ : (I → (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ) →* (Γ((Over.mk (𝟙 S)).left, ⊤))ˣ :=
      MonoidHom.mk' (fun x => charValue x m) fun x y => charValue_mul x y m
    have htor : IsOfFinOrder (charValue c' m) := χ.isOfFinOrder hc'
    rw [hc'eq, charValue_mul] at htor
    have h4 := hcc (Over.mk (𝟙 S)) t m
    change charValue (pe (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom)) m =
      charValue (pe t) (RootPairing.Equiv.reflection P c • m) at h4
    rw [h4, RootPairing.Equiv.reflection_smul] at htor
    exact htor
  have htj := isOfFinOrder_of_reflection_pair P hab (pe t) (key a na ha hza) (key b nb hb hzb)
  refine Subgroup.mem_map.mpr ⟨pe t, IsOfFinOrder.pi htj, Subtype.ext ?_⟩
  rw [torusHom_val, MulEquiv.symm_apply_apply, ht]

/-- **Finite lift of the Weyl group.** Let `i` be a closed split torus of a reductive group
`G`, maximal on every fibre, and let `P` be a finite reduced root datum on its coordinate
lattices. Let `n a` be points of `G(S)` inducing the reflections `s_a`, whose squares are
torus points `t` with `t² = 1`. Then some finite subgroup of the normalizer points contains,
for each element of the Weyl group of `P`, a point inducing it. -/
theorem exists_finite_subgroup_of_representatives [DecidableEq I] [Finite J] [P.IsReduced]
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) i)
    (n : J → (Over.mk (𝟙 S) ⟶ G.X))
    (hn : ∀ a, Induces i (n a) (RootPairing.Equiv.reflection P a))
    (hsq : ∀ a, ∃ t : Over.mk (𝟙 S) ⟶ (splitTorus S I).X,
      t * t = 1 ∧ n a * n a = t ≫ i.hom.hom) :
    ∃ H : Subgroup (Over.mk (𝟙 S) ⟶ G.X),
      H ≤ normalizerPoints (T := splitTorus.commGroupScheme S I) i ∧ Finite H ∧
        ∀ w ∈ P.weylGroup, ∃ m ∈ H, Induces i m w := by
  classical
  set N := normalizerPoints (T := splitTorus.commGroupScheme S I) i with hN
  set K := torsionPoints i hG hi hmax with hK
  have hKn : K.Normal := torsionPoints_normal hG hi hmax
  let n' : J → N := fun a => ⟨n a, by
    obtain ⟨σ, hσ, -⟩ := hn a
    exact (mem_normalizerPoints (T := splitTorus.commGroupScheme S I) i).2 ⟨σ, hσ⟩⟩
  have hsqK : ∀ a, n' a * n' a ∈ K := by
    intro a
    obtain ⟨t, ht, hnt⟩ := hsq a
    exact mem_torsionPoints_of_sq hG hi hmax _ t ht hnt
  obtain ⟨B, Mx, cs, hfin, hrel, hgen, hcw⟩ := exists_simple_coxeter P
  have hν2 : ∀ a : J, ((n' a : N ⧸ K)) * (n' a : N ⧸ K) = 1 := by
    intro a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hsqK a
  have hlift : ∀ a b : B, ((n' a : N ⧸ K) * (n' b : N ⧸ K)) ^ Mx a b = 1 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [Mx.diagonal, pow_one]
      exact hν2 a
    · have hzI : Induces i (P := P) (((n' a * n' b) ^ Mx a b : N) : Over.mk (𝟙 S) ⟶ G.X) 1 := by
        have h := ((hn a).mul (hn b)).pow (Mx a b)
        have h1 : (RootPairing.Equiv.reflection P b * RootPairing.Equiv.reflection P a) ^
            Mx a b = 1 := by
          rw [Mx.symmetric a b]
          exact hrel b a
        rw [h1] at h
        simpa only [Subgroup.coe_pow, Subgroup.coe_mul] using h
      have hcon := conj_pow_mul_eq_one (hν2 a) (hν2 b) (Mx a b)
      have hza : n' a * (n' a * n' b) ^ Mx a b * (n' a)⁻¹ * (n' a * n' b) ^ Mx a b ∈ K := by
        rw [← QuotientGroup.eq_one_iff]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
        exact hcon.1
      have hzb : n' b * (n' a * n' b) ^ Mx a b * (n' b)⁻¹ * (n' a * n' b) ^ Mx a b ∈ K := by
        rw [← QuotientGroup.eq_one_iff]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
        exact hcon.2
      have hzK := mem_torsionPoints_of_conj hG hi hmax (hcw a b hab) (na := n' a) (nb := n' b)
        (z := (n' a * n' b) ^ Mx a b) (hn a) (hn b) hzI hza hzb
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hzK
  let L := cs.lift ⟨fun b => (n' b : N ⧸ K), hlift⟩
  have := hfin
  let H₀ : Subgroup N := Subgroup.closure (Set.range fun b : B => n' b)
  have hfg : Group.FG H₀ := by
    rw [Group.fg_iff_subgroup_fg]
    exact ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  let f : H₀ →* N ⧸ K := (QuotientGroup.mk' K).comp H₀.subtype
  have hle : f.range ≤ L.range := by
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    change (h : N ⧸ K) ∈ L.range
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨cs.simple b, cs.lift_apply_simple hlift b⟩
    | one => exact L.range.one_mem
    | mul x y _ _ hx hy =>
      rw [QuotientGroup.mk_mul]
      exact L.range.mul_mem hx hy
    | inv x _ hx =>
      rw [QuotientGroup.mk_inv]
      exact L.range.inv_mem hx
  have : Finite L.range := Finite.of_surjective L.rangeRestrict L.rangeRestrict_surjective
  have : Finite f.range :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hker : ∀ g ∈ f.ker, ∃ x, IsOfFinOrder x ∧ torusHom i hG hi hmax x = (g : N) := by
    intro g hg
    have hgK : (g : N) ∈ K := (QuotientGroup.eq_one_iff _).1 hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgK
    exact ⟨x, hx, hxg⟩
  have hH₀ : Finite H₀ :=
    finite_of_ker_torsion f (torusHom i hG hi hmax) (torusHom_injective hG hi hmax) hker
  refine ⟨H₀.map N.subtype, Subgroup.map_subtype_le H₀, ?_, ?_⟩
  · refine Finite.of_surjective (fun h : H₀ => (⟨h.1.1, Subgroup.mem_map.mpr ⟨h.1, h.2, rfl⟩⟩ :
      H₀.map N.subtype)) ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · let Sg : Subgroup (RootPairing.Aut P) :=
      { carrier := {w | ∃ m ∈ H₀.map N.subtype, Induces i m w}
        mul_mem' := by
          rintro w w' ⟨m, hm, hw⟩ ⟨m', hm', hw'⟩
          exact ⟨m' * m, mul_mem hm' hm, hw'.mul hw⟩
        one_mem' := ⟨1, one_mem _, induces_one i P⟩
        inv_mem' := by
          rintro w ⟨m, hm, hw⟩
          exact ⟨m⁻¹, inv_mem hm, hw.inv⟩ }
    have hs : ∀ b : B, RootPairing.Equiv.reflection P b ∈ Sg := fun b =>
      ⟨n b, Subgroup.mem_map.mpr ⟨n' b, Subgroup.subset_closure ⟨b, rfl⟩, rfl⟩, hn b⟩
    have hcl : Subgroup.closure (Set.range fun b : B => RootPairing.Equiv.reflection P b) ≤ Sg :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨b, rfl⟩; exact hs b)
    have hW : P.weylGroup ≤ Sg :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨a, rfl⟩; exact hcl (hgen a))
    intro w hw
    exact hW hw

end Main

end Langlands.GroupScheme.AffineSplitNormalizerWeyl
