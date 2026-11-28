import Langlands.Geometry.Building.DepthZero.GeneralLinear.Valuation
import Langlands.Geometry.Building.AffineRootSystem

/-!
# The apartment of the diagonal torus of `GL_N`

For apartment data `A` of the diagonal torus of `GL_N` over a nonarchimedean local field, with
the root values `c_{kl}(x)` of `Langlands.Geometry.Building.DepthZero.GeneralLinear.Valuation`:

* translating `x` by `v` adds `(e_k − e_l)(v)` to `c_{kl}` (`rootValue_vadd`), every coordinate
  change is realized by a translation (`exists_eval_coordCharacter`), and a point is determined
  by its root values (`eq_of_rootValue_eq`);
* the filtration groups are `U_{kl,x,r} = {1 + t E_{kl} | t = 0 or r ≤ ord t + c_{kl}(x)}`
  (`mem_filtration_iff`);
* the affine roots are the functions `y ↦ c_{kl}(y) + m`, `k ≠ l`, `m ∈ ℤ`
  (`exists_affineRoot_eq`, `affineRoot_apply_eq`);
* `x` is a vertex exactly when all `c_{kl}(x)` are integers (`isVertex_iff`), and `x` lies on no
  root hyperplane exactly when no `c_{kl}(x)`, `k ≠ l`, is an integer
  (`forall_affineRoot_ne_zero_iff`).

For `N ≥ 2` this is the affine root system of type `Ã_{N−1}` of `GL_N` (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, §15.1). For `N ≤ 1` the affine root set is empty.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable {F : Type u} [Field F] {N : ℕ}

/-- The coordinate character `e_k` of the diagonal split torus. -/
def coordCharacter (k : Fin N) : characterLattice (diagonalSplitTorus F N) :=
  (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))).symm (Pi.single ⟨k⟩ 1)

theorem rootCharacter_eq_sub (k l : Fin N) :
    rootCharacter (F := F) k l = coordCharacter k - coordCharacter l := by
  apply (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))).injective
  rw [map_sub, characterLatticeEquiv_rootCharacter, coordCharacter, coordCharacter,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem eval_rootCharacter (k l : Fin N) (w : V (diagonalSplitTorus F N)) :
    eval _ (rootCharacter (F := F) k l) w =
      eval _ (coordCharacter k) w - eval _ (coordCharacter l) w := by
  rw [rootCharacter_eq_sub, sub_eq_add_neg, eval_add_char, eval_neg_char, ← sub_eq_add_neg]

/-- Every family of real coordinates is realized by a vector of `V(S)`. -/
theorem exists_eval_coordCharacter (z : Fin N → ℝ) :
    ∃ w : V (diagonalSplitTorus F N), ∀ k, eval _ (coordCharacter (F := F) k) w = z k := by
  refine ⟨(∑ m, (z m : ℝ) ⊗ₜ[ℤ] ((splitTorus.cocharacterLatticeEquiv F (ULift.{u} (Fin N))).symm
    (Pi.single ⟨m⟩ 1) : cocharacterLattice (diagonalSplitTorus F N)) :
      V (diagonalSplitTorus F N)), fun k => ?_⟩
  rw [map_sum]
  simp only [eval_tmul, splitTorus.latticePairing_eq_sum, coordCharacter,
    AddEquiv.apply_symm_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single ⟨k⟩]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  · intro b _ hb
    have hb' : (⟨k⟩ : ULift.{u} (Fin N)) ≠ ⟨b⟩ := fun h => hb (congrArg ULift.down h).symm
    rw [Finset.sum_eq_zero]
    · simp
    · intro c _
      by_cases hc : c = ⟨k⟩
      · subst hc
        simp [Pi.single_eq_of_ne hb']
      · simp [Pi.single_eq_of_ne hc]
  · simp

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (A : KPApartmentData (diagTorus F N) (localFieldOrder F))

/-- The relative root `e_k − e_l`, as an element of the set of relative roots. -/
abbrev rootOf {k l : Fin N} (hkl : k ≠ l) : relativeRoots (diagTorus F N) :=
  ⟨rootCharacter k l, rootCharacter_mem_relativeRoots hkl⟩

/-- `c_{kl}(v + x) = c_{kl}(x) + (e_k − e_l)(v)`. -/
theorem rootValue_vadd (x : A.Apartment) (v : TranslationSpace (diagTorus F N)) {k l : Fin N}
    (hkl : k ≠ l) :
    rootValue A (v +ᵥ x) k l = rootValue A x k l + rootForm _ (rootOf (F := F) hkl) v := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have h := val_transvectionPoint_one A
    ((Submodule.Quotient.mk w : TranslationSpace (diagTorus F N)) +ᵥ x) hkl
  rw [KPApartmentData.val_mk_vadd w x,
    RootFunctionFamily.vadd_apply w x.val (rootCharacter k l) (transvectionPoint hkl (1 : F)),
    val_transvectionPoint_one A x hkl, ← WithTop.coe_add, WithTop.coe_inj] at h
  rw [rootForm_mk]
  exact h.symm

theorem rootValue_mk_vadd (x : A.Apartment) (w : V (diagonalSplitTorus F N)) (k l : Fin N) :
    rootValue A ((Submodule.Quotient.mk w : TranslationSpace (diagTorus F N)) +ᵥ x) k l =
      rootValue A x k l + (eval _ (coordCharacter (F := F) k) w -
        eval _ (coordCharacter (F := F) l) w) := by
  by_cases hkl : k = l
  · subst hkl
    simp [rootValue]
  rw [rootValue_vadd A x _ hkl, rootForm_mk, eval_rootCharacter]

/-- A point of the apartment is determined by its root values. -/
theorem eq_of_rootValue_eq {x x' : A.Apartment}
    (h : ∀ k l, rootValue A x k l = rootValue A x' k l) : x = x' := by
  rw [← vsub_vadd x' x]
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (x' -ᵥ x)
  suffices hw0 : (Submodule.Quotient.mk w : TranslationSpace (diagTorus F N)) = 0 by
    rw [← hw, hw0, zero_vadd]
  rw [Submodule.Quotient.mk_eq_zero, mem_rootAnnihilator]
  intro a ha
  obtain ⟨k, l, hkl, rfl⟩ := exists_eq_rootCharacter ha
  have h1 := rootValue_vadd A x (x' -ᵥ x) hkl
  rw [vsub_vadd, ← hw, rootForm_mk, ← h k l] at h1
  linarith

/-! ### Filtrations -/

/-- `U_{kl,x,r}` consists of the transvections `1 + t E_{kl}` with `t = 0` or
`r ≤ ord(t) + c_{kl}(x)`. -/
theorem mem_filtration_iff (x : A.Apartment) {k l : Fin N} (hkl : k ≠ l) (r : ℝ)
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ A.filtration x (rootCharacter k l) r ↔
      ∃ t : F, g = transvectionPoint hkl t ∧
        ∀ ht : t ≠ 0, r ≤ localFieldOrder F (Units.mk0 t ht) + rootValue A x k l := by
  have ha := rootCharacter_mem_relativeRoots (F := F) hkl
  rw [KPApartmentData.mem_filtration]
  constructor
  · rintro ⟨hg, hr⟩
    obtain ⟨t, ht⟩ := exists_eq_transvectionGL_of_mem_rootGroupPoints hkl hg
    have hgt : g = transvectionPoint hkl t := by
      rw [transvectionPoint, ← ht, MulEquiv.symm_apply_apply]
    refine ⟨t, hgt, fun ht0 => ?_⟩
    rw [hgt, val_transvectionPoint A x hkl ht0] at hr
    exact_mod_cast hr
  · rintro ⟨t, rfl, ht⟩
    refine ⟨transvectionPoint_mem_rootGroupPoints A hkl t, ?_⟩
    by_cases ht0 : t = 0
    · subst ht0
      rw [transvectionPoint_zero,
        (x.isValuation.eq_top_iff _ ha _ (Subgroup.one_mem _)).2 rfl]
      exact le_top
    · rw [val_transvectionPoint A x hkl ht0]
      exact_mod_cast ht ht0

/-! ### Affine roots -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem two_nsmul_rootCharacter_not_mem {k l : Fin N} (hkl : k ≠ l) :
    2 • rootCharacter (F := F) k l ∉ relativeRoots (diagTorus F N) := by
  intro h
  obtain ⟨p, q, -, heq⟩ := exists_eq_rootCharacter h
  have hc := congrArg (splitTorus.characterLatticeEquiv F (ULift.{u} (Fin N))) heq
  rw [map_nsmul, characterLatticeEquiv_rootCharacter, characterLatticeEquiv_rootCharacter] at hc
  have hk := congrFun hc ⟨k⟩
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, ULift.up_inj, hkl,
    ↓reduceIte] at hk
  simp only [nsmul_eq_mul, sub_zero] at hk
  split_ifs at hk <;> omega

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem doubleRootGroupPoints_rootCharacter {k l : Fin N} (hkl : k ≠ l) :
    doubleRootGroupPoints (diagTorus F N) (rootCharacter (F := F) k l) = ⊥ := by
  simp [doubleRootGroupPoints, two_nsmul_rootCharacter_not_mem hkl]

/-- The root value `c_{kl}` is the affine function on the apartment with derivative
`e_k − e_l` and value `c_{kl}(x₀)` at `x₀`. -/
theorem affineFunctional_apply_eq (x₀ y : A.Apartment) {k l : Fin N} (hkl : k ≠ l) (r : ℝ) :
    A.affineFunctional (rootOf (F := F) hkl) x₀ r y = rootValue A y k l - rootValue A x₀ k l + r := by
  rw [KPApartmentData.affineFunctional_apply]
  have h := rootValue_vadd A x₀ (y -ᵥ x₀) hkl
  rw [vsub_vadd] at h
  linarith

/-- For `k ≠ l` and `m ∈ ℤ`, the function `y ↦ c_{kl}(y) + m` is an affine root. -/
theorem exists_affineRoot_eq {k l : Fin N} (hkl : k ≠ l) (m : ℤ) :
    ∃ ψ ∈ A.affineRoots, ∀ y : A.Apartment, ψ y = rootValue A y k l + m := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty A.Apartment)
  set ψ := A.affineFunctional (rootOf (F := F) hkl) x₀ (rootValue A x₀ k l + m) with hψdef
  have hψ : ∀ y, ψ y = rootValue A y k l + m := fun y => by
    rw [hψdef, affineFunctional_apply_eq]
    ring
  refine ⟨ψ, ⟨rootOf hkl, KPApartmentData.affineFunctional_linear _ _ _, fun hsub => ?_⟩, hψ⟩
  let ϖ : Fˣ := SplitTorusValuation.uniformizerUnit F ^ m
  have hϖ : localFieldOrder F ϖ = m := by
    simp [ϖ, localFieldOrder, SplitTorusValuation.fieldOrderUnits_uniformizerUnit]
  have hmem : transvectionPoint hkl (ϖ : F) ∈ A.affineRootGroup (rootCharacter k l) ψ := by
    rw [KPApartmentData.mem_affineRootGroup_iff (α := rootOf hkl)
      (KPApartmentData.affineFunctional_linear _ _ _) x₀]
    refine ⟨transvectionPoint_mem_rootGroupPoints A hkl _, ?_⟩
    rw [val_transvectionPoint A x₀ hkl ϖ.ne_zero, hψ]
    rw [show Units.mk0 (ϖ : F) ϖ.ne_zero = ϖ by ext; rfl, hϖ]
    exact le_of_eq (congrArg _ (add_comm _ _))
  obtain ⟨v, hv, w, hw, hvw⟩ := hsub hmem
  rw [doubleRootGroupPoints_rootCharacter hkl] at hw
  have hw1 : w = 1 := hw
  have hvw' : v = transvectionPoint hkl (ϖ : F) := by simpa [hw1] using hvw
  rw [hvw'] at hv
  have hv1 := (KPApartmentData.mem_affineRootGroupPlus_iff (α := rootOf hkl) (ψ := ψ)
    (KPApartmentData.affineFunctional_linear _ _ _) x₀).1 hv
  rw [val_transvectionPoint A x₀ hkl ϖ.ne_zero, hψ,
    show Units.mk0 (ϖ : F) ϖ.ne_zero = ϖ by ext; rfl, hϖ] at hv1
  have hv2 := hv1.2
  norm_cast at hv2
  linarith

theorem localFieldOrder_eq_intCast (t : Fˣ) :
    localFieldOrder F t = ((Plancherel.fieldOrderUnits F t).toAdd : ℤ) :=
  rfl

/-- Every affine root is `y ↦ c_{kl}(y) + m` for some `k ≠ l` and `m ∈ ℤ`. -/
theorem affineRoot_apply_eq {ψ : A.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ A.affineRoots) :
    ∃ k l : Fin N, k ≠ l ∧ ∃ m : ℤ, ∀ y : A.Apartment, ψ y = rootValue A y k l + m := by
  obtain ⟨⟨a, ha⟩, hlin, hnot⟩ := hψ
  obtain ⟨k, l, hkl, rfl⟩ := exists_eq_rootCharacter ha
  obtain ⟨x₀⟩ := (inferInstance : Nonempty A.Apartment)
  set r := ψ x₀ - rootValue A x₀ k l
  have hval : ∀ y, ψ y = rootValue A y k l + r := by
    intro y
    have h1 : ψ y = ψ x₀ + rootForm _ (rootOf (F := F) hkl) (y -ᵥ x₀) := by
      have h0 := ψ.linear_apply_vsub y x₀
      rw [hlin, vsub_eq_sub] at h0
      change ψ y = ψ x₀ + rootForm (diagTorus F N) ⟨rootCharacter k l, ha⟩ (y -ᵥ x₀)
      rw [h0]
      ring
    have h2 := rootValue_vadd A x₀ (y -ᵥ x₀) hkl
    rw [vsub_vadd] at h2
    rw [h1, h2]
    ring
  refine ⟨k, l, hkl, ?_⟩
  by_contra hr
  push Not at hr
  apply hnot
  intro u hu0
  refine ⟨u, ?_, 1, Subgroup.one_mem _, mul_one u⟩
  have hu := (KPApartmentData.mem_affineRootGroup_iff (α := ⟨rootCharacter k l, ha⟩) hlin x₀).1 hu0
  show u ∈ A.affineRootGroupPlus _ ψ
  rw [KPApartmentData.mem_affineRootGroupPlus_iff (α := ⟨rootCharacter k l, ha⟩) hlin x₀]
  refine ⟨hu.1, ?_⟩
  obtain ⟨t, ht⟩ := exists_eq_transvectionGL_of_mem_rootGroupPoints hkl hu.1
  have hut : u = transvectionPoint hkl t := by
    rw [transvectionPoint, ← ht, MulEquiv.symm_apply_apply]
  by_cases ht0 : t = 0
  · subst ht0
    have hu1 : u = 1 := by rw [hut, transvectionPoint_zero]
    rw [hu1, (x₀.isValuation.eq_top_iff _ ha _ (Subgroup.one_mem _)).2 rfl]
    exact WithTop.coe_lt_top _
  · have h2 := hu.2
    rw [hut, val_transvectionPoint A x₀ hkl ht0, hval] at h2 ⊢
    norm_cast at h2 ⊢
    have hne : r ≠ localFieldOrder F (Units.mk0 t ht0) := by
      intro h
      obtain ⟨y, hy⟩ := hr (Plancherel.fieldOrderUnits F (Units.mk0 t ht0)).toAdd
      apply hy
      rw [hval y, h, localFieldOrder_eq_intCast]
    have hle : r ≤ localFieldOrder F (Units.mk0 t ht0) := by linarith
    have := lt_of_le_of_ne hle hne
    linarith

/-! ### Vertices and chambers -/

/-- `x` lies on no root hyperplane exactly when no `c_{kl}(x)` with `k ≠ l` is an integer. -/
theorem forall_affineRoot_ne_zero_iff (x : A.Apartment) :
    (∀ ψ ∈ A.affineRoots, ψ x ≠ 0) ↔
      ∀ k l : Fin N, k ≠ l → ∀ m : ℤ, rootValue A x k l ≠ m := by
  constructor
  · intro h k l hkl m hm
    obtain ⟨ψ, hψ, hψv⟩ := exists_affineRoot_eq A hkl (-m)
    apply h ψ hψ
    rw [hψv, hm]
    push_cast
    ring
  · intro h ψ hψ hψx
    obtain ⟨k, l, hkl, m, hm⟩ := affineRoot_apply_eq A hψ
    apply h k l hkl (-m)
    rw [hm] at hψx
    push_cast
    linarith

/-- For real `a` and integer `m`, `|a + m|` is at least the distance from `a` to `ℤ`. -/
theorem min_fract_le_abs_add_intCast (a : ℝ) (m : ℤ) :
    min (Int.fract a) (1 - Int.fract a) ≤ |a + m| := by
  have ha : a + m = ((⌊a⌋ + m : ℤ) : ℝ) + Int.fract a := by
    rw [Int.fract]
    push_cast
    ring
  rw [ha]
  have h0 := Int.fract_nonneg a
  have h1 := Int.fract_lt_one a
  rcases le_or_gt 0 (⌊a⌋ + m) with hn | hn
  · have hn' : (0 : ℝ) ≤ ((⌊a⌋ + m : ℤ) : ℝ) := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have hn' : ((⌊a⌋ + m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show ⌊a⌋ + m ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

theorem sign_add_eq_of_abs_lt {a d : ℝ} (h : |d| < |a|) :
    SignType.sign (a + d) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at h
    have : a + d < 0 := by linarith [le_abs_self d]
    rw [sign_neg this, sign_neg ha]
  · subst ha
    simp at h
    exact absurd h (not_lt.2 (abs_nonneg d))
  · rw [abs_of_pos ha] at h
    have : 0 < a + d := by linarith [neg_abs_le d]
    rw [sign_pos this, sign_pos ha]

/-- **Vertices of the apartment.** `x` is a vertex exactly when all root values `c_{kl}(x)`
are integers. -/
theorem isVertex_iff (x : A.Apartment) :
    AffineRootSystem.IsVertex A.affineRoots x ↔ ∀ k l : Fin N, ∃ m : ℤ, rootValue A x k l = m := by
  constructor
  · intro hx
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, l₀, hkl₀⟩ := hcon
    have hk₀l₀ : k₀ ≠ l₀ := by
      rintro rfl
      exact hkl₀ 0 (by simp [rootValue])
    obtain ⟨y, hy⟩ := exists_rootValue_eq_sub A x
    let C : Finset (Fin N) := Finset.univ.filter fun m => Int.fract (y m) = Int.fract (y k₀)
    have hk₀C : k₀ ∈ C := by simp [C]
    have hnotint : ∀ p q, p ∈ C → q ∉ C → ∀ z : ℤ, y p - y q ≠ z := by
      intro p q hp hq z hz
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      apply hq
      rw [← hp]
      exact (Int.fract_eq_fract.2 ⟨z, hz⟩).symm
    have hl₀C : l₀ ∉ C := by
      intro hl
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 hl.symm
      exact hkl₀ z (by rw [hy]; exact hz)
    let d : Fin N × Fin N → ℝ := fun pq =>
      min (Int.fract (y pq.1 - y pq.2)) (1 - Int.fract (y pq.1 - y pq.2))
    let S : Finset (Fin N × Fin N) := Finset.univ.filter fun pq => pq.1 ∈ C ∧ pq.2 ∉ C
    have hS : S.Nonempty := ⟨(k₀, l₀), by simp [S, hk₀C, hl₀C]⟩
    have hdpos : ∀ pq ∈ S, 0 < d pq := by
      intro pq hpq
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hpq
      have hne : Int.fract (y pq.1 - y pq.2) ≠ 0 := by
        intro h0
        rw [Int.fract_eq_iff] at h0
        obtain ⟨-, -, z, hz⟩ := h0
        exact hnotint pq.1 pq.2 hpq.1 hpq.2 z (by linarith)
      have h0 := Int.fract_nonneg (y pq.1 - y pq.2)
      have h1 := Int.fract_lt_one (y pq.1 - y pq.2)
      exact lt_min (lt_of_le_of_ne h0 (Ne.symm hne)) (by linarith)
    set δ := S.inf' hS d
    have hδ : 0 < δ := (Finset.lt_inf'_iff hS).2 hdpos
    have hδle : ∀ p q, p ∈ C → q ∉ C → δ ≤ d (p, q) := fun p q hp hq =>
      Finset.inf'_le _ (by simp [S, hp, hq])
    obtain ⟨w, hw⟩ := exists_eval_coordCharacter (F := F)
      (fun m => if m ∈ C then δ / 2 else 0)
    set x' := (Submodule.Quotient.mk w : TranslationSpace (diagTorus F N)) +ᵥ x
    have hx' : x' ∈ AffineRootSystem.facet A.affineRoots x := by
      intro ψ hψ
      obtain ⟨p, q, hpq, m, hm⟩ := affineRoot_apply_eq A hψ
      rw [hm, hm, rootValue_mk_vadd, hw, hw, hy]
      by_cases hp : p ∈ C <;> by_cases hq : q ∈ C
      · simp [hp, hq]
      · simp only [hp, hq, ↓reduceIte, sub_zero]
        symm
        rw [show y p - y q + (δ / 2) + (m : ℝ) = (y p - y q + m) + δ / 2 by ring]
        apply sign_add_eq_of_abs_lt
        have h1 := min_fract_le_abs_add_intCast (y p - y q) m
        have h2 := hδle p q hp hq
        rw [abs_of_pos (by linarith)]
        exact lt_of_lt_of_le (by linarith) (h2.trans h1)
      · simp only [hp, hq, ↓reduceIte, zero_sub]
        symm
        rw [show y p - y q + -(δ / 2) + (m : ℝ) = (y p - y q + m) + -(δ / 2) by ring]
        apply sign_add_eq_of_abs_lt
        have h1 := min_fract_le_abs_add_intCast (y q - y p) (-m)
        have h2 := hδle q p hq hp
        rw [show |y p - y q + (m : ℝ)| = |y q - y p + ((-m : ℤ) : ℝ)| by
          rw [← abs_neg]; push_cast; ring_nf]
        rw [abs_neg, abs_of_pos (by linarith)]
        exact lt_of_lt_of_le (by linarith) (h2.trans h1)
      · simp [hp, hq]
    rw [hx] at hx'
    have hxx : x' = x := hx'
    have h1 := rootValue_mk_vadd A x w k₀ l₀
    rw [show (Submodule.Quotient.mk w : TranslationSpace (diagTorus F N)) +ᵥ x = x from hxx,
      hw, hw] at h1
    simp only [hk₀C, hl₀C, ↓reduceIte, sub_zero] at h1
    linarith
  · intro hint
    ext x'
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hx'
      apply eq_of_rootValue_eq A
      intro k l
      by_cases hkl : k = l
      · subst hkl
        simp [rootValue]
      obtain ⟨m, hm⟩ := hint k l
      obtain ⟨ψ, hψ, hψv⟩ := exists_affineRoot_eq A hkl (-m)
      have hs := hx' ψ hψ
      rw [hψv, hψv, hm] at hs
      push_cast at hs
      rw [show (m : ℝ) + -m = 0 by ring, sign_zero, eq_comm, sign_eq_zero_iff] at hs
      linarith
    · rintro rfl
      exact AffineRootSystem.mem_facet_self _ _

end Langlands.Geometry.Building.GeneralLinearParahoric
