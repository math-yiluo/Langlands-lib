/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitHomology
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Mittag-Leffler towers have vanishing `lim¹`

For a tower `F` and a product `∏ Fₙ` with its transition endomorphism `t` (components
`∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`), the condition `lim¹ F = coker (1 - t) = 0` is that `1 - t` is an
epimorphism.

For towers of modules satisfying the Mittag-Leffler condition (the images of the transition
maps `Fₖ ⟶ Fₙ` stabilise), `1 - t` is surjective (Stacks 0598, 07KW). The proof first corrects a
family `a ∈ ∏ Fₙ`, modulo the image of `1 - t`, into the product of the stable images `Iₙ`,
using finite partial sums `yₙ = ∑_{n ≤ k < Mₙ} t_{k,n}(aₖ)`; the tower of the stable images has
surjective transitions, on which `1 - t` is surjective by the inductive construction of
`ModuleCat.epi_one_sub_of_epi`.

For towers in a preadditive category with a product `∏ Gₙ`:

- `CategoryTheory.Limits.epi_one_sub_of_essentiallyZero`: if `G` is essentially zero (for
  every `n` some transition `G m ⟶ G n` vanishes), `1 - t` is a split epimorphism, a section
  being the geometric series `∑ₖ tᵏ`, whose components are finite sums
  (`CategoryTheory.Limits.towerPartialSum`);
- `CategoryTheory.Limits.epi_one_sub_of_shortExact`: in an abelian category with exact
  countable products in which sequential limits of epimorphisms project epimorphically onto the
  first term (a replete topos), if `G` is an extension of an essentially zero tower by a tower
  with epimorphic transitions — the Mittag-Leffler condition — then `1 - t` is an
  epimorphism, i.e. `lim¹ G = 0`;
- `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler`: hence
  `Hⁱ(R lim F) = lim Hⁱ(Fₙ)` when the tower `H^{i-1}(Fₙ)` is Mittag-Leffler in this sense.

## Main results

- `ModuleCat.epi_one_sub_of_mittagLeffler`: Mittag-Leffler towers of modules have `R¹lim = 0`.
- `ModuleCat.mittagLeffler_of_isMittagLeffler`, `ModuleCat.mittagLeffler_of_finite`: the
  explicit Mittag-Leffler condition from `Functor.IsMittagLeffler`, and for finite modules.
- `ModuleCat.epi_one_sub_of_finite`: towers of finite modules have `R¹lim = 0`.
- `CategoryTheory.Limits.epi_one_sub_of_shortExact` and
  `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler`: the
  replete abelian case.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

/-- **Mittag-Leffler towers of modules have `R¹lim = 0`** (Stacks 0598, 07KW). Let `F` be a
tower of modules satisfying the Mittag-Leffler condition: for every `n` there is `N ≥ n` such
that the image of `F_N ⟶ Fₙ` is contained in the image of `Fₖ ⟶ Fₙ` for every `k ≥ n`. Then the
map `1 - t` on a product `∏ Fₙ` is surjective, where `t` has components `∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
lemma epi_one_sub_of_mittagLeffler {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hML : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range (F.map (homOfLE hN).op).hom ≤ LinearMap.range (F.map (homOfLE hk).op).hom) :
    Epi (𝟙 P.pt - t) := by
  classical
  let φ {m n : ℕ} (h : n ≤ m) : F.obj (op m) →ₗ[R] F.obj (op n) := (F.map (homOfLE h).op).hom
  have hφid (n : ℕ) (x : F.obj (op n)) : φ (le_refl n) x = x := by
    simp [φ]
  have hφcomp {k m n : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x : F.obj (op k)) :
      φ h₁ (φ h₂ x) = φ (h₁.trans h₂) x := by
    have : (homOfLE (h₁.trans h₂)).op = (homOfLE h₂).op ≫ (homOfLE h₁).op := Subsingleton.elim _ _
    simp [φ, this]
  choose N hN hNrange using hML
  -- the stable images and a monotone bound `M n ≥ max (N n) (n + 1)`
  let I (n : ℕ) : Submodule R (F.obj (op n)) := LinearMap.range (φ (hN n))
  let M : ℕ → ℕ := fun n ↦ Nat.rec (N 0 + 1) (fun n Mn ↦ max Mn (N (n + 1) + n + 2)) n
  have hMsucc (n : ℕ) : M n ≤ M (n + 1) := le_max_left _ _
  have hMN (n : ℕ) : N n < M n ∧ n < M n := by
    cases n with
    | zero => exact ⟨Nat.lt_succ_self _, Nat.succ_pos _⟩
    | succ n => exact ⟨lt_of_lt_of_le (by lia) (le_max_right _ _),
        lt_of_lt_of_le (by lia) (le_max_right _ _)⟩
  have hI (n k : ℕ) (hk : N n ≤ k) (x : F.obj (op k)) : φ ((hN n).trans hk) x ∈ I n :=
    ⟨φ hk x, hφcomp _ _ _⟩
  -- the transitions of the stable images are surjective
  have hIsurj (n : ℕ) (x : F.obj (op n)) (hx : x ∈ I n) :
      ∃ z : F.obj (op (n + 1)), z ∈ I (n + 1) ∧ φ n.le_succ z = x := by
    obtain ⟨w, hw⟩ := hNrange n (N (n + 1)) ((n.le_succ).trans (hN (n + 1))) hx
    exact ⟨φ (hN (n + 1)) w, ⟨w, rfl⟩, (hφcomp _ _ _).trans hw⟩
  rw [ModuleCat.epi_iff_surjective]
  intro a
  let ψ (k n : ℕ) : F.obj (op n) := if h : n ≤ k then φ h ((P.proj k).hom a) else 0
  have hψ (k n : ℕ) (h : n + 1 ≤ k) : φ n.le_succ (ψ k (n + 1)) = ψ k n := by
    simp only [ψ, dite_eq_left h, dite_eq_left (n.le_succ.trans h), hφcomp]
  let y (n : ℕ) : F.obj (op n) := ∑ k ∈ Finset.Ico n (M n), ψ k n
  -- the correction `b = a - (1 - t) y` lies in the stable images
  let b (n : ℕ) : F.obj (op n) := (P.proj n).hom a - y n + φ n.le_succ (y (n + 1))
  have hb (n : ℕ) : b n ∈ I n := by
    have h₁ : y n = ψ n n + ∑ k ∈ Finset.Ico (n + 1) (M n), ψ k n :=
      Finset.sum_eq_sum_Ico_succ_bot (hMN n).2 _
    have h₂ : φ n.le_succ (y (n + 1)) = ∑ k ∈ Finset.Ico (n + 1) (M n), ψ k n +
        ∑ k ∈ Finset.Ico (M n) (M (n + 1)), ψ k n := by
      rw [map_sum, Finset.sum_Ico_consecutive _ (hMN n).2 (hMsucc n)]
      exact Finset.sum_congr rfl fun k hk ↦ hψ k n (Finset.mem_Ico.1 hk).1
    have hψn : ψ n n = (P.proj n).hom a := by simp only [ψ, dite_eq_left le_rfl, hφid]
    have hb' : b n = ∑ k ∈ Finset.Ico (M n) (M (n + 1)), ψ k n := by
      simp only [b, h₁, h₂, hψn]
      abel
    rw [hb']
    refine Submodule.sum_mem _ fun k hk ↦ ?_
    have hk' : N n ≤ k := ((hMN n).1.le).trans (Finset.mem_Ico.1 hk).1
    simp only [ψ, dite_eq_left ((hN n).trans hk')]
    exact hI n k hk' _
  -- solve `x - t x = b` inside the stable images
  let x : ∀ n : ℕ, I n := fun n ↦ Nat.rec (motive := fun n ↦ I n) 0
    (fun n xn ↦ ⟨(hIsurj n _ (Submodule.sub_mem _ xn.2 (hb n))).choose,
      (hIsurj n _ (Submodule.sub_mem _ xn.2 (hb n))).choose_spec.1⟩) n
  have hx (n : ℕ) : φ n.le_succ (x (n + 1) : F.obj (op (n + 1))) = x n - b n :=
    (hIsurj n _ (Submodule.sub_mem _ (x n).2 (hb n))).choose_spec.2
  obtain ⟨z, hz⟩ := exists_proj_eq_of_isLimit_fan hP fun n ↦ y n + x n
  refine ⟨z, ext_of_isLimit_fan hP fun n ↦ ?_⟩
  have h₁ := congrArg (fun f ↦ f.hom z) (ht n)
  simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply] at h₁
  simp only [hom_sub, hom_id, LinearMap.sub_apply, LinearMap.id_apply, map_sub, h₁, hz]
  have := hx n
  simp only [φ] at this
  rw [map_add, this]
  simp only [b, φ]
  abel

/-- The Mittag-Leffler condition of Mathlib (`CategoryTheory.Functor.IsMittagLeffler`, for the
underlying tower of sets) for a tower of modules, in the explicit form used by
`ModuleCat.epi_one_sub_of_mittagLeffler`: for every `n` there is `N ≥ n` such that the image
of `F_N ⟶ Fₙ` is contained in the image of `Fₖ ⟶ Fₙ` for every `k ≥ n`. -/
lemma mittagLeffler_of_isMittagLeffler {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (h : (F ⋙ forget (ModuleCat.{u} R)).IsMittagLeffler) (n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range (F.map (homOfLE hN).op).hom ≤
        LinearMap.range (F.map (homOfLE hk).op).hom := by
  obtain ⟨i, g, hg⟩ := h (op n)
  have hg' : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
  refine ⟨i.unop, leOfHom g.unop, fun k hk ↦ ?_⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hg (homOfLE hk).op (⟨y, by rw [hg']⟩ : _ ∈ Set.range _)
  exact ⟨z, hz⟩

/-- **Towers of finite modules are Mittag-Leffler**, in the explicit form used by
`ModuleCat.epi_one_sub_of_mittagLeffler` (Stacks 0596). -/
lemma mittagLeffler_of_finite {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} (h : ∀ n : ℕ, Finite (F.obj (op n)))
    (n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range (F.map (homOfLE hN).op).hom ≤
        LinearMap.range (F.map (homOfLE hk).op).hom :=
  mittagLeffler_of_isMittagLeffler (Functor.isMittagLeffler_of_exists_finite_range (F ⋙ forget _)
    fun j ↦ ⟨j, 𝟙 j, @Set.finite_range _ _ _ (h j.unop)⟩) n

/-- **Towers of finite modules have `R¹lim = 0`** (Stacks 0596, 0598): for a tower `F` of
finite modules, the map `1 - t` on a product `∏ Fₙ` is surjective, where `t` has components
`∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
lemma epi_one_sub_of_finite {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (h : ∀ n : ℕ, Finite (F.obj (op n))) : Epi (𝟙 P.pt - t) :=
  epi_one_sub_of_mittagLeffler hP t ht (mittagLeffler_of_finite h)

end ModuleCat

open Category

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] {G : ℕᵒᵖ ⥤ C}
  {P : Fan fun n : ℕ ↦ G.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
  (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op)

/-- The partial sums `∑_{k < K} pₙ₊ₖ ≫ G(n + k ⟶ n)`. -/
noncomputable def towerPartialSum (n K : ℕ) : P.pt ⟶ G.obj (op n) :=
  ∑ k ∈ Finset.range K, P.proj (n + k) ≫ G.map (homOfLE (n.le_add_right k)).op


omit [Preadditive C] in
lemma proj_comp_map_congr {n a b : ℕ} (h : a = b) (hn : n ≤ a) :
    P.proj a ≫ G.map (homOfLE hn).op = P.proj b ≫ G.map (homOfLE (h ▸ hn)).op := by
  subst h
  rfl

lemma towerPartialSum_succ (n K : ℕ) :
    towerPartialSum (P := P) n (K + 1) =
      P.proj n + towerPartialSum (P := P) (n + 1) K ≫ G.map (homOfLE n.le_succ).op := by
  rw [towerPartialSum, Finset.sum_range_succ', towerPartialSum, Preadditive.sum_comp,
    add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [assoc, ← G.map_comp, ← op_comp, proj_comp_map_congr (P := P) (show n + (k + 1) = n + 1 + k
      by lia)]
    rfl
/-- If the tower is essentially zero beyond `m`, the partial sums stabilise. -/
lemma towerPartialSum_eq_of_le {n m : ℕ} (hnm : n ≤ m)
    (hm : G.map (homOfLE hnm).op = 0) {K K' : ℕ} (hK : m ≤ n + K) (hK' : K ≤ K') :
    towerPartialSum (P := P) n K' = towerPartialSum (P := P) n K := by
  rw [towerPartialSum, towerPartialSum, ← Finset.sum_range_add_sum_Ico _ hK',
    add_eq_left]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk' : m ≤ n + k := hK.trans (by have := (Finset.mem_Ico.1 hk).1; lia)
  have : homOfLE (n.le_add_right k) = homOfLE hnm ≫ homOfLE hk' := Subsingleton.elim _ _
  rw [this, op_comp, G.map_comp, hm, comp_zero, comp_zero]

include hP ht in
/-- **`lim¹` of an essentially zero tower vanishes**: if for every `n` some transition
`G m ⟶ G n` is zero, then `1 - t : ∏ Gₙ ⟶ ∏ Gₙ` is a split epimorphism, with section the
"geometric series" `∑ₖ tᵏ`, whose components are finite sums. -/
lemma epi_one_sub_of_essentiallyZero
    (hG : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G.map (homOfLE h).op = 0) : Epi (𝟙 P.pt - t) := by
  choose m hnm hm using hG
  let s : P.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ towerPartialSum (P := P) n (m n - n)
  have hs : s ≫ (𝟙 P.pt - t) = 𝟙 _ := by
    refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
    let K := max (m n - n) (m (n + 1) - (n + 1))
    rw [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, assoc, ht, Fan.IsLimit.fac,
      ← assoc, Fan.IsLimit.fac, id_comp,
      ← towerPartialSum_eq_of_le (hnm n) (hm n) (K' := K + 1) (by lia) (by lia),
      ← towerPartialSum_eq_of_le (hnm (n + 1)) (hm (n + 1)) (K' := K) (by lia) (by lia),
      towerPartialSum_succ, add_sub_cancel_right]
  exact (IsSplitEpi.mk' ⟨s, hs⟩).epi

include hP ht in
/-- `1 - t` is an epimorphism on one product of a tower as soon as it is on another. -/
lemma epi_one_sub_of_isLimit {Q : Fan fun n : ℕ ↦ G.obj (op n)} (hQ : IsLimit Q) (t' : Q.pt ⟶ Q.pt)
    (ht' : ∀ n : ℕ, t' ≫ Q.proj n = Q.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op)
    (h : Epi (𝟙 Q.pt - t')) : Epi (𝟙 P.pt - t) := by
  let e := hQ.conePointUniqueUpToIso hP
  have he (n : ℕ) : e.hom ≫ P.proj n = Q.proj n := hQ.conePointUniqueUpToIso_hom_comp hP ⟨n⟩
  have hc : e.hom ≫ (𝟙 P.pt - t) = (𝟙 Q.pt - t') ≫ e.hom :=
    Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, assoc, he, ht,
        ht', reassoc_of% he]
  have : Epi (e.hom ≫ (𝟙 P.pt - t)) := by rw [hc]; infer_instance
  exact epi_of_epi e.hom _

section Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]

/-- The transition endomorphism of the product `∏ Gₙ` of a tower. -/
noncomputable abbrev piTowerShift (G : ℕᵒᵖ ⥤ C) :
    ∏ᶜ (fun n : ℕ ↦ G.obj (op n)) ⟶ ∏ᶜ (fun n : ℕ ↦ G.obj (op n)) :=
  Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ G.map (homOfLE n.le_succ).op

/-- **`lim¹` vanishes for Mittag-Leffler towers in a replete abelian category.** Let
`0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0` be a pointwise short exact sequence of towers, where `G'` has
epimorphic transitions and `G''` is essentially zero (for instance `G'` the tower of stable
images of a Mittag-Leffler tower `G`). Then `1 - t` is an epimorphism on `∏ Gₙ`. -/
lemma epi_one_sub_of_shortExact (hC : EpiπAppZeroOfEpi C) {G' G G'' : ℕᵒᵖ ⥤ C}
    (ι : G' ⟶ G) (π : G ⟶ G'') (hιπ : ∀ n : ℕ, ι.app (op n) ≫ π.app (op n) = 0)
    (hS : ∀ n : ℕ, (ShortComplex.mk _ _ (hιπ n)).ShortExact)
    (h' : ∀ n : ℕ, Epi (G'.map (homOfLE n.le_succ).op))
    (h'' : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G''.map (homOfLE h).op = 0)
    {P : Fan fun n : ℕ ↦ G.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op) :
    Epi (𝟙 P.pt - t) := by
  -- the short exact sequence of products
  let SF : ShortComplex (Discrete ℕ ⥤ C) :=
    ShortComplex.mk
      (Discrete.natTrans (F := Discrete.functor fun n ↦ G'.obj (op n))
        (G := Discrete.functor fun n ↦ G.obj (op n)) fun n ↦ ι.app (op n.as))
      (Discrete.natTrans (F := Discrete.functor fun n ↦ G.obj (op n))
        (G := Discrete.functor fun n ↦ G''.obj (op n)) fun n ↦ π.app (op n.as))
      (by ext n; exact hιπ n.as)
  have hSF : SF.ShortExact := by
    have : ∀ n : Discrete ℕ, Mono (SF.f.app n) := fun n ↦ (hS n.as).mono_f
    have : ∀ n : Discrete ℕ, Epi (SF.g.app n) := fun n ↦ (hS n.as).epi_g
    refine ShortComplex.ShortExact.mk' ?_ (NatTrans.mono_of_mono_app _)
      (NatTrans.epi_of_epi_app _)
    rw [ShortComplex.exact_iff_evaluation]
    exact fun n ↦ (hS n.as).exact
  have hSP := hSF.map_of_exact (lim : (Discrete ℕ ⥤ C) ⥤ C)
  let ht₀ (H : ℕᵒᵖ ⥤ C) (n : ℕ) : piTowerShift H ≫ Pi.π _ n =
      Pi.π _ (n + 1) ≫ H.map (homOfLE n.le_succ).op := Pi.lift_comp_π _ _
  have e' : Epi (𝟙 _ - piTowerShift G') :=
    epi_one_sub_of_epiπAppZeroOfEpi hC h' (productIsProduct _) _ (ht₀ G')
  have e'' : Epi (𝟙 _ - piTowerShift G'') :=
    epi_one_sub_of_essentiallyZero (productIsProduct _) _ (ht₀ G'') h''
  let φ : SF.map lim ⟶ SF.map lim :=
    { τ₁ := 𝟙 _ - piTowerShift G'
      τ₂ := 𝟙 _ - piTowerShift G
      τ₃ := 𝟙 _ - piTowerShift G''
      comm₁₂ := by
        refine Pi.hom_ext _ _ fun n ↦ ?_
        change ((𝟙 _ - piTowerShift G') ≫ Pi.map fun n ↦ ι.app (op n)) ≫ Pi.π _ n =
          ((Pi.map fun n ↦ ι.app (op n)) ≫ (𝟙 _ - piTowerShift G)) ≫ Pi.π _ n
        simp only [assoc, Pi.map_π, Preadditive.sub_comp, Preadditive.comp_sub, id_comp,
          comp_id, Pi.lift_comp_π_assoc, Pi.lift_comp_π, Pi.map_π_assoc, NatTrans.naturality]
      comm₂₃ := by
        refine Pi.hom_ext _ _ fun n ↦ ?_
        change ((𝟙 _ - piTowerShift G) ≫ Pi.map fun n ↦ π.app (op n)) ≫ Pi.π _ n =
          ((Pi.map fun n ↦ π.app (op n)) ≫ (𝟙 _ - piTowerShift G'')) ≫ Pi.π _ n
        simp only [assoc, Pi.map_π, Preadditive.sub_comp, Preadditive.comp_sub, id_comp,
          comp_id, Pi.lift_comp_π_assoc, Pi.lift_comp_π, Pi.map_π_assoc, NatTrans.naturality] }
  have : Epi (SF.map lim).g := hSP.epi_g
  have : Epi φ.τ₁ := e'
  have : Epi φ.τ₃ := e''
  have : Epi (𝟙 _ - piTowerShift G) := ShortComplex.epi_τ₂_of_exact_of_epi φ hSP.exact
  exact epi_one_sub_of_isLimit hP t ht (productIsProduct _) _ (ht₀ G) this

end Abelian

end CategoryTheory.Limits

namespace DerivedCategory

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- **The Milnor sequence for Mittag-Leffler towers**: in an abelian category with exact
countable products in which sequential limits of epimorphisms project epimorphically onto the
first term, let `c` be a homotopy limit cone over a tower `F` in `D(C)` whose cohomology tower
`H^{i-1}(Fₙ)` is an extension of an essentially zero tower `G''` by a tower `G'` with
epimorphic transitions (the Mittag-Leffler condition, `G'` being the stable images). Then
`Hⁱ(R lim F) = lim Hⁱ(Fₙ)`. -/
noncomputable def isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler
    (hC : EpiπAppZeroOfEpi C) (hc : IsHomotopyLimit c) (i : ℤ) {G' G'' : ℕᵒᵖ ⥤ C}
    (ι : G' ⟶ F ⋙ homologyFunctor C (i - 1)) (π : F ⋙ homologyFunctor C (i - 1) ⟶ G'')
    (hιπ : ∀ n : ℕ, ι.app (op n) ≫ π.app (op n) = 0)
    (hS : ∀ n : ℕ, (ShortComplex.mk _ _ (hιπ n)).ShortExact)
    (h' : ∀ n : ℕ, Epi (G'.map (homOfLE n.le_succ).op))
    (h'' : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G''.map (homOfLE h).op = 0) :
    IsLimit ((homologyFunctor C i).mapCone c) :=
  have ht (n : ℕ) : piTowerShift (F ⋙ homologyFunctor C (i - 1)) ≫ Pi.π _ n =
      Pi.π _ (n + 1) ≫ (F ⋙ homologyFunctor C (i - 1)).map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  have := isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit hc (i - 1) i (by lia)
    (productIsProduct _) _ ht (epi_one_sub_of_shortExact hC ι π hιπ hS h' h''
      (productIsProduct _) _ ht)
    (limit.isLimit _)
  IsLimit.ofPointIso (limit.isLimit _)

end DerivedCategory
