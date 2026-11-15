import Langlands.GroupScheme.Reductive.LocalSplitCommutatorPolynomials
import Langlands.GroupScheme.SplitExistence.IntegralBase

/-! # Commutators of two root groups for an arbitrary pair of non-opposite roots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LinearAlgebra

open Set Submodule Module IsAddIndecomposable
open Langlands.GroupScheme.SplitExistence

variable {J X Y : Type*} [Finite J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y)

/-- An integral functional positive on the simple roots of a base detects exactly its positive
roots. -/
theorem isPos_iff_of_pos_simple (b : P.Base) (f : Dual ℤ X)
    (hf : ∀ i ∈ b.support, 0 < f (P.root i)) (i : J) :
    b.IsPos i ↔ 0 < f (P.root i) := by
  have hforward (j : J) (hj : b.IsPos j) : 0 < f (P.root j) := by
    apply hj.induction_on_add
    · exact hf
    · intro a c z hz ha hc
      rw [hz, map_add]
      exact add_pos ha (hf c hc)
  constructor
  · exact hforward i
  · intro hi
    let := P.indexNeg
    rcases RootPairing.Base.IsPos.or_neg b i with hp | hn
    · exact hp
    · have hneg := hforward (-i) hn
      have heq : P.root (-i) = -P.root i := by simp
      rw [heq, map_neg] at hneg
      omega

/-- A regular integral functional on the coroots has a base whose positive roots are exactly
the roots whose coroots it takes to positive values. -/
theorem exists_base_isPos_iff [P.IsReduced] (g : Dual ℤ Y) (hg : ∀ i, g (P.coroot i) ≠ 0) :
    ∃ b : P.Base, ∀ i, b.IsPos i ↔ 0 < g (P.coroot i) := by
  have := Fintype.ofFinite J
  let f : Dual ℤ X := g ∘ₗ P.Polarization
  have hf : ∀ i, f (P.root i) ≠ 0 := dual_polarization_root_ne_zero P hg
  have hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i) := dual_polarization_root_pos_iff P g
  have heq := baseOf_root_eq_baseOf_coroot P f g hf hg hfg
  let := P.indexNeg
  let b : P.Base :=
    { support := (toFinite (baseOf P.root (f : X →+ ℤ))).toFinset
      linearIndepOn_root := by
        simpa using RootPairing.linearIndepOn_root_baseOf' P (S := ℤ) f hf
      linearIndepOn_coroot := by
        simpa [heq] using RootPairing.linearIndepOn_root_baseOf' P.flip (S := ℤ) g hg
      root_mem_or_neg_mem := fun i => by
        simpa using mem_or_neg_mem_closure_baseOf P.root (f : X →+ ℤ) i (hf i) (by simp)
      coroot_mem_or_neg_mem := fun i => by
        simpa [heq] using
          mem_or_neg_mem_closure_baseOf P.coroot (g : Y →+ ℤ) i (hg i) (by simp) }
  have hsimple : ∀ i ∈ b.support, 0 < f (P.root i) := by
    intro i hi
    have hi' : i ∈ baseOf P.root (f : X →+ ℤ) := by simpa [b] using hi
    exact hi'.1
  exact ⟨b, fun i => (isPos_iff_of_pos_simple P b f hsimple i).trans (hfg i)⟩

/-- A functional on the coroots can be perturbed to a regular one that stays positive wherever
the original one is positive. -/
theorem exists_regular_of_pos (g : Dual ℤ Y) :
    ∃ q : Dual ℤ Y, (∀ i, q (P.coroot i) ≠ 0) ∧
      ∀ i, 0 < g (P.coroot i) → 0 < q (P.coroot i) := by
  classical
  have := Fintype.ofFinite J
  obtain ⟨q, hq⟩ := exists_dual_coroot_ne_zero P
  let n : ℤ := ∑ i, |q (P.coroot i)| + 1
  have hbound (i : J) : |q (P.coroot i)| < n := by
    have := Finset.single_le_sum (f := fun j => |q (P.coroot j)|)
      (fun j _ => abs_nonneg (q (P.coroot j))) (Finset.mem_univ i)
    dsimp [n]
    omega
  refine ⟨n • g + q, ?_, ?_⟩
  · intro i hi
    have hi' : n * g (P.coroot i) + q (P.coroot i) = 0 := by simpa [smul_eq_mul] using hi
    have hb := hbound i
    have hlo := neg_abs_le (q (P.coroot i))
    have hhi := le_abs_self (q (P.coroot i))
    rcases lt_trichotomy (g (P.coroot i)) 0 with hneg | hzero | hpos
    · have : g (P.coroot i) ≤ -1 := by omega
      nlinarith
    · exact hq i (by simpa [hzero] using hi')
    · have : 1 ≤ g (P.coroot i) := by omega
      nlinarith
  · intro i hi
    have hb := hbound i
    have hlo := neg_abs_le (q (P.coroot i))
    have h1 : 1 ≤ g (P.coroot i) := by omega
    have hn : 0 ≤ n := le_trans (abs_nonneg _) hb.le
    have hng : n ≤ n * g (P.coroot i) := le_mul_of_one_le_right hn h1
    have : 0 < n * g (P.coroot i) + q (P.coroot i) := by linarith
    simpa [smul_eq_mul] using this

/-- A base making positive every root whose coroot has positive value under a given
functional. -/
theorem exists_base_isPos_of_pos [P.IsReduced] (g : Dual ℤ Y) :
    ∃ b : P.Base, ∀ i, 0 < g (P.coroot i) → b.IsPos i := by
  obtain ⟨q, hq, hpos⟩ := exists_regular_of_pos P g
  obtain ⟨b, hb⟩ := exists_base_isPos_iff P q hq
  exact ⟨b, fun i hi => (hb i).mpr (hpos i hi)⟩

/-- **A base containing two given roots among its positive roots**, for two roots that are not
opposite. -/
theorem exists_base_isPos_pair [P.IsReduced] [Module.IsTorsionFree ℤ X] {i j : J} (hneg : P.root i ≠ -P.root j) :
    ∃ b : P.Base, b.IsPos i ∧ b.IsPos j := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨b, hb⟩ := exists_base_isPos_of_pos P (P.toLinearMap (P.root i))
    have h : 0 < P.toLinearMap (P.root i) (P.coroot i) := by
      rw [RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
      norm_num
    exact ⟨b, hb i h, hb i h⟩
  · have h4 : P.coxeterWeightIn ℤ i j < 4 :=
      lt_of_le_of_ne (P.coxeterWeightIn_le_four ℤ i j) (P.coxeterWeightIn_ne_four (S := ℤ) hij hneg)
    have e := P.algebraMap_coxeterWeightIn ℤ i j
    rw [Algebra.algebraMap_self, RingHom.id_apply, RootPairing.coxeterWeight] at e
    rw [e] at h4
    let g : Dual ℤ Y := (2 - P.pairing j i) • P.toLinearMap (P.root i) +
      (2 - P.pairing i j) • P.toLinearMap (P.root j)
    have hgi : g (P.coroot i) = 4 - P.pairing i j * P.pairing j i := by
      simp only [g, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
      ring
    have hgj : g (P.coroot j) = 4 - P.pairing i j * P.pairing j i := by
      simp only [g, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
      ring
    obtain ⟨b, hb⟩ := exists_base_isPos_of_pos P g
    exact ⟨b, hb i (by rw [hgi]; linarith), hb j (by rw [hgj]; linarith)⟩

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Single

variable {R : Type u} [CommRing R] {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}

/-- An ordered product whose coordinates vanish away from one position is the factor at that
position. -/
theorem orderedProduct_eq_rootPoint_of_eq_zero (u : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin n → Γ(Z.left, ⊤)) (k : Fin n)
    (hc : ∀ l, l ≠ k → c l = 0) :
    orderedProduct u pos Z c = rootPoint (u (pos k)) Z (c k) := by
  unfold orderedProduct
  rw [prod_ofFn_split _ k]
  have h1 : (List.ofFn fun l => if l < k then rootPoint (u (pos l)) Z (c l) else 1) =
      List.ofFn fun _ : Fin n => (1 : Z ⟶ G.X) := by
    congr 1
    funext l
    split_ifs with hl
    · rw [hc l (ne_of_lt hl), rootPoint_zero]
    · rfl
  have h2 : (List.ofFn fun l => if k < l then rootPoint (u (pos l)) Z (c l) else 1) =
      List.ofFn fun _ : Fin n => (1 : Z ⟶ G.X) := by
    congr 1
    funext l
    split_ifs with hl
    · rw [hc l (ne_of_gt hl), rootPoint_zero]
    · rfl
  rw [h1, h2, prod_ofFn_one, one_mul, mul_one]

/-- An ordered product whose coordinates vanish away from two positions `k₁ < k₂` is the
product of the two factors at those positions. -/
theorem orderedProduct_eq_rootPoint_mul_of_eq_zero (u : J → (Ga R ⟶ G)) {n : ℕ}
    (pos : Fin n → J) (Z : Over (Spec (CommRingCat.of R))) (c : Fin n → Γ(Z.left, ⊤))
    {k₁ k₂ : Fin n} (hk : k₁ < k₂) (hc : ∀ l, l ≠ k₁ → l ≠ k₂ → c l = 0) :
    orderedProduct u pos Z c =
      rootPoint (u (pos k₁)) Z (c k₁) * rootPoint (u (pos k₂)) Z (c k₂) := by
  unfold orderedProduct
  rw [prod_ofFn_split _ k₂]
  have h2 : (List.ofFn fun l => if k₂ < l then rootPoint (u (pos l)) Z (c l) else 1) =
      List.ofFn fun _ : Fin n => (1 : Z ⟶ G.X) := by
    congr 1
    funext l
    split_ifs with hl
    · rw [hc l (ne_of_gt (hk.trans hl)) (ne_of_gt hl), rootPoint_zero]
    · rfl
  rw [h2, prod_ofFn_one, mul_one, prod_ofFn_split _ k₁]
  have h3 : (List.ofFn fun l => if l < k₁ then
      (if l < k₂ then rootPoint (u (pos l)) Z (c l) else 1) else 1) =
      List.ofFn fun _ : Fin n => (1 : Z ⟶ G.X) := by
    congr 1
    funext l
    split_ifs with hl hl'
    · rw [hc l (ne_of_lt hl) (ne_of_lt (hl.trans hk)), rootPoint_zero]
    · rfl
    · rfl
  have h4 : (List.ofFn fun l => if k₁ < l then
      (if l < k₂ then rootPoint (u (pos l)) Z (c l) else 1) else 1) =
      List.ofFn fun _ : Fin n => (1 : Z ⟶ G.X) := by
    congr 1
    funext l
    split_ifs with hl hl'
    · rw [hc l (ne_of_gt hl) (ne_of_lt hl'), rootPoint_zero]
    · rfl
    · rfl
  rw [h3, h4]
  simp only [prod_ofFn_one, one_mul, mul_one, hk, ↓reduceIte]

end Single

section Pairs

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {v : J → (Ga R ⟶ G)}

/-- **Cell data for an arbitrary base.** For a family of root parametrizations of all roots and
any base `b`, enumerations of the non-positive and positive roots of `b` give an open big cell,
and some cocharacter separates the two kinds of roots. -/
theorem exists_cell_of_base (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (b : P.Base) :
    ∃ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
      IsOpenImmersion (cellMap i v (fun k => (neg k : J)) (fun k => (pos k : J))).left ∧
      ∃ ν : I → ℤ, (∀ k, coPairing (P.root (neg k : J)) ν < 0) ∧
        (∀ k, 0 < coPairing (P.root (pos k : J)) ν) := by
  have := hP.finite
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  refine ⟨_, _, neg, pos, LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b v hv neg pos,
    ?_⟩
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  refine ⟨ν, fun k => ?_, fun k => ?_⟩
  · rw [hν]
    have h0 := b.height_ne_zero (neg k : J)
    have h1 := (neg k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd (by omega)
  · rw [hν]
    exact mul_pos hd (pos k).2

/-- **Commuting root groups.** Let `β` and `ε` be roots that are not opposite, and suppose that
no `dS • β + dT • ε` with `dS, dT ≥ 1` is a root. Then the root groups of `β` and `ε` commute
over every ring over `R`. -/
theorem rootPoint_commute_of_forall_ne (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {β ε : J} (hβε : P.root β ≠ -P.root ε)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε ≠ P.root α)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)) :
    rootPoint (v β) (Over.mk s) x * rootPoint (v ε) (Over.mk s) y =
      rootPoint (v ε) (Over.mk s) y * rootPoint (v β) (Over.mk s) x := by
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b, hβ, hε⟩ := Langlands.LinearAlgebra.exists_base_isPos_pair P hβε
  obtain ⟨m, n, neg, pos, hopen, ν, hneg, hpos⟩ := exists_cell_of_base hG hmax hP hv b
  have := hopen
  have hTE : TorusEquivariant i (fun α => P.root α) v := fun α Z t c => (hv α).equivariant Z t c
  have hk : ((pos (pos.symm ⟨β, hβ⟩) : {α // b.IsPos α}) : J) = β := by simp
  have hl : ((pos (pos.symm ⟨ε, hε⟩) : {α // b.IsPos α}) : J) = ε := by simp
  have h := posComm_eq_one_of_forall_ne (i := i) (neg := fun k => (neg k : J)) hTE ν hneg hpos
    (k := pos.symm ⟨β, hβ⟩) (l := pos.symm ⟨ε, hε⟩)
    (fun p dS dT h1 h2 => by
      simp only [hk, hl]
      exact hcone _ dS dT h1 h2) s x y
  simp only [posComm, hk, hl] at h
  exact inv_mul_eq_one.mp h

/-- **A single root in the cone.** Let `β` and `ε` be roots that are not opposite, with
`β + ε = δ` a root, and suppose that `dS • β + dT • ε` with `dS, dT ≥ 1` is a root only for
`dS = dT = 1`. Then there is `C ∈ R` such that over every ring `B` over `R` and for all
`x, y ∈ B`, `(u_β(x) u_ε(y))⁻¹ (u_ε(y) u_β(x)) = u_δ(C x y)`, where `C` is mapped to `B`. -/
theorem exists_rootPoint_comm_single (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {β ε δ : J} (hβε : P.root β ≠ -P.root ε) (hδ : P.root δ = P.root β + P.root ε)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε = P.root α → dS = 1 ∧ dT = 1) :
    ∃ C : R, ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v δ) (Over.mk s)
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Spec.preimage s).hom C * x * y)) := by
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b, hβ, hε⟩ := Langlands.LinearAlgebra.exists_base_isPos_pair P hβε
  have hδpos : b.IsPos δ := hβ.add hε hδ
  obtain ⟨m, n, neg, pos, hopen, ν, hneg, hpos⟩ := exists_cell_of_base hG hmax hP hv b
  have := hopen
  have hTE : TorusEquivariant i (fun α => P.root α) v := fun α Z t c => (hv α).equivariant Z t c
  set k := pos.symm ⟨β, hβ⟩ with hkdef
  set l := pos.symm ⟨ε, hε⟩ with hldef
  set q₀ := pos.symm ⟨δ, hδpos⟩ with hq₀def
  have hk : ((pos k : {α // b.IsPos α}) : J) = β := by simp [k]
  have hl : ((pos l : {α // b.IsPos α}) : J) = ε := by simp [l]
  have hq₀ : ((pos q₀ : {α // b.IsPos α}) : J) = δ := by simp [q₀]
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := fun k => (neg k : J)) hTE ν hneg hpos k l
  -- the coordinates away from `δ` vanish
  have hzero : ∀ q, q ≠ q₀ → E q = 0 := by
    intro q hq
    refine hE.eq_zero_of_forall_ne (i := i) (neg := fun k => (neg k : J)) hTE q ?_
    intro dS dT h1 h2 heq
    simp only [hk, hl] at heq
    obtain ⟨rfl, rfl⟩ := hcone _ dS dT h1 h2 heq
    apply hq
    apply pos.injective
    apply Subtype.ext
    apply P.root.injective
    rw [hq₀, hδ, ← heq]
    simp
  -- the coordinate at `δ` is a multiple of `S T`
  let C : R := ((E q₀).coeff 1).coeff 1
  have hEq₀ : E q₀ = Polynomial.monomial 1 (Polynomial.monomial 1 C) := by
    ext dT dS
    rw [Polynomial.coeff_monomial, apply_ite (fun p : Polynomial R => p.coeff dS),
      Polynomial.coeff_monomial, Polynomial.coeff_zero]
    by_cases hnz : ((E q₀).coeff dT).coeff dS = 0
    · rw [hnz]
      split_ifs with h1 h2
      · subst h1; subst h2; exact hnz.symm.trans rfl
      · rfl
      · rfl
    · obtain ⟨h1, h2⟩ := hE.one_le (i := i) (neg := fun k => (neg k : J)) q₀ hnz
      have hw := hE.weight (neg := fun k => (neg k : J)) hTE q₀ hnz
      simp only [hk, hl, hq₀] at hw
      obtain ⟨rfl, rfl⟩ := hcone δ dS dT h1 h2 hw
      simp [C]
  refine ⟨C, fun B _ s x y => ?_⟩
  have h := hE.posComm_eq s x y
  simp only [posComm, hk, hl] at h
  rw [h, orderedProduct_eq_rootPoint_of_eq_zero v _ _ _ q₀ (fun q hq => by
    rw [hzero q hq, map_zero, map_zero]), hq₀, hEq₀]
  congr 2
  simp [lineEval, Polynomial.eval₂_monomial]

/-- **Two roots in the cone.** Let `β` and `ε` be roots that are not opposite, with roots
`δ₁ = β + ε` and `δ₂ = 2 β + ε` whose root groups commute. Suppose that `dS • β + dT • ε`
with `dS, dT ≥ 1` is a root only for `(dS, dT) = (1, 1)` or `(2, 1)`. Then there are
`C₁, C₂ ∈ R` with `(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = v_{δ₁}(C₁ x y) v_{δ₂}(C₂ x² y)` over
every ring over `R`. -/
theorem exists_rootPoint_comm_two (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {β ε δ₁ δ₂ : J} (hβε : P.root β ≠ -P.root ε) (hδ₁ : P.root δ₁ = P.root β + P.root ε)
    (hδ₂ : P.root δ₂ = (2 : ℤ) • P.root β + P.root ε)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε = P.root α →
        (dS = 1 ∧ dT = 1) ∨ (dS = 2 ∧ dT = 1))
    (hcomm : ∀ {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : Γ((Over.mk s).left, ⊤)),
      rootPoint (v δ₁) (Over.mk s) x * rootPoint (v δ₂) (Over.mk s) y =
        rootPoint (v δ₂) (Over.mk s) y * rootPoint (v δ₁) (Over.mk s) x) :
    ∃ C₁ C₂ : R, ∀ (B : Type u) [CommRing B]
      (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B),
      (rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v δ₁) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Spec.preimage s).hom C₁ * x * y)) *
        rootPoint (v δ₂) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Spec.preimage s).hom C₂ * x ^ 2 * y)) := by
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b, hβ, hε⟩ := Langlands.LinearAlgebra.exists_base_isPos_pair P hβε
  have hδ₁pos : b.IsPos δ₁ := hβ.add hε hδ₁
  obtain ⟨m, n, neg, pos, hopen, ν, hneg, hpos⟩ := exists_cell_of_base hG hmax hP hv b
  have := hopen
  have hTE : TorusEquivariant i (fun α => P.root α) v := fun α Z t c => (hv α).equivariant Z t c
  have hδ₂pos : b.IsPos δ₂ := by
    have h' : P.root δ₂ = P.root δ₁ + P.root β := by rw [hδ₂, hδ₁, two_smul]; abel
    exact hδ₁pos.add hβ h'
  set k := pos.symm ⟨β, hβ⟩ with hkdef
  set l := pos.symm ⟨ε, hε⟩ with hldef
  set q₁ := pos.symm ⟨δ₁, hδ₁pos⟩ with hq₁def
  set q₂ := pos.symm ⟨δ₂, hδ₂pos⟩ with hq₂def
  have hk : ((pos k : {α // b.IsPos α}) : J) = β := by simp [k]
  have hl : ((pos l : {α // b.IsPos α}) : J) = ε := by simp [l]
  have hq₁ : ((pos q₁ : {α // b.IsPos α}) : J) = δ₁ := by simp [q₁]
  have hq₂ : ((pos q₂ : {α // b.IsPos α}) : J) = δ₂ := by simp [q₂]
  have hli : LinearIndependent ℤ ![P.root β, P.root ε] := by
    by_cases hβε' : β = ε
    · exfalso
      subst hβε'
      exact P.nsmul_notMem_range_root (n := 3) (i := β)
        ⟨δ₂, by rw [hδ₂]; simp only [show (3 : ℕ) = 2 + 1 from rfl, add_smul, one_smul]; simp⟩
    · exact RootPairing.IsReduced.linearIndependent P hβε' hβε
  have hq₁₂ : q₁ ≠ q₂ := by
    intro h
    have h' : P.root δ₁ = P.root δ₂ := by rw [← hq₁, ← hq₂, h]
    rw [hδ₁, hδ₂] at h'
    have h'' : (1 : ℤ) • P.root β + (0 : ℤ) • P.root ε = 0 := by
      rw [one_smul, zero_smul, add_zero]
      have : (2 : ℤ) • P.root β + P.root ε - (P.root β + P.root ε) = P.root β := by
        rw [two_smul]; abel
      rw [← this, ← h', sub_self]
    have := LinearIndependent.pair_iff.mp hli 1 0 h''
    omega
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := fun k => (neg k : J)) hTE ν hneg hpos k l
  have hzero : ∀ q, q ≠ q₁ → q ≠ q₂ → E q = 0 := by
    intro q hq hq'
    refine hE.eq_zero_of_forall_ne (i := i) (neg := fun k => (neg k : J)) hTE q ?_
    intro dS dT h1 h2 heq
    simp only [hk, hl] at heq
    rcases hcone _ dS dT h1 h2 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply hq
      apply pos.injective
      apply Subtype.ext
      apply P.root.injective
      rw [hq₁, hδ₁, ← heq]
      simp
    · apply hq'
      apply pos.injective
      apply Subtype.ext
      apply P.root.injective
      rw [hq₂, hδ₂, ← heq]
      simp
  have hmono : ∀ (q : Fin n) (e₁ e₂ : ℕ) (hq : (pos q : J) = δ₁ ∨ (pos q : J) = δ₂),
      (∀ dS dT, ((E q).coeff dT).coeff dS ≠ 0 → dS = e₁ ∧ dT = e₂) →
      E q = Polynomial.monomial e₂ (Polynomial.monomial e₁ (((E q).coeff e₂).coeff e₁)) := by
    intro q e₁ e₂ _ h
    ext dT dS
    rw [Polynomial.coeff_monomial, apply_ite (fun p : Polynomial R => p.coeff dS),
      Polynomial.coeff_monomial, Polynomial.coeff_zero]
    by_cases hnz : ((E q).coeff dT).coeff dS = 0
    · rw [hnz]
      split_ifs with h1 h2
      · subst h1; subst h2; exact hnz.symm.trans rfl
      · rfl
      · rfl
    · obtain ⟨rfl, rfl⟩ := h dS dT hnz
      simp
  have hE₁ : E q₁ = Polynomial.monomial 1 (Polynomial.monomial 1 (((E q₁).coeff 1).coeff 1)) := by
    refine hmono q₁ 1 1 (Or.inl hq₁) ?_
    intro dS dT hnz
    obtain ⟨h1, h2⟩ := hE.one_le (i := i) (neg := fun k => (neg k : J)) q₁ hnz
    have hw := hE.weight (neg := fun k => (neg k : J)) hTE q₁ hnz
    simp only [hk, hl, hq₁] at hw
    rcases hcone δ₁ dS dT h1 h2 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exfalso
      rw [hδ₁] at hw
      have h'' : (1 : ℤ) • P.root β + (0 : ℤ) • P.root ε = 0 := by
        rw [one_smul, zero_smul, add_zero]
        have : ((2 : ℕ) : ℤ) • P.root β + ((1 : ℕ) : ℤ) • P.root ε -
            (P.root β + P.root ε) = P.root β := by
          simp only [Nat.cast_ofNat, Nat.cast_one, one_smul, two_smul]; abel
        rw [← this, hw, sub_self]
      have := LinearIndependent.pair_iff.mp hli 1 0 h''
      omega
  have hE₂ : E q₂ = Polynomial.monomial 1 (Polynomial.monomial 2 (((E q₂).coeff 1).coeff 2)) := by
    refine hmono q₂ 2 1 (Or.inr hq₂) ?_
    intro dS dT hnz
    obtain ⟨h1, h2⟩ := hE.one_le (i := i) (neg := fun k => (neg k : J)) q₂ hnz
    have hw := hE.weight (neg := fun k => (neg k : J)) hTE q₂ hnz
    simp only [hk, hl, hq₂] at hw
    rcases hcone δ₂ dS dT h1 h2 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      rw [hδ₂] at hw
      have h'' : (1 : ℤ) • P.root β + (0 : ℤ) • P.root ε = 0 := by
        rw [one_smul, zero_smul, add_zero]
        have : (2 : ℤ) • P.root β + P.root ε -
            (((1 : ℕ) : ℤ) • P.root β + ((1 : ℕ) : ℤ) • P.root ε) = P.root β := by
          simp only [Nat.cast_one, one_smul, two_smul]; abel
        rw [← this, hw, sub_self]
      have := LinearIndependent.pair_iff.mp hli 1 0 h''
      omega
    · exact ⟨rfl, rfl⟩
  refine ⟨((E q₁).coeff 1).coeff 1, ((E q₂).coeff 1).coeff 2, fun B _ s x y => ?_⟩
  have h := hE.posComm_eq s x y
  simp only [posComm, hk, hl] at h
  rw [h]
  rcases lt_or_gt_of_ne hq₁₂ with hlt | hgt
  · rw [orderedProduct_eq_rootPoint_mul_of_eq_zero v _ _ _ hlt (fun q hq hq' => by
      rw [hzero q hq hq', map_zero, map_zero]), hq₁, hq₂, hE₁, hE₂]
    congr 2 <;> simp [lineEval, Polynomial.eval₂_monomial]
  · rw [orderedProduct_eq_rootPoint_mul_of_eq_zero v _ _ _ hgt (fun q hq hq' => by
      rw [hzero q hq' hq, map_zero, map_zero]), hq₁, hq₂, hE₁, hE₂, ← hcomm]
    congr 2 <;> simp [lineEval, Polynomial.eval₂_monomial]

/-- **Uniqueness of coordinates for three positive roots.** Let `δ₀`, `δ₁`, `δ₂` be distinct
positive roots of a base, the root groups of `δ₁` and `δ₂` commuting. If
`v_{δ₀}(r₀) = v_{δ₁}(r₁) v_{δ₂}(r₂)` over a ring over `R`, then `r₀ = r₁ = r₂ = 0`. -/
theorem coord_zero_of_eq_mul (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (b : P.Base) {δ₀ δ₁ δ₂ : J} (h₀ : b.IsPos δ₀) (h₁ : b.IsPos δ₁) (h₂ : b.IsPos δ₂)
    (h01 : δ₀ ≠ δ₁) (h02 : δ₀ ≠ δ₂) (h12 : δ₁ ≠ δ₂)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (hcomm : ∀ x y : Γ((Over.mk s).left, ⊤),
      rootPoint (v δ₁) (Over.mk s) x * rootPoint (v δ₂) (Over.mk s) y =
        rootPoint (v δ₂) (Over.mk s) y * rootPoint (v δ₁) (Over.mk s) x)
    (r₀ r₁ r₂ : Γ((Over.mk s).left, ⊤))
    (h : rootPoint (v δ₀) (Over.mk s) r₀ =
      rootPoint (v δ₁) (Over.mk s) r₁ * rootPoint (v δ₂) (Over.mk s) r₂) :
    r₀ = 0 ∧ r₁ = 0 ∧ r₂ = 0 := by
  classical
  obtain ⟨m, n, neg, pos, hopen, -⟩ := exists_cell_of_base hG hmax hP hv b
  have := hopen
  set q₀ := pos.symm ⟨δ₀, h₀⟩ with hq₀def
  set q₁ := pos.symm ⟨δ₁, h₁⟩ with hq₁def
  set q₂ := pos.symm ⟨δ₂, h₂⟩ with hq₂def
  have hq₀ : ((pos q₀ : {α // b.IsPos α}) : J) = δ₀ := by simp [q₀]
  have hq₁ : ((pos q₁ : {α // b.IsPos α}) : J) = δ₁ := by simp [q₁]
  have hq₂ : ((pos q₂ : {α // b.IsPos α}) : J) = δ₂ := by simp [q₂]
  have hne : ∀ {x y : Fin n}, ((pos x : {α // b.IsPos α}) : J) ≠ (pos y : J) → x ≠ y :=
    fun hxy h => hxy (by rw [h])
  have hq01 : q₀ ≠ q₁ := hne (by rw [hq₀, hq₁]; exact h01)
  have hq02 : q₀ ≠ q₂ := hne (by rw [hq₀, hq₂]; exact h02)
  have hq12 : q₁ ≠ q₂ := hne (by rw [hq₁, hq₂]; exact h12)
  have e₀ := orderedProduct_eq_rootPoint_of_eq_zero v (fun k => (pos k : J)) (Over.mk s)
    (fun q => if q = q₀ then r₀ else 0) q₀ (fun l hl => by simp [hl])
  simp only [hq₀, ↓reduceIte] at e₀
  have e₁ : orderedProduct v (fun k => (pos k : J)) (Over.mk s)
      (fun q => if q = q₁ then r₁ else if q = q₂ then r₂ else 0) =
      rootPoint (v δ₁) (Over.mk s) r₁ * rootPoint (v δ₂) (Over.mk s) r₂ := by
    rcases lt_or_gt_of_ne hq12 with hlt | hgt
    · rw [orderedProduct_eq_rootPoint_mul_of_eq_zero v _ _ _ hlt (fun l hl hl' => by
        simp [hl, hl'])]
      simp only [hq₁, hq₂, ↓reduceIte, hq12.symm]
    · rw [orderedProduct_eq_rootPoint_mul_of_eq_zero v _ _ _ hgt (fun l hl hl' => by
        simp [hl, hl'])]
      simp only [hq₁, hq₂, ↓reduceIte, hq12.symm]
      exact (hcomm r₁ r₂).symm
  have h3 := orderedProduct_pos_injective (i := i) (neg := fun k => (neg k : J))
    (Over.mk s) (e₀.trans (h.trans e₁.symm))
  have h4 := congrFun h3 q₀
  have h5 := congrFun h3 q₁
  have h6 := congrFun h3 q₂
  simp only [hq01, hq02, hq01.symm, hq02.symm, hq12.symm, ↓reduceIte] at h4 h5 h6
  exact ⟨h4, h5.symm, h6.symm⟩

end Pairs

end LocalSplitCell

open LocalSplitCell in
/-- **Commutators of two root groups.** For a reductive group scheme over a commutative ring
with a fibrewise maximal coordinate split torus, a fibrewise root datum `P`, and root
parametrizations `v α` of all roots, let `β` and `ε` be roots with `β ≠ -ε`. (1) If no
`dS • β + dT • ε` with `dS, dT ≥ 1` is a root, the root groups of `β` and `ε` commute over
every ring over `R`. (2) If `δ = β + ε` is a root and `dS • β + dT • ε` with `dS, dT ≥ 1` is a
root only for `dS = dT = 1`, there is `C ∈ R` with
`(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = v_δ(C x y)` over every ring over `R`. -/
def LocalSplitRootPairCommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom], IsReductive G →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    ∀ (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
    ∀ (v : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (v α)) →
    ∀ (β ε : J), P.root β ≠ -P.root ε →
    ((∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
        (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε ≠ P.root α) →
      ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x y : Γ((Over.mk s).left, ⊤)),
        rootPoint (v β) (Over.mk s) x * rootPoint (v ε) (Over.mk s) y =
          rootPoint (v ε) (Over.mk s) y * rootPoint (v β) (Over.mk s) x) ∧
    ∀ δ : J, P.root δ = P.root β + P.root ε →
      (∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
        (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε = P.root α → dS = 1 ∧ dT = 1) →
      ∃ C : R, ∀ (B : Type u) [CommRing B]
        (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B),
        (rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
            rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
          (rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
            rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
        rootPoint (v δ) (Over.mk s)
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Spec.preimage s).hom C * x * y))

open LocalSplitCell in
/-- The commutator statement holds at full universe. -/
theorem localSplitRootPairCommutator : LocalSplitRootPairCommutatorStatement.{u} := by
  intro R _ I _ J G _ hG i hmax P hP v hv β ε hβε
  exact ⟨fun hcone B _ s x y => rootPoint_commute_of_forall_ne hG hmax hP hv hβε hcone s x y,
    fun δ hδ hcone => exists_rootPoint_comm_single hG hmax hP hv hβε hδ hcone⟩

end Langlands.GroupScheme
