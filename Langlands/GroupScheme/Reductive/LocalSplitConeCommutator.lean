import Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator

/-! # Commutators with an ordered cone of roots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section InitialSegment

variable {I : Type*} {J : Type*} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- **Enumerations with a prescribed initial segment.** For a list `L` of distinct positive
roots of a base, some enumeration of the positive roots lists `L` first, in order. -/
theorem exists_pos_initial [Finite J] (b : P.Base) (L : List J) (hL : L.Nodup)
    (hpos : ∀ x ∈ L, b.IsPos x) :
    ∃ (m : ℕ) (pos : Fin (L.length + m) ≃ {α // b.IsPos α}),
      ∀ r : Fin L.length, ((pos (Fin.castAdd m r) : {α // b.IsPos α}) : J) = L.get r := by
  classical
  let p : {α // b.IsPos α} → Prop := fun x => (x : J) ∈ L
  let e₂ : {x : {α // b.IsPos α} // p x} ≃ {x : J // x ∈ L} :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hpos y.1 y.2⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let e₃ := Finite.equivFin {x : {α // b.IsPos α} // ¬ p x}
  let total : {α // b.IsPos α} ≃ Fin (L.length + Nat.card {x : {α // b.IsPos α} // ¬ p x}) :=
    (Equiv.sumCompl p).symm.trans
      ((Equiv.sumCongr (e₂.trans (List.Nodup.getEquiv L hL).symm) e₃).trans finSumFinEquiv)
  refine ⟨_, total.symm, fun r => ?_⟩
  simp only [total, Equiv.symm_trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_symm,
    Equiv.sumCompl_apply_inl]
  rfl

end InitialSegment

section Cone

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {v : J → (Ga R ⟶ G)}

/-- The pairing `coPairing` is additive and homogeneous in its first argument. -/
theorem coPairing_combo (x y ν : I → ℤ) (p q : ℤ) :
    coPairing (p • x + q • y) ν = p * coPairing x ν + q * coPairing y ν := by
  simp only [coPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

omit [IsAffineHom G.X.hom] in
/-- An ordered product whose coordinates vanish after the first `k` positions is the ordered
product of its first `k` factors. -/
theorem orderedProduct_initial (u : J → (Ga R ⟶ G)) {k m : ℕ} (pos : Fin (k + m) → J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin (k + m) → Γ(Z.left, ⊤))
    (hc : ∀ j : Fin m, c (Fin.natAdd k j) = 0) :
    orderedProduct u pos Z c =
      (List.ofFn fun r : Fin k =>
        rootPoint (u (pos (Fin.castAdd m r))) Z (c (Fin.castAdd m r))).prod := by
  unfold orderedProduct
  rw [List.ofFn_add, List.prod_append]
  have h : (List.ofFn fun j : Fin m =>
      rootPoint (u (pos (Fin.natAdd k j))) Z (c (Fin.natAdd k j))) =
      List.ofFn fun _ : Fin m => (1 : Z ⟶ G.X) := by
    congr 1
    funext j
    rw [hc j, rootPoint_zero]
  rw [h, prod_ofFn_one, mul_one]
  rfl

/-- **Cells with a prescribed initial segment.** -/
theorem exists_cell_initial (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (b : P.Base) (L : List J) (hL : L.Nodup) (hpos : ∀ x ∈ L, b.IsPos x) :
    ∃ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin (L.length + n) ≃ {α // b.IsPos α}),
      (∀ r : Fin L.length, ((pos (Fin.castAdd n r) : {α // b.IsPos α}) : J) = L.get r) ∧
      IsOpenImmersion (cellMap i v (fun k => (neg k : J)) (fun k => (pos k : J))).left ∧
      ∃ ν : I → ℤ, (∀ k, coPairing (P.root (neg k : J)) ν < 0) ∧
        (∀ k, 0 < coPairing (P.root (pos k : J)) ν) := by
  have := hP.finite
  obtain ⟨n, pos, hpos'⟩ := exists_pos_initial b L hL hpos
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  refine ⟨_, n, neg, pos, hpos',
    LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b v hv neg pos, ?_⟩
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  refine ⟨ν, fun k => ?_, fun k => ?_⟩
  · rw [hν]
    have h0 := b.height_ne_zero (neg k : J)
    have h1 := (neg k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd (by omega)
  · rw [hν]
    exact mul_pos hd (pos k).2

/-- **Uniqueness of coordinates for an ordered list of positive roots.** -/
theorem listProd_rootPoint_injective (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    (b : P.Base) (L : List J) (hL : L.Nodup) (hpos : ∀ x ∈ L, b.IsPos x)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    {x y : Fin L.length → Γ((Over.mk s).left, ⊤)}
    (h : (List.ofFn fun r => rootPoint (v (L.get r)) (Over.mk s) (x r)).prod =
      (List.ofFn fun r => rootPoint (v (L.get r)) (Over.mk s) (y r)).prod) :
    x = y := by
  classical
  obtain ⟨m, n, neg, pos, hpos', hopen, -⟩ := exists_cell_initial hG hmax hP hv b L hL hpos
  have := hopen
  let cx : Fin (L.length + n) → Γ((Over.mk s).left, ⊤) :=
    Fin.addCases (fun r => x r) (fun _ => 0)
  let cy : Fin (L.length + n) → Γ((Over.mk s).left, ⊤) :=
    Fin.addCases (fun r => y r) (fun _ => 0)
  have ex := orderedProduct_initial v (fun k => (pos k : J)) (Over.mk s) cx
    (fun j => by simp [cx])
  have ey := orderedProduct_initial v (fun k => (pos k : J)) (Over.mk s) cy
    (fun j => by simp [cy])
  simp only [hpos', cx, cy, Fin.addCases_left] at ex ey
  have h3 := orderedProduct_pos_injective (i := i) (neg := fun k => (neg k : J))
    (Over.mk s) (ex.trans (h.trans ey.symm))
  funext r
  have := congrFun h3 (Fin.castAdd n r)
  simpa [cx, cy] using this

/-- **The commutator of two root groups along an ordered cone.** Let `β ≠ ε` be roots that are
not opposite, and let `L` be a list of distinct roots with `L r = e₁ r • β + e₂ r • ε`,
`e₁ r, e₂ r ≥ 1`, containing every root of the form `dS • β + dT • ε` with `dS, dT ≥ 1`.
Then there are constants `C r ∈ R` such that over every ring over `R`,
`(v_β(x) v_ε(y))⁻¹ (v_ε(y) v_β(x)) = ∏_r v_{L r}(C r x^{e₁ r} y^{e₂ r})`, the product taken
in the order of `L`. -/
theorem exists_rootPoint_comm_cone (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {β ε : J} (hβε : P.root β ≠ -P.root ε) (hne : β ≠ ε) (L : List J) (hL : L.Nodup)
    (ex : Fin L.length → ℕ × ℕ)
    (hex : ∀ r, P.root (L.get r) = ((ex r).1 : ℤ) • P.root β + ((ex r).2 : ℤ) • P.root ε)
    (hex1 : ∀ r, 1 ≤ (ex r).1 ∧ 1 ≤ (ex r).2)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root ε = P.root α → α ∈ L) :
    ∃ C : Fin L.length → R, ∀ (B : Type u) [CommRing B]
      (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : B),
      (rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v ε) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v β) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      (List.ofFn fun r => rootPoint (v (L.get r)) (Over.mk s)
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv
          ((Spec.preimage s).hom (C r) * x ^ (ex r).1 * y ^ (ex r).2))).prod := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b, hβ, hε⟩ := Langlands.LinearAlgebra.exists_base_isPos_pair P hβε
  have hli : LinearIndependent ℤ ![P.root β, P.root ε] :=
    RootPairing.IsReduced.linearIndependent P hne hβε
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  have hLpos : ∀ x ∈ L, b.IsPos x := by
    intro x hx
    obtain ⟨r, rfl⟩ := List.mem_iff_get.mp hx
    have h := hν (L.get r)
    rw [hex r, coPairing_combo, hν, hν] at h
    have h1 := hex1 r
    have hb : 0 < b.height β := hβ
    have he : 0 < b.height ε := hε
    rw [RootPairing.Base.isPos_iff]
    by_contra hneg
    have hneg := not_lt.mp hneg
    have : d * b.height (L.get r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le hneg
    have h2 : 0 < ((ex r).1 : ℤ) * (d * b.height β) + ((ex r).2 : ℤ) * (d * b.height ε) := by
      have : (1 : ℤ) ≤ (ex r).1 := by exact_mod_cast h1.1
      have : (1 : ℤ) ≤ (ex r).2 := by exact_mod_cast h1.2
      positivity
    linarith
  obtain ⟨m, n, neg, pos, hpos', hopen, ν', hneg, hpos⟩ :=
    exists_cell_initial hG hmax hP hv b L hL hLpos
  have := hopen
  have hTE : TorusEquivariant i (fun α => P.root α) v := fun α Z t c => (hv α).equivariant Z t c
  set k := pos.symm ⟨β, hβ⟩ with hkdef
  set l := pos.symm ⟨ε, hε⟩ with hldef
  have hk : ((pos k : {α // b.IsPos α}) : J) = β := by simp [k]
  have hl : ((pos l : {α // b.IsPos α}) : J) = ε := by simp [l]
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := fun k => (neg k : J)) hTE ν' hneg hpos k l
  -- the coordinates outside the initial segment vanish
  have hzero : ∀ j : Fin n, E (Fin.natAdd L.length j) = 0 := by
    intro j
    refine hE.eq_zero_of_forall_ne (i := i) (neg := fun k => (neg k : J)) hTE _ ?_
    intro dS dT h1 h2 heq
    simp only [hk, hl] at heq
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp (hcone _ dS dT h1 h2 heq)
    have : Fin.castAdd n r = Fin.natAdd L.length j := by
      apply pos.injective
      apply Subtype.ext
      rw [hpos' r, hr]
    have hv' := congrArg Fin.val this
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv'
    omega
  -- the coordinate at `L r` is a single monomial
  have hmono : ∀ r : Fin L.length, E (Fin.castAdd n r) =
      Polynomial.monomial (ex r).2 (Polynomial.monomial (ex r).1
        (((E (Fin.castAdd n r)).coeff (ex r).2).coeff (ex r).1)) := by
    intro r
    ext dT dS
    rw [Polynomial.coeff_monomial, apply_ite (fun p : Polynomial R => p.coeff dS),
      Polynomial.coeff_monomial, Polynomial.coeff_zero]
    by_cases hnz : ((E (Fin.castAdd n r)).coeff dT).coeff dS = 0
    · rw [hnz]
      split_ifs with h1 h2
      · subst h1; subst h2; exact hnz.symm.trans rfl
      · rfl
      · rfl
    · have hw := hE.weight (neg := fun k => (neg k : J)) hTE (Fin.castAdd n r) hnz
      simp only [hk, hl, hpos' r, hex r] at hw
      have h0 : ((dS : ℤ) - (ex r).1) • P.root β + ((dT : ℤ) - (ex r).2) • P.root ε = 0 := by
        rw [sub_smul, sub_smul]
        rw [← sub_eq_zero] at hw
        rw [← hw]
        abel
      have := LinearIndependent.pair_iff.mp hli _ _ h0
      have e1 : dS = (ex r).1 := by omega
      have e2 : dT = (ex r).2 := by omega
      subst e1; subst e2
      simp
  refine ⟨fun r => ((E (Fin.castAdd n r)).coeff (ex r).2).coeff (ex r).1, fun B _ s x y => ?_⟩
  have h := hE.posComm_eq s x y
  simp only [posComm, hk, hl] at h
  rw [h, orderedProduct_initial v (fun k => (pos k : J)) _ _ (fun j => by
    rw [hzero j, map_zero, map_zero])]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  simp only [hpos' r]
  rw [hmono r]
  congr 2
  simp [lineEval, Polynomial.eval₂_monomial]

end Cone

end LocalSplitCell

end Langlands.GroupScheme
