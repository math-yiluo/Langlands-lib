import Langlands.GroupScheme.SimplyConnected.FactorialCellData

/-! # The negative and positive spans and the rank-one translation of the big cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitFactorial

open LocalSplitCell

/-- A list product with all factors but one in a subgroup splits around that factor. -/
theorem list_prod_ofFn_split {M : Type*} [Group M] (S : Subgroup M) :
    ∀ {m : ℕ} (f : Fin m → M) (r₀ : Fin m), (∀ r, r ≠ r₀ → f r ∈ S) →
      ∃ A ∈ S, ∃ B ∈ S, (List.ofFn f).prod = A * f r₀ * B
  | 0, _, r₀, _ => r₀.elim0
  | m + 1, f, r₀, hf => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun r₁ hr => ?_) r₀ hf
    · intro hf
      refine ⟨1, S.one_mem, (List.ofFn fun r => f r.succ).prod, ?_, by rw [one_mul]⟩
      apply Subgroup.list_prod_mem
      intro g hg
      obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hg
      exact hf r.succ (Fin.succ_ne_zero r)
    · obtain ⟨A, hA, B, hB, h⟩ := list_prod_ofFn_split S (fun r => f r.succ) r₁
        (fun r hr' => hr r.succ fun h => hr' (Fin.succ_injective _ h))
      refine ⟨f 0 * A, S.mul_mem (hr 0 (Fin.succ_ne_zero r₁).symm) hA, B, hB, ?_⟩
      simp only [h, mul_assoc]

namespace CellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : CellData k G)

/-! ### Root combinatorics -/

/-- The negative roots form a closed set without opposite pairs. -/
theorem isClosedRootSet_neg : D.IsClosedRootSet {α | ¬ D.b.IsPos α} := by
  refine ⟨fun a ha c hc d hd => ?_, fun a ha c hc h => ?_⟩
  · simp only [Set.mem_ofPred_eq, RootPairing.Base.isPos_iff] at ha hc ⊢
    rw [D.b.height_add hd]
    lia
  · simp only [Set.mem_ofPred_eq] at ha hc
    let := D.P.indexNeg
    have hc' : c = -a := by
      apply D.P.root.injective
      rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self]
      exact eq_neg_of_add_eq_zero_right h
    rw [hc', RootPairing.Base.IsPos.neg_iff_not] at hc
    exact hc ha

/-- The positive roots form a closed set without opposite pairs. -/
theorem isClosedRootSet_pos : D.IsClosedRootSet {α | D.b.IsPos α} := by
  refine ⟨fun a ha c hc d hd => ?_, fun a ha c hc h => ?_⟩
  · exact RootPairing.Base.IsPos.add ha hc hd
  · simp only [Set.mem_ofPred_eq] at ha hc
    let := D.P.indexNeg
    have hc' : c = -a := by
      apply D.P.root.injective
      rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self]
      exact eq_neg_of_add_eq_zero_right h
    rw [hc', RootPairing.Base.IsPos.neg_iff_not] at hc
    exact hc ha

/-- A positive combination of a simple root and a negative root other than its opposite is not a
positive root. -/
theorem not_isPos_of_root_eq_add {a β d : D.J} (ha : a ∈ D.b.support) (hβ : ¬ D.b.IsPos β)
    (hβa : D.P.root β ≠ -D.P.root a) {p q : ℕ} (hq : 0 < q)
    (hd : D.P.root d = p • D.P.root a + q • D.P.root β) : ¬ D.b.IsPos d := by
  classical
  obtain ⟨g, hg0, hgs, hg⟩ := D.b.exists_root_eq_sum_int β
  have hgneg : g < 0 := by
    rcases hgs with h | h
    · exfalso
      apply hβ
      rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_eq_sum hg]
      refine Finset.sum_pos' (fun j _ => h.le j) ?_
      obtain ⟨j, hj⟩ := (Pi.lt_def.1 h).2
      exact ⟨j, hg0 (ne_of_gt hj), hj⟩
    · exact h
  have hgle : ∀ j, g j ≤ 0 := fun j => hgneg.le j
  -- some simple root other than `a` has a negative coefficient
  have hj : ∃ j ∈ D.b.support, j ≠ a ∧ g j < 0 := by
    by_contra! hcon
    have hsum : D.P.root β = g a • D.P.root a := by
      rw [hg, Finset.sum_eq_single_of_mem a ha]
      intro j hj hja
      rw [le_antisymm (hgle j) (hcon j hj hja), zero_smul]
    have hga := D.b.eq_one_or_neg_one_of_mem_support_of_smul_mem a ha (g a)
      ⟨β, hsum⟩
    rcases hga with h1 | h1
    · have := hgle a
      lia
    · exact hβa (by rw [hsum, h1, neg_one_smul])
  obtain ⟨j₀, hj₀, hj₀a, hgj₀⟩ := hj
  let f : D.J → ℤ := (p : ℤ) • Pi.single a 1 + (q : ℤ) • g
  have hf : D.P.root d = ∑ j ∈ D.b.support, f j • D.P.root j := by
    simp only [f, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_assoc,
      ← Finset.smul_sum, ← hg]
    rw [Finset.sum_eq_single_of_mem a ha]
    · simp [hd]
    · intro j _ hja
      simp [hja]
  have hf0 : f.support ⊆ D.b.support := by
    intro j hj
    by_contra hjs
    apply hj
    have hja : j ≠ a := fun h => hjs (h ▸ ha)
    have hgj : g j = 0 := by
      by_contra h
      exact hjs (hg0 h)
    simp [f, hja, hgj]
  have hfj₀ : f j₀ < 0 := by
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    simp only [f, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hj₀a, ite_false, smul_eq_mul]
    nlinarith
  have hfneg : f < 0 := by
    rcases D.b.pos_or_neg_of_sum_smul_root_mem f ⟨d, hf⟩ hf0 with h | h
    · exact absurd ((Pi.lt_def.1 h).1 j₀) (not_le.2 hfj₀)
    · exact h
  rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_eq_sum hf, not_lt]
  exact (Finset.sum_neg' (fun j _ => hfneg.le j) ⟨j₀, hj₀, hfj₀⟩).le

/-- The subgroup functor spanned by the negative root groups. -/
def negSpan : SubgroupFunctor G := D.rootSpan D.isClosedRootSet_neg

/-- The subgroup functor spanned by the positive root groups. -/
def posSpan : SubgroupFunctor G := D.rootSpan D.isClosedRootSet_pos

theorem rootPoint_mem_negSpan {β : D.J} (hβ : ¬ D.b.IsPos β) (Z : Over (Spec (CommRingCat.of k)))
    (c : Γ(Z.left, ⊤)) : rootPoint (D.u β) Z c ∈ D.negSpan.carrier Z :=
  D.rootPoint_mem_rootSpan D.isClosedRootSet_neg hβ Z c

theorem rootPoint_mem_posSpan {β : D.J} (hβ : D.b.IsPos β) (Z : Over (Spec (CommRingCat.of k)))
    (c : Γ(Z.left, ⊤)) : rootPoint (D.u β) Z c ∈ D.posSpan.carrier Z :=
  D.rootPoint_mem_rootSpan D.isClosedRootSet_pos hβ Z c

/-! ### Conjugating negative root groups by a simple root group -/

/-- Conjugation by a simple root point keeps the other negative root points in the negative
span. -/
theorem conj_rootPoint_mem_negSpan {a β : D.J} (ha : a ∈ D.b.support) (hβ : ¬ D.b.IsPos β)
    (hβa : D.P.root β ≠ -D.P.root a) (Z : Over (Spec (CommRingCat.of k))) (x y : Γ(Z.left, ⊤)) :
    rootPoint (D.u a) Z x * rootPoint (D.u β) Z y * rootPoint (D.u a) Z (-x) ∈
      D.negSpan.carrier Z := by
  classical
  have hβa' : D.P.root β ≠ D.P.root a := by
    intro h
    exact hβ (D.P.root.injective h ▸ RootPairing.Base.isPos_of_mem_support ha)
  let S : Set D.J := {d | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ D.P.root d = p • D.P.root a + q • D.P.root β}
  have : Fintype S := Fintype.ofFinite S
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  obtain ⟨p, q, C, hpq, hcomm⟩ := (affineSplitRootSubgroupSpanning k G D.isReductive D.I D.i
    D.isClosedSubgroup D.isFibrewiseMaximal D.J D.P D.hP D.u D.hu).2.2.2 a β hβa' hβa _ e
  have hprod : orderedProduct D.u (fun r => ((e r : S) : D.J)) Z
      (fun r => scalarMap Z (C r) * x ^ p r * y ^ q r) ∈ D.negSpan.carrier Z := by
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hg
    obtain ⟨-, hq, hr⟩ := hpq r
    exact D.rootPoint_mem_negSpan (D.not_isPos_of_root_eq_add ha hβ hβa hq hr) Z _
  have key : rootPoint (D.u a) Z x * rootPoint (D.u β) Z y * rootPoint (D.u a) Z (-x) =
      (rootPoint (D.u a) Z x * rootPoint (D.u β) Z y * rootPoint (D.u a) Z (-x) *
        rootPoint (D.u β) Z (-y)) * rootPoint (D.u β) Z y := by
    rw [rootPoint_neg (D.u β), inv_mul_cancel_right]
  rw [key, hcomm Z x y]
  exact mul_mem hprod (D.rootPoint_mem_negSpan hβ Z y)

/-- The negative-span points whose conjugates by every point of the root group of `a` stay in
the negative span. -/
def negConj (a : D.J) (Z : Over (Spec (CommRingCat.of k))) : Subgroup (Z ⟶ G.X) :=
  D.negSpan.carrier Z ⊓
    ⨅ x : Γ(Z.left, ⊤),
      (D.negSpan.carrier Z).comap (MulAut.conj (rootPoint (D.u a) Z x)).toMonoidHom

theorem conj_mem_negSpan_of_mem_negConj {a : D.J} {Z : Over (Spec (CommRingCat.of k))}
    {g : Z ⟶ G.X} (hg : g ∈ D.negConj a Z) (x : Γ(Z.left, ⊤)) :
    rootPoint (D.u a) Z x * g * rootPoint (D.u a) Z (-x) ∈ D.negSpan.carrier Z := by
  have h := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2) x
  rw [Subgroup.mem_comap] at h
  rw [rootPoint_neg]
  exact h

theorem rootPoint_mem_negConj {a β : D.J} (ha : a ∈ D.b.support) (hβ : ¬ D.b.IsPos β)
    (hβa : D.P.root β ≠ -D.P.root a) (Z : Over (Spec (CommRingCat.of k))) (y : Γ(Z.left, ⊤)) :
    rootPoint (D.u β) Z y ∈ D.negConj a Z := by
  refine Subgroup.mem_inf.2 ⟨D.rootPoint_mem_negSpan hβ Z y, Subgroup.mem_iInf.2 fun x => ?_⟩
  rw [Subgroup.mem_comap]
  have h := D.conj_rootPoint_mem_negSpan ha hβ hβa Z x y
  rw [rootPoint_neg] at h
  exact h

/-! ### The rank-one translation of the big cell -/

theorem root_reflectionPerm_self (a : D.J) :
    D.P.root (D.P.reflectionPerm a a) = -D.P.root a := by
  simp

theorem not_isPos_reflectionPerm_self {a : D.J} (ha : a ∈ D.b.support) :
    ¬ D.b.IsPos (D.P.reflectionPerm a a) := by
  let := D.P.indexNeg
  have h := RootPairing.Base.IsPos.neg_iff_not (b := D.b) a
  rw [RootPairing.indexNeg_neg] at h
  rw [h, not_not]
  exact RootPairing.Base.isPos_of_mem_support ha

/-- The rank-one laws of a simple root and its opposite. -/
theorem rankOneLaws {a : D.J} (ha : a ∈ D.b.support) :
    RankOneLaws D.i (D.P.coroot a) (D.u a) (D.u (D.P.reflectionPerm a a)) :=
  LocalSplitCell.rankOneLaws_of_weylNormalization_affine D.isReductive D.i D.isClosedSubgroup
    D.isFibrewiseMaximal D.hP a (D.hu a)
    (by rw [← D.root_reflectionPerm_self]; exact D.hu _) (D.weyl a ha)

/-- **Left translation of a big-cell point by `u_a(e₀)`.** If the coordinate `y` of the opposite
root `-a` satisfies `1 + e₀ y = d` with `d` a unit, then `u_a(e₀)` times the cell point with torus
coordinate `t` is again a cell point, with torus coordinate `a∨(d) t`. -/
theorem exists_translate_cellPoint {a : D.J} (ha : a ∈ D.b.support) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ D.b.IsPos α}) (pos : Fin n ≃ {α // D.b.IsPos α})
    (Z : Over (Spec (CommRingCat.of k))) (c : Fin m → Γ(Z.left, ⊤))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) D.I).X) (w : Fin n → Γ(Z.left, ⊤))
    (e₀ : Γ(Z.left, ⊤)) (d : (Γ(Z.left, ⊤))ˣ)
    (hd : (d : Γ(Z.left, ⊤)) =
      1 + e₀ * c (neg.symm ⟨D.P.reflectionPerm a a, D.not_isPos_reflectionPerm_self ha⟩)) :
    ∃ (v' : Fin m → Γ(Z.left, ⊤)) (w' : Fin n → Γ(Z.left, ⊤)),
      rootPoint (D.u a) Z e₀ * cellPoint D.i D.u (fun r => (neg r : D.J)) (fun r => (pos r : D.J))
          Z c t w =
        cellPoint D.i D.u (fun r => (neg r : D.J)) (fun r => (pos r : D.J)) Z v'
          (cocharPoint (D.P.coroot a) Z d * t) w' := by
  set na := D.P.reflectionPerm a a with hna_def
  have hna : ¬ D.b.IsPos na := D.not_isPos_reflectionPerm_self ha
  set r₀ := neg.symm ⟨na, hna⟩ with hr₀
  let f : Fin m → (Z ⟶ G.X) := fun r => rootPoint (D.u (neg r)) Z (c r)
  have hf : ∀ r, r ≠ r₀ → f r ∈ D.negConj a Z := by
    intro r hr
    refine D.rootPoint_mem_negConj ha (neg r).2 ?_ Z (c r)
    intro h
    apply hr
    rw [hr₀, Equiv.eq_symm_apply]
    apply Subtype.ext
    apply D.P.root.injective
    rw [h, D.root_reflectionPerm_self]
  obtain ⟨A, hA, B, hB, hsplit⟩ := list_prod_ofFn_split (D.negConj a Z) f r₀ hf
  have hfr₀ : f r₀ = rootPoint (D.u na) Z (c r₀) := by
    simp only [f, hr₀, Equiv.apply_symm_apply]
  -- notation
  set y := c r₀ with hy
  set T := t ≫ D.i.hom.hom with hT
  set Cc := cocharPoint (D.P.coroot a) Z d ≫ D.i.hom.hom with hCc
  set U := orderedProduct D.u (fun r => (pos r : D.J)) Z w with hU
  set e : Γ(Z.left, ⊤) := (↑d⁻¹ : Γ(Z.left, ⊤)) * e₀ with he
  set e'' : Γ(Z.left, ⊤) := VectorGroup.charValue (S := splitTorus.commGroupScheme _ D.I)
    (splitTorus.exponentCharacter _ D.I (D.P.root a)) Z t⁻¹ * e with he''
  -- the rank-one relation
  have E1 : rootPoint (D.u a) Z e₀ * rootPoint (D.u na) Z y =
      rootPoint (D.u na) Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) * Cc * rootPoint (D.u a) Z e :=
    (D.rankOneLaws ha).2.2.2 Z e₀ y d hd
  -- moving the positive root point past the torus
  have E2 : T * rootPoint (D.u a) Z e'' = rootPoint (D.u a) Z e * T := by
    have h := (D.hu a).equivariant Z t⁻¹ e
    rw [GrpObj.inv_comp, inv_inv, ← he''] at h
    rw [← h, hT]
    group
  set A₁ := rootPoint (D.u a) Z e₀ * A * rootPoint (D.u a) Z (-e₀) with hA₁
  set B₁ := rootPoint (D.u a) Z e * B * rootPoint (D.u a) Z (-e) with hB₁
  have hA₁m : A₁ ∈ D.negSpan.carrier Z := D.conj_mem_negSpan_of_mem_negConj hA e₀
  have hB₁m : B₁ ∈ D.negSpan.carrier Z := D.conj_mem_negSpan_of_mem_negConj hB e
  have hN : A₁ * rootPoint (D.u na) Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) * (Cc * B₁ * Cc⁻¹) ∈
      D.negSpan.carrier Z :=
    mul_mem (mul_mem hA₁m (D.rootPoint_mem_negSpan hna Z _))
      (D.torus_conj_mem_rootSpan D.isClosedRootSet_neg _ hB₁m)
  have hPp : rootPoint (D.u a) Z e'' * U ∈ D.posSpan.carrier Z :=
    mul_mem (D.rootPoint_mem_posSpan (RootPairing.Base.isPos_of_mem_support ha) Z _)
      (D.orderedProduct_mem_rootSpan D.isClosedRootSet_pos pos Z w)
  obtain ⟨v', hv'⟩ := D.exists_eq_orderedProduct D.isClosedRootSet_neg neg hN
  obtain ⟨w', hw'⟩ := D.exists_eq_orderedProduct D.isClosedRootSet_pos pos hPp
  refine ⟨v', w', ?_⟩
  have hv'' : orderedProduct D.u (fun r => (neg r : D.J)) Z v' =
      A₁ * rootPoint (D.u na) Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) * (Cc * B₁ * Cc⁻¹) := hv'
  have hw'' : orderedProduct D.u (fun r => (pos r : D.J)) Z w' = rootPoint (D.u a) Z e'' * U :=
    hw'
  rw [cellPoint, cellPoint, hv'', hw'', MonObj.mul_comp]
  change rootPoint (D.u a) Z e₀ * ((List.ofFn f).prod * T * U) = _
  rw [hsplit, hfr₀, hA₁, hB₁, rootPoint_neg, rootPoint_neg]
  calc rootPoint (D.u a) Z e₀ * (A * rootPoint (D.u na) Z y * B * T * U)
      = rootPoint (D.u a) Z e₀ * A * (rootPoint (D.u a) Z e₀)⁻¹ *
          (rootPoint (D.u a) Z e₀ * rootPoint (D.u na) Z y) * B * T * U := by group
    _ = rootPoint (D.u a) Z e₀ * A * (rootPoint (D.u a) Z e₀)⁻¹ *
          (rootPoint (D.u na) Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) * Cc * rootPoint (D.u a) Z e) *
          B * ((rootPoint (D.u a) Z e)⁻¹ * (rootPoint (D.u a) Z e * T)) * U := by
        rw [E1]; group
    _ = rootPoint (D.u a) Z e₀ * A * (rootPoint (D.u a) Z e₀)⁻¹ *
          (rootPoint (D.u na) Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) * Cc * rootPoint (D.u a) Z e) *
          B * ((rootPoint (D.u a) Z e)⁻¹ * (T * rootPoint (D.u a) Z e'')) * U := by
        rw [E2]
    _ = _ := by rw [← hCc, ← hT]; group

end CellData

end Langlands.GroupScheme.SplitFactorial
