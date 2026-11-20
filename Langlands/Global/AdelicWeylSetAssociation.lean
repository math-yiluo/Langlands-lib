import Langlands.Global.AdelicInducedInnerProduct

/-! # Association of parabolics and the counting identity for `Ω(P, P')`

For parabolics `P = MU` with Levi projections `π` (`l ≫ π = 𝟙`), the Weyl sets
`Ω(P, P') = weylParameterSet p l p' l' π'` compose: `(w, c)` presenting an element of `Ω(P, P')`
and `(w', c')` presenting one of `Ω(P', P'')` give `(w' w, c' ≫ c)` presenting the composite in
`Ω(P, P'')`, and `(w⁻¹, c⁻¹)` presents an element of `Ω(P', P)`. Hence association
(`Ω(P, P') ≠ ∅`) is symmetric and transitive, `|Ω(P, P'')| = |Ω(P', P'')|` and
`|Ω(P'', P)| = |Ω(P'', P')|` for associate `P`, `P'`, and for a finite family `(P i)` with
`n_P i = ∑ i', |Ω(P i, P i')|`, `∑ i, (n_P i)⁻¹ |Ω(P i, P i')| = 1` whenever `n_P i' ≠ 0`
(Arthur 2005, §7, the weights `n_P` of Theorem 7.2; Lapid 2011, §3, Theorem 2). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-! ### A counting lemma -/

/-- Let `N a b` be natural numbers on a finite type such that `N a b ≠ 0` is symmetric, and for
`N a b ≠ 0` the rows and the columns of `a` and `b` agree. Then for every `b` whose row sum
`n b = ∑ x, N b x` is nonzero, `∑ a, (n a)⁻¹ N a b = 1`. -/
theorem sum_inv_rowSum_mul_eq_one {I : Type*} [Fintype I] (N : I → I → ℕ)
    (hsymm : ∀ a b, N a b ≠ 0 → N b a ≠ 0)
    (hright : ∀ a b, N a b ≠ 0 → ∀ x, N a x = N b x)
    (hleft : ∀ a b, N a b ≠ 0 → ∀ x, N x a = N x b)
    (b : I) (hb : ∑ x, N b x ≠ 0) :
    ∑ a, ((∑ x, N a x : ℕ) : ℝ)⁻¹ * (N a b : ℝ) = 1 := by
  classical
  set C := Finset.univ.filter (fun a => N a b ≠ 0) with hC
  have hsum : ∑ a, ((∑ x, N a x : ℕ) : ℝ)⁻¹ * (N a b : ℝ) =
      ∑ a, if N a b ≠ 0 then ((∑ x, N b x : ℕ) : ℝ)⁻¹ * (N b b : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : N a b = 0
    · simp [h]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have hrow : ∀ x, N a x = N b x := hright a b h
      rw [hrow b]
      congr 3
      exact Finset.sum_congr rfl fun x _ => hrow x
  have hrowb : ∑ x, N b x = ∑ x, if N x b ≠ 0 then N b b else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : N b x = 0
    · have h' : N x b = 0 := by
        by_contra h''
        exact hsymm x b h'' h
      simp [h, h']
    · have h' : N x b ≠ 0 := hsymm b x h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h')]
      exact (hleft b x h b).symm
  rw [hsum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hrowb, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    smul_eq_mul] at hb ⊢
  have hcard : ((Finset.univ.filter fun x => N x b ≠ 0).card : ℝ) ≠ 0 := by
    have : (Finset.univ.filter fun x => N x b ≠ 0).card ≠ 0 := fun h0 => hb (by simp [h0])
    exact_mod_cast this
  have hbb : (N b b : ℝ) ≠ 0 := by
    have : N b b ≠ 0 := fun h0 => hb (by simp [h0])
    exact_mod_cast this
  push_cast
  field_simp

section Parameters

variable {F : Type u} [Field F]
variable {P Q R M M' M'' : GroupScheme (Spec (CommRingCat.of F))}

/-- Composition of Weyl parameters: for `l' ≫ π' = 𝟙`, `(w'λ) ∘ (wλ)` is the parameter of the
composite conjugation `c ≫ c₀`. -/
theorem weylParameter_comp (l : M ⟶ P) (c₀ : M' ⟶ M) (π' : Q ⟶ M') (l' : M' ⟶ Q)
    (c : M'' ⟶ M') (π'' : R ⟶ M'') (h : l' ≫ π' = 𝟙 M') :
    (weylParameter (F := F) l' c π'').comp (weylParameter l c₀ π') =
      weylParameter l (c ≫ c₀) π'' := by
  refine TensorProduct.AlgebraTensorModule.ext fun s χ => ?_
  rw [LinearMap.comp_apply, weylParameter_tmul, weylParameter_tmul, weylParameter_tmul]
  congr 1
  rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
  congr 1
  simp only [Category.assoc, reassoc_of% h]

variable {G : GroupScheme (Spec (CommRingCat.of F))}

theorem innerIso_mul_inv (w w₀ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    (G.innerIso (w * w₀)).inv = (G.innerIso w).inv ≫ (G.innerIso w₀).inv := by
  rw [← cancel_epi (G.innerIso (w * w₀)).hom, Iso.hom_inv_id, G.innerIso_mul_hom]
  simp

theorem innerIso_inv_point_inv (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    (G.innerIso w⁻¹).inv = (G.innerIso w).hom := by
  rw [← cancel_epi (G.innerIso w⁻¹).hom, Iso.hom_inv_id, G.innerIso_inv_hom, Iso.inv_hom_id]

namespace IsWeylConjugation

variable {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {l' : M' ⟶ Q} {r : R ⟶ G} {l'' : M'' ⟶ R}
  {w₀ w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₀ : M' ⟶ M} {c : M'' ⟶ M'}

/-- Composition of Weyl conjugations: `w₀ M w₀⁻¹ = M'` and `w M' w⁻¹ = M''` give
`(w w₀) M (w w₀)⁻¹ = M''`. -/
theorem comp (h₀ : IsWeylConjugation p l q l' w₀ c₀) (h : IsWeylConjugation q l' r l'' w c) :
    IsWeylConjugation p l r l'' (w * w₀) (c ≫ c₀) where
  isIso := by
    have := h₀.isIso
    have := h.isIso
    infer_instance
  comp_eq := by
    rw [Category.assoc, h₀.comp_eq, reassoc_of% h.comp_eq, innerIso_mul_inv]

/-- Inverse of a Weyl conjugation: `w M w⁻¹ = M'` gives `w⁻¹ M' w = M`, presented by the inverse
isomorphism. -/
theorem exists_symm (h : IsWeylConjugation p l q l' w c₀) :
    ∃ c' : M ⟶ M', IsWeylConjugation q l' p l w⁻¹ c' ∧ c₀ ≫ c' = 𝟙 M' ∧ c' ≫ c₀ = 𝟙 M := by
  have := h.isIso
  refine ⟨inv c₀, ⟨inferInstance, ?_⟩, IsIso.hom_inv_id c₀, IsIso.inv_hom_id c₀⟩
  rw [innerIso_inv_point_inv, IsIso.inv_comp_eq, reassoc_of% h.comp_eq, Iso.inv_hom_id,
    Category.comp_id]

end IsWeylConjugation

section Sets

variable {Pa Pb Px Ma Mb Mx : GroupScheme (Spec (CommRingCat.of F))}
  {pa : Pa ⟶ G} {la : Ma ⟶ Pa} {πa : Pa ⟶ Ma}
  {pb : Pb ⟶ G} {lb : Mb ⟶ Pb} {πb : Pb ⟶ Mb}
  {px : Px ⟶ G} {lx : Mx ⟶ Px} {πx : Px ⟶ Mx}
  {w₀ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c₀ : Mb ⟶ Ma}

/-- Precomposition with an element of `Ω(Pa, Pb)` maps `Ω(Pb, Px)` to `Ω(Pa, Px)`. -/
theorem comp_mem_weylParameterSet_right (h₀ : IsWeylConjugation pa la pb lb w₀ c₀)
    (hb : lb ≫ πb = 𝟙 Mb) {s : ComplexCharacterParameter F Pb →ₗ[ℂ] ComplexCharacterParameter F Px}
    (hs : s ∈ weylParameterSet pb lb px lx πx) :
    s.comp (weylParameter la c₀ πb) ∈ weylParameterSet pa la px lx πx := by
  obtain ⟨w, c, hc, rfl⟩ := hs
  exact ⟨w * w₀, c ≫ c₀, h₀.comp hc, (weylParameter_comp la c₀ πb lb c πx hb).symm⟩

/-- Postcomposition with an element of `Ω(Pa, Pb)` maps `Ω(Px, Pa)` to `Ω(Px, Pb)`. -/
theorem comp_mem_weylParameterSet_left (h₀ : IsWeylConjugation pa la pb lb w₀ c₀)
    (ha : la ≫ πa = 𝟙 Ma) {s : ComplexCharacterParameter F Px →ₗ[ℂ] ComplexCharacterParameter F Pa}
    (hs : s ∈ weylParameterSet px lx pa la πa) :
    (weylParameter la c₀ πb).comp s ∈ weylParameterSet px lx pb lb πb := by
  obtain ⟨w, c, hc, rfl⟩ := hs
  exact ⟨w₀ * w, c₀ ≫ c, hc.comp h₀, (weylParameter_comp lx c πa la c₀ πb ha).symm⟩

/-- For `Pa` associate to `Pb`, `|Ω(Pb, Px)| ≤ |Ω(Pa, Px)|`. -/
theorem card_weylParameterSet_le_right (h₀ : IsWeylConjugation pa la pb lb w₀ c₀)
    (ha : la ≫ πa = 𝟙 Ma) (hb : lb ≫ πb = 𝟙 Mb)
    (hfin : (weylParameterSet pa la px lx πx).Finite) :
    Nat.card (weylParameterSet pb lb px lx πx) ≤ Nat.card (weylParameterSet pa la px lx πx) := by
  obtain ⟨c₁, -, h01, -⟩ := h₀.exists_symm
  have hfin' : Finite (weylParameterSet pa la px lx πx) := hfin.to_subtype
  have key : ∀ s ∈ weylParameterSet pb lb px lx πx,
      (s.comp (weylParameter la c₀ πb)).comp (weylParameter lb c₁ πa) = s := by
    rintro s ⟨w, c, -, rfl⟩
    rw [LinearMap.comp_assoc, weylParameter_comp lb c₁ πa la c₀ πb ha, h01,
      weylParameter_comp lb (𝟙 Mb) πb lb c πx hb, Category.comp_id]
  refine Nat.card_le_card_of_injective
    (fun s => ⟨s.1.comp (weylParameter la c₀ πb),
      comp_mem_weylParameterSet_right h₀ hb s.2⟩) ?_
  intro s s' hss'
  have h := congrArg (fun z : weylParameterSet pa la px lx πx =>
    (z.1).comp (weylParameter lb c₁ πa)) hss'
  simp only at h
  rw [key s.1 s.2, key s'.1 s'.2] at h
  exact Subtype.ext h

/-- For `Pa` associate to `Pb`, `|Ω(Px, Pa)| ≤ |Ω(Px, Pb)|`. -/
theorem card_weylParameterSet_le_left (h₀ : IsWeylConjugation pa la pb lb w₀ c₀)
    (ha : la ≫ πa = 𝟙 Ma) (hb : lb ≫ πb = 𝟙 Mb)
    (hfin : (weylParameterSet px lx pb lb πb).Finite) :
    Nat.card (weylParameterSet px lx pa la πa) ≤ Nat.card (weylParameterSet px lx pb lb πb) := by
  obtain ⟨c₁, -, -, h10⟩ := h₀.exists_symm
  have hfin' : Finite (weylParameterSet px lx pb lb πb) := hfin.to_subtype
  have key : ∀ s ∈ weylParameterSet px lx pa la πa,
      (weylParameter lb c₁ πa).comp ((weylParameter la c₀ πb).comp s) = s := by
    rintro s ⟨w, c, -, rfl⟩
    rw [← LinearMap.comp_assoc, weylParameter_comp la c₀ πb lb c₁ πa hb, h10,
      weylParameter_comp lx c πa la (𝟙 Ma) πa ha, Category.id_comp]
  refine Nat.card_le_card_of_injective
    (fun s => ⟨(weylParameter la c₀ πb).comp s.1,
      comp_mem_weylParameterSet_left h₀ ha s.2⟩) ?_
  intro s s' hss'
  have h := congrArg (fun z : weylParameterSet px lx pb lb πb =>
    (weylParameter lb c₁ πa).comp z.1) hss'
  simp only at h
  rw [key s.1 s.2, key s'.1 s'.2] at h
  exact Subtype.ext h

end Sets

section Family

variable {I : Type*} {P M : I → GroupScheme (Spec (CommRingCat.of F))}
  (p : ∀ i, P i ⟶ G) (l : ∀ i, M i ⟶ P i) (π : ∀ i, P i ⟶ M i)
  (T : I → I → Type*) [∀ i i', Fintype (T i i')]
  (w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
  (cw : ∀ i i', T i i' → (M i' ⟶ M i))

/-- An enumeration `T` of `Ω(P i, P i')` by Weyl conjugations has `|T| = |Ω(P i, P i')|`. -/
theorem card_eq_natCard_weylParameterSet
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    (hinj : ∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i')))
    (hsurj : ∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
      ∃ t, weylParameter (l i) (cw i i' t) (π i') = s) (i i' : I) :
    Fintype.card (T i i') = Nat.card (weylParameterSet (p i) (l i) (p i') (l i') (π i')) := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective
    (fun t => ⟨weylParameter (l i) (cw i i' t) (π i'), w i i' t, cw i i' t, hW i i' t, rfl⟩)
    ⟨fun t t' h => hinj i i' (congrArg Subtype.val h), fun s => ?_⟩
  obtain ⟨t, ht⟩ := hsurj i i' s.1 s.2
  exact ⟨t, Subtype.ext ht⟩

/-- The counting identity `∑ i, (n_P i)⁻¹ |Ω(P i, P i')| = 1` for every member `i'` with
`n_P i' = ∑ i'', |Ω(P i', P i'')| ≠ 0`, the sets `Ω` being enumerated by `T`. -/
theorem sum_inv_card_mul_card_eq_one [Fintype I] (hπ : ∀ i, l i ≫ π i = 𝟙 (M i))
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    (hinj : ∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i')))
    (hsurj : ∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
      ∃ t, weylParameter (l i) (cw i i' t) (π i') = s)
    (i' : I) (h : ∑ i'', Fintype.card (T i' i'') ≠ 0) :
    ∑ i, ((∑ i'', Fintype.card (T i i'') : ℕ) : ℝ)⁻¹ * (Fintype.card (T i i') : ℝ) = 1 := by
  have hcard := card_eq_natCard_weylParameterSet p l π T w cw hW hinj hsurj
  have hfin : ∀ a b, (weylParameterSet (p a) (l a) (p b) (l b) (π b)).Finite := by
    intro a b
    refine (Set.finite_range fun t : T a b => weylParameter (l a) (cw a b t) (π b)).subset ?_
    intro s hs
    obtain ⟨t, ht⟩ := hsurj a b s hs
    exact ⟨t, ht⟩
  have hne : ∀ a b, Fintype.card (T a b) ≠ 0 → Nonempty (T a b) := fun a b h =>
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
  refine sum_inv_rowSum_mul_eq_one (fun a b => Fintype.card (T a b)) ?_ ?_ ?_ i' h
  · intro a b hab
    obtain ⟨t⟩ := hne a b hab
    obtain ⟨c', hc', -, -⟩ := (hW a b t).exists_symm
    obtain ⟨t', -⟩ := hsurj b a _ ⟨_, c', hc', rfl⟩
    exact (Fintype.card_pos_iff.mpr ⟨t'⟩).ne'
  · intro a b hab x
    obtain ⟨t⟩ := hne a b hab
    obtain ⟨c', hc', -, -⟩ := (hW a b t).exists_symm
    simp only [hcard]
    exact le_antisymm (card_weylParameterSet_le_right hc' (hπ b) (hπ a) (hfin b x))
      (card_weylParameterSet_le_right (hW a b t) (hπ a) (hπ b) (hfin a x))
  · intro a b hab x
    obtain ⟨t⟩ := hne a b hab
    simp only [hcard]
    obtain ⟨c', hc', -, -⟩ := (hW a b t).exists_symm
    exact le_antisymm (card_weylParameterSet_le_left (hW a b t) (hπ a) (hπ b) (hfin x b))
      (card_weylParameterSet_le_left hc' (hπ b) (hπ a) (hfin x a))

end Family

end Parameters

end Langlands.Global.AdelicGroupPoints
