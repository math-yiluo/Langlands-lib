import Langlands.Representation.Archimedean.RealStandardEllipticCartanReduction
import Langlands.Representation.Archimedean.RealStandardEllipticCartanRegular

/-! # Elliptic Cartan comparison from support and evaluation -/

noncomputable section

set_option autoImplicit false

open Set

namespace Langlands.Archimedean.RealStandardEllipticCartan

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- The logarithmic absolute value of a complex or real Cartan slot. -/
def coordinateRadius {r s : ℕ} (x : Coordinates r s) : Fin r ⊕ Fin s → ℝ :=
  Sum.elim (fun i => (x.1 i).toAdd.1) (fun j => (x.2 j).toAdd.1)

/-- Coordinates with distinct radii across all slots and nonreal eigenvalues in each
complex slot. -/
def separatedRegularCoordinates (r s : ℕ) : Set (Coordinates r s) :=
  {x | Function.Injective (coordinateRadius x) ∧ ∀ i, Real.sin (x.1 i).toAdd.2 ≠ 0}

/-- The cross inequalities between complex and real radii preserve density. -/
theorem dense_separatedRegularCoordinates (r s : ℕ) :
    Dense (separatedRegularCoordinates r s) := by
  let U (ij : Fin r × Fin s) : Set (Coordinates r s) :=
    {x | (x.1 ij.1).toAdd.1 ≠ (x.2 ij.2).toAdd.1}
  have ho (ij : Fin r × Fin s) : IsOpen (U ij) :=
    isOpen_ne_fun
      (continuous_fst.comp ((continuous_apply ij.1).comp continuous_fst))
      (continuous_fst.comp ((continuous_apply ij.2).comp continuous_snd))
  have hd (ij : Fin r × Fin s) : Dense (U ij) := by
    obtain ⟨i, j⟩ := ij
    rw [dense_iff_inter_open]
    rintro V hV ⟨x, hx⟩
    let f (t : ℝ) : Coordinates r s :=
      (Function.update x.1 i (Multiplicative.ofAdd (t, (x.1 i).toAdd.2)), x.2)
    have hf : Continuous f :=
      (continuous_const.update i (continuous_id.prodMk continuous_const)).prodMk continuous_const
    have hfx : f (x.1 i).toAdd.1 = x := by simp [f, Function.update_eq_self]
    have hmem : (x.1 i).toAdd.1 ∈ f ⁻¹' V := by simpa only [mem_preimage, hfx] using hx
    obtain ⟨t, ht, htV⟩ := (dense_compl_singleton (x.2 j).toAdd.1).exists_mem_open
      (hV.preimage hf) ⟨_, hmem⟩
    exact ⟨f t, htV, by simpa [U, f] using ht⟩
  have hcross : Dense (⋂ ij, U ij) := by
    rw [← sInter_range]
    exact (Set.toFinite _).dense_sInter (fun _ ⟨ij, h⟩ => h ▸ ho ij)
      (fun _ ⟨ij, h⟩ => h ▸ hd ij)
  refine ((dense_regularCoordinates r s).inter_of_isOpen_right hcross
    (isOpen_iInter_of_finite ho)).mono ?_
  rintro x ⟨⟨hr, hs, hθ⟩, hx⟩
  refine ⟨?_, hθ⟩
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (hr hij)
    | inr j => exact ((mem_iInter.mp hx (i, j)) hij).elim
  | inr i =>
    cases j with
    | inl j => exact ((mem_iInter.mp hx (j, i)) hij.symm).elim
    | inr j => exact congrArg Sum.inr (hs hij)

/-- Positive induced weights give a nonzero evaluation even with all radii distinct. -/
theorem exists_separated_numerator_ne_zero {r s : ℕ} {p : Parameters r s}
    (hp : ∀ i, 0 < (p.1 i).1) :
    ∃ x ∈ separatedRegularCoordinates r s, numerator p x ≠ 0 := by
  obtain ⟨x, _, hx⟩ := exists_regular_numerator_ne_zero hp
  exact (dense_separatedRegularCoordinates r s).exists_mem_open
    (isOpen_ne_fun (continuous_numerator p) continuous_const) ⟨x, hx⟩

private theorem exists_block_lists (xs : List RealBlock) :
    ∃ (ds : List ComplexCharacterData) (cs : List RealCharacterData),
      xs.Perm (ds.map RealBlock.induced ++ cs.map RealBlock.character) := by
  induction xs with
  | nil => exact ⟨[], [], .nil⟩
  | cons a xs ih =>
    obtain ⟨ds, cs, hp⟩ := ih
    cases a with
    | character c => exact ⟨ds, c :: cs, (hp.cons _).trans List.perm_middle.symm⟩
    | induced d => exact ⟨d :: ds, cs, hp.cons _⟩

/-- Every real block list has separate enumerations of its induced and character blocks. -/
theorem exists_ofBlockData_perm (xs : List RealBlock) :
    ∃ (r s : ℕ) (d : Fin r → ComplexCharacterData) (c : Fin s → RealCharacterData),
      xs.Perm (ofBlockData d c) := by
  obtain ⟨ds, cs, hp⟩ := exists_block_lists xs
  exact ⟨ds.length, cs.length, ds.get, cs.get, by simpa only [ofBlockData, List.ofFn_get] using hp⟩

/-- The rank of a real block list in terms of its two enumeration sizes. -/
theorem realRank_ofBlockData {r s : ℕ} (d : Fin r → ComplexCharacterData)
    (c : Fin s → RealCharacterData) : realRank (ofBlockData d c) = 2 * r + s := by
  simp [ofBlockData, realRank, List.sum_append, Function.comp_def, RealBlock.rank,
    Nat.mul_comm]

private theorem weight_pos_ofBlockData {r s : ℕ} {d : Fin r → ComplexCharacterData}
    {c : Fin s → RealCharacterData} {xs : List RealBlock} (hp : xs.Perm (ofBlockData d c))
    (hw : ∀ a : ComplexCharacterData, .induced a ∈ xs → 0 < a.weight) (i : Fin r) :
    0 < (d i).weight := by
  apply hw
  exact hp.mem_iff.mpr (List.mem_append_left _ (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)))

/-- Scalar evaluations of the actual modules on the separated regular Cartan coordinates,
with intertwiner invariance, support and the formula at maximal elliptic rank. -/
def RealStandardEllipticCartanEvaluationStatement : Prop :=
  ∃ (A : ∀ {n r s : ℕ}, 2 * r + s = n → List RealBlock → Coordinates r s → ℂ)
    (c : ∀ r s : ℕ, Coordinates r s → ℂ),
    (∀ (r s : ℕ) (x : Coordinates r s), x ∈ separatedRegularCoordinates r s → c r s x ≠ 0) ∧
    (∀ (n : ℕ) (ds es : List RealBlock), realRank ds = n → realRank es = n →
      ∀ T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
          kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
        IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
        Function.Bijective T →
        ∀ {r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s),
          x ∈ separatedRegularCoordinates r s → A h ds x = A h es x) ∧
    (∀ {n r s r' s' : ℕ} {ds : List RealBlock}
      {d : Fin r' → ComplexCharacterData} {b : Fin s' → RealCharacterData},
      ∀ (h : 2 * r + s = n), realRank ds = n → ds.Perm (ofBlockData d b) →
        (∀ i, 0 < (d i).weight) → r' < r →
        ∀ x : Coordinates r s, x ∈ separatedRegularCoordinates r s → A h ds x = 0) ∧
    (∀ {n r s : ℕ} {ds : List RealBlock}
      {d : Fin r → ComplexCharacterData} {b : Fin s → RealCharacterData},
      ∀ (h : 2 * r + s = n), realRank ds = n → ds.Perm (ofBlockData d b) →
        (∀ i, 0 < (d i).weight) →
        ∀ x : Coordinates r s, x ∈ separatedRegularCoordinates r s →
          A h ds x = c r s x * numerator (blockParameters d b) x)

/-- The support and maximal-rank evaluation clauses imply the exact elliptic Cartan
comparison. -/
theorem realStandardEllipticCartanComparison_of_evaluation
    (heval : RealStandardEllipticCartanEvaluationStatement) :
    RealStandardEllipticCartanComparisonStatement := by
  obtain ⟨A, C, hC, hinv, hvanish, htop⟩ := heval
  intro n ds es hn hm hd he _ _ T hT hbij
  obtain ⟨r, s, d, c, hdp⟩ := exists_ofBlockData_perm ds
  obtain ⟨r', s', e, b, hep⟩ := exists_ofBlockData_perm es
  have hdn : 2 * r + s = n := (realRank_ofBlockData d c).symm.trans
    ((hdp.map RealBlock.rank).sum_eq.symm.trans hn)
  have hen : 2 * r' + s' = n := (realRank_ofBlockData e b).symm.trans
    ((hep.map RealBlock.rank).sum_eq.symm.trans hm)
  have hd' := weight_pos_ofBlockData hdp hd
  have he' := weight_pos_ofBlockData hep he
  have hle : r ≤ r' := by
    by_contra! hlt
    obtain ⟨x, hx, hnum⟩ := exists_separated_numerator_ne_zero (p := blockParameters d c) hd'
    have h := hinv n ds es hn hm T hT hbij hdn x hx
    rw [htop hdn hn hdp hd' x hx, hvanish hdn hm hep he' hlt x hx] at h
    exact (mul_ne_zero (hC r s x hx) hnum) h
  have hge : r' ≤ r := by
    by_contra! hlt
    obtain ⟨x, hx, hnum⟩ := exists_separated_numerator_ne_zero (p := blockParameters e b) he'
    have h := hinv n ds es hn hm T hT hbij hen x hx
    rw [hvanish hen hn hdp hd' hlt x hx, htop hen hm hep he' x hx] at h
    exact (mul_ne_zero (hC r' s' x hx) hnum) h.symm
  have hr : r = r' := le_antisymm hle hge
  subst r'
  have hs : s = s' := by omega
  subst s'
  refine ⟨r, s, d, e, c, b, hdp, hep, ?_⟩
  apply Continuous.ext_on (dense_separatedRegularCoordinates r s)
    (continuous_numerator _) (continuous_numerator _)
  intro x hx
  have h := hinv n ds es hn hm T hT hbij hdn x hx
  rw [htop hdn hn hdp hd' x hx, htop hdn hm hep he' x hx] at h
  exact mul_left_cancel₀ (hC r s x hx) h

end Langlands.Archimedean.RealStandardEllipticCartan
