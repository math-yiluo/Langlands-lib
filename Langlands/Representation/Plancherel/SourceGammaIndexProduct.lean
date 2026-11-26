import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

/-! # Relative indices of split compact traces -/

namespace Langlands.Plancherel.SourceGammaIndexProduct

open MulAction

variable {A : Type*} [Group A]

/-- If every element of the group is `t * y` with `t ∈ T` and `y ∈ Y`, then
`[T : T ∩ Y] = [A : Y]`. -/
theorem relIndex_eq_index_of_forall_mul (Y T : Subgroup A)
    (h : ∀ z : A, ∃ t ∈ T, ∃ y ∈ Y, z = t * y) :
    Y.relIndex T = Y.index := by
  have htrans : IsPretransitive T (A ⧸ Y) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    obtain ⟨t₁, ht₁, y₁, hy₁, rfl⟩ := h b
    obtain ⟨t₂, ht₂, y₂, hy₂, rfl⟩ := h a
    refine ⟨⟨t₁ * t₂⁻¹, T.mul_mem ht₁ (T.inv_mem ht₂)⟩, ?_⟩
    change (((t₁ * t₂⁻¹ : A) * (t₂ * y₂) : A) : A ⧸ Y) = ((t₁ * y₁ : A) : A ⧸ Y)
    rw [QuotientGroup.eq]
    have e : (t₁ * t₂⁻¹ * (t₂ * y₂))⁻¹ * (t₁ * y₁) = y₂⁻¹ * y₁ := by group
    rw [e]
    exact Y.mul_mem (Y.inv_mem hy₂) hy₁
  have hstab : stabilizer T ((1 : A) : A ⧸ Y) = Y.subgroupOf T := by
    ext t
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (((t : A) * 1 : A) : A ⧸ Y) = ((1 : A) : A ⧸ Y) ↔ _
    rw [QuotientGroup.eq]
    simp
  rw [Subgroup.relIndex, ← hstab, index_stabilizer_of_transitive, Subgroup.index_eq_card]

/-- If every element of `Z` is `t * y` with `t ∈ T` and `y ∈ Y`, then
`[T : T ∩ Y] = [Z : Y]`. -/
theorem relIndex_eq_of_forall_mem_mul {Y T Z : Subgroup A} (hYZ : Y ≤ Z) (hTZ : T ≤ Z)
    (h : ∀ z ∈ Z, ∃ t ∈ T, ∃ y ∈ Y, z = t * y) :
    Y.relIndex T = Y.relIndex Z := by
  rw [← Subgroup.relIndex_subgroupOf hTZ]
  apply relIndex_eq_index_of_forall_mul
  rintro ⟨z, hz⟩
  obtain ⟨t, ht, y, hy, e⟩ := h z hz
  exact ⟨⟨t, hTZ ht⟩, ht, ⟨y, hYZ hy⟩, hy, Subtype.ext e⟩


/-- Relative indices only see the intersection with the larger group. -/
theorem relIndex_congr_inf {Y Y' T : Subgroup A} (h : Y ⊓ T = Y' ⊓ T) :
    Y.relIndex T = Y'.relIndex T := by
  rw [← Subgroup.inf_relIndex_right Y T, h, Subgroup.inf_relIndex_right]

/-- **Indices of split traces.** Let `X = Bs ⋉ N` inside a group, with `N` normalized
by `X` and `Bs ∩ N = 1`. If two subgroups `H ≤ K` have traces on `X` that are the
products of their traces on `Bs` and on `N`, then the relative index of the traces on
`X` is the product of the relative indices of the traces on `Bs` and on `N`. -/
theorem relIndex_inf_eq_mul {X Bs N K H : Subgroup A}
    (hNX : N ≤ X) (hBX : Bs ≤ X) (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hBN : ∀ b ∈ Bs, b ∈ N → b = 1) (hHK : H ≤ K)
    (hK : ∀ x ∈ K ⊓ X, ∃ b ∈ K ⊓ Bs, ∃ n ∈ K ⊓ N, x = b * n)
    (hH : ∀ x ∈ H ⊓ X, ∃ b ∈ H ⊓ Bs, ∃ n ∈ H ⊓ N, x = b * n) :
    (H ⊓ X).relIndex (K ⊓ X) = (H ⊓ Bs).relIndex (K ⊓ Bs) * (H ⊓ N).relIndex (K ⊓ N) := by
  have hconj : ∀ b ∈ H ⊓ Bs, ∀ n ∈ K ⊓ N, b * n * b⁻¹ ∈ K ⊓ N := by
    intro b hb n hn
    have hbK : b ∈ K := hHK (Subgroup.mem_inf.mp hb).1
    exact Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hbK (Subgroup.mem_inf.mp hn).1)
      (K.inv_mem hbK), hnorm b (hBX (Subgroup.mem_inf.mp hb).2) n (Subgroup.mem_inf.mp hn).2⟩
  let Z : Subgroup A :=
    { carrier := {x | ∃ b ∈ H ⊓ Bs, ∃ n ∈ K ⊓ N, x = b * n}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, n, hn, rfl⟩ ⟨b', hb', n', hn', rfl⟩
        refine ⟨b * b', mul_mem hb hb', b'⁻¹ * n * b'⁻¹⁻¹ * n', mul_mem ?_ hn', by group⟩
        exact hconj b'⁻¹ (inv_mem hb') n hn
      inv_mem' := by
        rintro _ ⟨b, hb, n, hn, rfl⟩
        exact ⟨b⁻¹, inv_mem hb, b * n⁻¹ * b⁻¹, hconj b hb n⁻¹ (inv_mem hn), by group⟩ }
  have hZ : ∀ x, x ∈ Z ↔ ∃ b ∈ H ⊓ Bs, ∃ n ∈ K ⊓ N, x = b * n := fun _ => Iff.rfl
  have hYZ : H ⊓ X ≤ Z := by
    intro x hx
    obtain ⟨b, hb, n, hn, rfl⟩ := hH x hx
    exact (hZ _).2 ⟨b, hb, n, Subgroup.mem_inf.mpr ⟨hHK (Subgroup.mem_inf.mp hn).1,
      (Subgroup.mem_inf.mp hn).2⟩, rfl⟩
  have hZX : Z ≤ K ⊓ X := by
    intro x hx
    obtain ⟨b, hb, n, hn, rfl⟩ := (hZ x).1 hx
    exact Subgroup.mem_inf.mpr ⟨K.mul_mem (hHK (Subgroup.mem_inf.mp hb).1)
      (Subgroup.mem_inf.mp hn).1, X.mul_mem (hBX (Subgroup.mem_inf.mp hb).2)
      (hNX (Subgroup.mem_inf.mp hn).2)⟩
  have hNZ : K ⊓ N ≤ Z := fun n hn => (hZ n).2 ⟨1, one_mem _, n, hn, (one_mul n).symm⟩
  have hBZ : K ⊓ Bs ≤ K ⊓ X := fun b hb =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).1, hBX (Subgroup.mem_inf.mp hb).2⟩
  have h1 : (H ⊓ X).relIndex Z = (H ⊓ N).relIndex (K ⊓ N) := by
    rw [← relIndex_eq_of_forall_mem_mul hYZ hNZ]
    · apply relIndex_congr_inf
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨hxH, -⟩, hxK, hxN⟩
        exact ⟨⟨hxH, hxN⟩, hxK, hxN⟩
      · rintro ⟨⟨hxH, -⟩, hxK, hxN⟩
        exact ⟨⟨hxH, hNX hxN⟩, hxK, hxN⟩
    · intro z hz
      obtain ⟨b, hb, n, hn, rfl⟩ := (hZ z).1 hz
      refine ⟨b * n * b⁻¹, hconj b hb n hn, b, Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_inf.mp hb).1, hBX (Subgroup.mem_inf.mp hb).2⟩, by group⟩
  have h2 : Z.relIndex (K ⊓ X) = (H ⊓ Bs).relIndex (K ⊓ Bs) := by
    rw [← relIndex_eq_of_forall_mem_mul hZX hBZ]
    · apply relIndex_congr_inf
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨hxZ, hxK, hxB⟩
        obtain ⟨b, hb, n, hn, rfl⟩ := (hZ x).1 hxZ
        have hn1 : n = 1 := hBN n (by
          have : n = b⁻¹ * (b * n) := by group
          rw [this]
          exact Bs.mul_mem (Bs.inv_mem (Subgroup.mem_inf.mp hb).2) hxB)
          (Subgroup.mem_inf.mp hn).2
        subst hn1
        rw [mul_one] at hxK hxB ⊢
        exact ⟨Subgroup.mem_inf.mp hb, hxK, hxB⟩
      · rintro ⟨⟨hxH, hxB⟩, hxK, -⟩
        exact ⟨(hZ x).2 ⟨x, Subgroup.mem_inf.mpr ⟨hxH, hxB⟩, 1, one_mem _, (mul_one x).symm⟩,
          hxK, hxB⟩
    · intro x hx
      obtain ⟨b, hb, n, hn, rfl⟩ := hK x hx
      exact ⟨b, hb, n, hNZ hn, rfl⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hYZ hZX, h1, h2, mul_comm]


/-- The trace of `Y` on `X` is the product of its traces on `X ⊓ L` and on `N`. -/
def SplitTrace (Y X L N : Subgroup A) : Prop :=
  ∀ x ∈ Y ⊓ X, ∃ b ∈ Y ⊓ (X ⊓ L), ∃ n ∈ Y ⊓ N, x = b * n

/-- **Wall crossing for radical indices.** Suppose `U = (U ⊓ L) ⋉ N`, `U' = (U' ⊓ L) ⋉ N`,
`V = (V ⊓ L) ⋉ N'` and `V' = (V' ⊓ L) ⋉ N'`, where `U ⊓ L = V' ⊓ L` and
`V ⊓ L = U' ⊓ L`. If the traces of `H ≤ K` on these four groups split, then the
products of the radical indices for `(U, V)` and for `(U', V')` agree. -/
theorem relIndex_mul_eq_of_wall {L N N' U V U' V' K H : Subgroup A} (hHK : H ≤ K)
    (hNU : N ≤ U) (hNU' : N ≤ U') (hN'V : N' ≤ V) (hN'V' : N' ≤ V')
    (hnU : ∀ x ∈ U, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hnU' : ∀ x ∈ U', ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hnV : ∀ x ∈ V, ∀ n ∈ N', x * n * x⁻¹ ∈ N')
    (hnV' : ∀ x ∈ V', ∀ n ∈ N', x * n * x⁻¹ ∈ N')
    (hLN : ∀ l ∈ L, l ∈ N → l = 1) (hLN' : ∀ l ∈ L, l ∈ N' → l = 1)
    (hB : U ⊓ L = V' ⊓ L) (hC : V ⊓ L = U' ⊓ L)
    (hKU : SplitTrace K U L N) (hHU : SplitTrace H U L N)
    (hKU' : SplitTrace K U' L N) (hHU' : SplitTrace H U' L N)
    (hKV : SplitTrace K V L N') (hHV : SplitTrace H V L N')
    (hKV' : SplitTrace K V' L N') (hHV' : SplitTrace H V' L N') :
    (H ⊓ U).relIndex (K ⊓ U) * (H ⊓ V).relIndex (K ⊓ V) =
      (H ⊓ U').relIndex (K ⊓ U') * (H ⊓ V').relIndex (K ⊓ V') := by
  have key : ∀ {X M : Subgroup A}, M ≤ X → (∀ x ∈ X, ∀ n ∈ M, x * n * x⁻¹ ∈ M) →
      (∀ l ∈ L, l ∈ M → l = 1) → SplitTrace K X L M → SplitTrace H X L M →
      (H ⊓ X).relIndex (K ⊓ X) =
        (H ⊓ (X ⊓ L)).relIndex (K ⊓ (X ⊓ L)) * (H ⊓ M).relIndex (K ⊓ M) := by
    intro X M hMX hnX hLM hK hH
    exact relIndex_inf_eq_mul hMX inf_le_left hnX
      (fun b hb hbM => hLM b (Subgroup.mem_inf.mp hb).2 hbM) hHK hK hH
  rw [key hNU hnU hLN hKU hHU, key hN'V hnV hLN' hKV hHV, key hNU' hnU' hLN hKU' hHU',
    key hN'V' hnV' hLN' hKV' hHV', hB, hC]
  ring

end Langlands.Plancherel.SourceGammaIndexProduct
