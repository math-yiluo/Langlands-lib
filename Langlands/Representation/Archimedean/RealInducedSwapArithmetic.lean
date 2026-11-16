import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-!
# Arithmetic and parameter transport for two induced real blocks

These are internal consequences of the published definitions. They do not assume a swap
theorem or an irreducibility criterion.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedSwapArithmetic

/-- The parameters visible to an induced real standard-module block: absolute weight and
complex exponent. The original sign of the complex character's weight is forgotten. -/
def inducedParameter (d : ComplexCharacterData) : ℕ × ℂ :=
  (d.weight.natAbs, d.exponent)

theorem inducedParameter_eq_iff {d e : ComplexCharacterData} :
    inducedParameter d = inducedParameter e ↔
      d.weight.natAbs = e.weight.natAbs ∧ d.exponent = e.exponent := by
  simp only [inducedParameter, Prod.mk.injEq]

/-- The two branches in Mœglin's linking condition for nonzero induced weights. -/
theorem unlinked_iff {d e : ComplexCharacterData} (hd : d.weight ≠ 0)
    (he : e.weight ≠ 0) :
    AreRealBlocksUnlinked (.induced d) (.induced e) ↔
      ∀ k : ℕ, 0 < k →
        d.exponent - e.exponent ≠
            ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℂ) / 2 + k) ∧
          e.exponent - d.exponent ≠
            ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℂ) / 2 + k) := by
  simp [AreRealBlocksUnlinked, realBlockMoeglinData, hd, he, MoeglinDatum.IsLinked,
    not_exists, not_and, not_or]

/-- With decreasing real parts, a nonnegative half-integer plus a positive integer cannot
occur as the difference in the reverse direction. -/
theorem reverse_difference_ne {s t : ℂ} {a k : ℕ} (horder : t.re ≤ s.re)
    (hk : 0 < k) : t - s ≠ (a : ℂ) / 2 + k := by
  intro h
  have hre : t.re - s.re = (a : ℝ) / 2 + k := by
    simpa using congrArg Complex.re h
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  linarith

/-- The exponent order removes the reverse branch from the exact unlinkedness test. -/
theorem unlinked_iff_of_order {d e : ComplexCharacterData} (hd : d.weight ≠ 0)
    (he : e.weight ≠ 0)
    (horder : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d)) :
    AreRealBlocksUnlinked (.induced d) (.induced e) ↔
      ∀ k : ℕ, 0 < k →
        d.exponent - e.exponent ≠
          ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℂ) / 2 + k) := by
  rw [unlinked_iff hd he]
  constructor
  · exact fun h k hk => (h k hk).1
  · intro h k hk
    exact ⟨h k hk, reverse_difference_ne horder hk⟩

/-- Unequal imaginary exponents exclude both branches of the linking condition. -/
theorem unlinked_of_im_ne {d e : ComplexCharacterData} (hd : d.weight ≠ 0)
    (he : e.weight ≠ 0) (him : d.exponent.im ≠ e.exponent.im) :
    AreRealBlocksUnlinked (.induced d) (.induced e) := by
  rw [unlinked_iff hd he]
  intro k hk
  constructor
  · intro h
    have him' : d.exponent.im - e.exponent.im = 0 := by
      simpa using congrArg Complex.im h
    exact him (sub_eq_zero.mp him')
  · intro h
    have him' : e.exponent.im - d.exponent.im = 0 := by
      simpa using congrArg Complex.im h
    exact him (sub_eq_zero.mp him').symm

/-- A difference smaller than the first possible positive linking value is unlinked. -/
theorem unlinked_of_gap_lt {d e : ComplexCharacterData} (hd : d.weight ≠ 0)
    (he : e.weight ≠ 0)
    (horder : realBlockExponent (.induced e) ≤ realBlockExponent (.induced d))
    (hgap : d.exponent.re - e.exponent.re <
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℝ) / 2 + 1)) :
    AreRealBlocksUnlinked (.induced d) (.induced e) := by
  rw [unlinked_iff_of_order hd he horder]
  intro k hk h
  have hre : d.exponent.re - e.exponent.re =
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℝ) / 2 + k) := by
    simpa using congrArg Complex.re h
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- The standard module only sees the absolute weights in its Fourier conditions. -/
theorem standardModule_eq_of_absolute_weights (n : ℕ) {ds es : List RealBlock}
    (hχ : ∀ p, realPositionCharacter ds p = realPositionCharacter es p)
    (hw : ∀ p, (realInducedBlockAt ds p).map (fun d => |d.weight|) =
      (realInducedBlockAt es p).map (fun d => |d.weight|)) :
    realStandardModule n ds = realStandardModule n es := by
  have hle : ∀ (ds es : List RealBlock),
      (∀ p, realPositionCharacter ds p = realPositionCharacter es p) →
      (∀ p, (realInducedBlockAt ds p).map (fun d => |d.weight|) =
        (realInducedBlockAt es p).map (fun d => |d.weight|)) →
      realStandardModule n ds ≤ realStandardModule n es := by
    intro ds es hχ hw f hf
    obtain ⟨hprincipal, hfourier⟩ := (mem_realStandardModule_iff n ds f).mp hf
    apply (mem_realStandardModule_iff n es f).mpr
    refine ⟨?_, ?_⟩
    · rwa [← funext hχ]
    · intro p d hd k hk g
      have hp := hw p
      rw [hd] at hp
      cases hds : realInducedBlockAt ds p with
      | none => simp [hds] at hp
      | some e =>
          have habs : |e.weight| = |d.weight| := by simpa [hds] using hp
          exact hfourier p e hds k (by rwa [habs]) g
  exact le_antisymm (hle ds es hχ hw)
    (hle es ds (fun p => (hχ p).symm) (fun p => (hw p).symm))

/-- Equal absolute weights and exponents allow replacement of an induced block inside
arbitrary surrounding blocks, by equality of the underlying spaces of functions. -/
theorem standardModule_replace_induced (n : ℕ) (pre post : List RealBlock)
    {d e : ComplexCharacterData} (hw : d.weight.natAbs = e.weight.natAbs)
    (ht : d.exponent = e.exponent) :
    realStandardModule n (pre ++ .induced d :: post) =
      realStandardModule n (pre ++ .induced e :: post) := by
  apply standardModule_eq_of_absolute_weights
  · apply realPositionCharacter_append_congr
    intro p
    rcases p with _ | _ | p
    · funext x
      simp [realPositionCharacter, realInducedFirstCharacter, hw, ht]
    · funext x
      simp [realPositionCharacter, realInducedSecondCharacter, hw, ht]
    · rfl
  · apply realInducedBlockAt_append_congr (R := fun a b =>
      a.map (fun d => |d.weight|) = b.map (fun d => |d.weight|)) (fun _ => rfl)
    intro p
    rcases p with _ | _ | p
    · simp only [realInducedBlockAt, Option.map_some, Option.some.injEq]
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs, hw]
    · rfl
    · rfl

/-- Swapping induced blocks with identical absolute weights and exponents is the identity
after transport along equal standard modules. -/
theorem swap_of_same_parameters (n : ℕ) (pre post : List RealBlock)
    {d e : ComplexCharacterData} (hw : d.weight.natAbs = e.weight.natAbs)
    (ht : d.exponent = e.exponent) :
    RealInjectiveIntertwinerExists n (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) := by
  apply (RealInjectiveIntertwinerExists.refl n
    (pre ++ .induced d :: .induced e :: post)).of_eq rfl
  calc
    realStandardModule n (pre ++ .induced d :: .induced e :: post) =
        realStandardModule n (pre ++ .induced e :: .induced e :: post) :=
      standardModule_replace_induced n pre (.induced e :: post) (d := d) (e := e) hw ht
    _ = realStandardModule n (pre ++ .induced e :: .induced d :: post) := by
      have h := standardModule_replace_induced n (pre ++ [.induced e]) post
        (d := e) (e := d) hw.symm ht.symm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        h

/-- Equality of the visible induced parameters preserves the standard module in every
surrounding list. -/
theorem standardModule_replace_of_parameter_eq (n : ℕ) (pre post : List RealBlock)
    {d e : ComplexCharacterData} (h : inducedParameter d = inducedParameter e) :
    realStandardModule n (pre ++ .induced d :: post) =
      realStandardModule n (pre ++ .induced e :: post) := by
  obtain ⟨hw, ht⟩ := inducedParameter_eq_iff.mp h
  exact standardModule_replace_induced n pre post hw ht

end RealInducedSwapArithmetic

end Langlands.Archimedean
