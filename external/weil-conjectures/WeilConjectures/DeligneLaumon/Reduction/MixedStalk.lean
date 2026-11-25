/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.AffineCurve
public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Local Frobenius eigenvalues of mixed Weil sheaves

A Weil sheaf which is `ι`-mixed of weights at most `w` has weights at most `w` at every closed
point: every eigenvalue `α` of its local Frobenius at a closed point `x` satisfies
`|ι α| ≤ q_x ^ (w / 2)`. The stalk functors are exact
(`AlgebraicGeometry.WeilSheaf.range_stalkAtMap_eq_ker`), so the stalk of the middle term of a
short exact sequence is an extension of Frobenius modules, whose weights are bounded by those of
the sub and of the quotient (`FrobeniusModule.HasWeightsAtMost.of_exact`); induction along the
filtration gives the bound.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.hasWeightsAtMost`: a sheaf mixed of weights
  at most `w` has weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Along a finite filtration `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G n` whose successive quotients have stalks
at `s` of weights at most `w`, every `G i` has stalk at `s` of weights at most `w`. -/
theorem stalkAt_hasWeightsAtMost_of_filtration {ι : PadicAlgCl l →+* ℂ} {q : ℕ} {w : ℝ}
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    {n : ℕ} (G : Fin (n + 1) → WeilSheaf k₀ l X) (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ)
    (h0 : IsZero (G 0)) (hmono : ∀ i, Mono (φ i))
    (h : ∀ i : Fin n, ((cokernel (φ i)).stalkAt s m hs).HasWeightsAtMost ι q w) :
    ∀ (i : ℕ) (hi : i < n + 1), ((G ⟨i, hi⟩).stalkAt s m hs).HasWeightsAtMost ι q w := by
  intro i
  induction i with
  | zero =>
    intro hi α hα
    exfalso
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    have : Subsingleton ((G ⟨0, hi⟩).stalkAt s m hs).carrier :=
      ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
        ((stalkFunctor k₀ l s).map_isZero (X := G ⟨0, hi⟩) h0))
    exact hv.2 (Subsingleton.elim _ _)
  | succ i ih =>
    intro hi
    let j : Fin n := ⟨i, by omega⟩
    have := hmono j
    exact FrobeniusModule.HasWeightsAtMost.of_exact (stalkAtMap s m hs (φ j))
      (stalkAtMap_frobenius s m hs _) (stalkAtMap s m hs (cokernel.π (φ j)))
      (stalkAtMap_frobenius s m hs _) (injective_stalkAtMap s m hs _)
      (range_stalkAtMap_eq_ker (ShortComplex.exact_cokernel (φ j)) s m hs) (ih j.castSucc.2) (h j)

/-- A Weil sheaf which is `ι`-mixed of weights at most `w` has weights at most `w`: at every
closed point `x`, every eigenvalue `α` of the local Frobenius satisfies `|ι α| ≤ q_x ^ (w / 2)`.
The stalk functors being exact, this follows by induction along the filtration from the bounds
for its punctually pure quotients (blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.hasWeightsAtMost {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsMixedOfWeightsAtMost ι w) : F.HasWeightsAtMost ι w := by
  intro x
  obtain ⟨n, G, φ, h0, ⟨e⟩, hmono, hpure⟩ := h
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  have hq : 1 ≤ (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 :=
    Nat.one_le_pow _ _ Nat.card_pos
  have hquot (i : Fin n) : ((cokernel (φ i)).stalkAt _ _ hs).HasWeightsAtMost ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w := by
    obtain ⟨v, hv, hpv⟩ := hpure i
    exact (hpv x).hasWeightsAtMost.mono hq hv
  have hlast : ((G (Fin.last n)).stalkAt _ _ hs).HasWeightsAtMost ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w :=
    stalkAt_hasWeightsAtMost_of_filtration _ _ hs G φ h0 hmono hquot n n.lt_succ_self
  have hF : (F.stalkAt _ _ hs).HasWeightsAtMost ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w :=
    FrobeniusModule.HasWeightsAtMost.of_injective (stalkAtMap _ _ hs e.inv)
      (stalkAtMap_frobenius _ _ hs _) (injective_stalkAtMap _ _ hs _) hlast
  exact hF

end AlgebraicGeometry.WeilSheaf
