import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso

/-! # Alternating extension of ordered unit cocycles -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open CocycleGluing

variable {X : Scheme.{u}}

/-- Restriction of units along an inclusion of opens. -/
def resU {V W : X.Opens} (h : W ≤ V) : (Γ(X, V))ˣ →* (Γ(X, W))ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

lemma resU_val {V W : X.Opens} (h : W ≤ V) (u : (Γ(X, V))ˣ) :
    (resU h u : Γ(X, W)) = X.presheaf.map (homOfLE h).op (u : Γ(X, V)) := rfl

lemma resU_resU {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (u : (Γ(X, U))ˣ) :
    resU h' (resU h u) = resU (h'.trans h) u := by
  apply Units.ext
  rw [resU_val, resU_val, resU_val, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {ι : Type u} [LinearOrder ι] {T : ι → X.Opens}

/-- The alternating extension of a family of units given on ordered pairs: `H i j` for
`i < j`, `1` on the diagonal and the restricted inverse of `H j i` for `j < i`. -/
def altExt (H : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (i j : ι) : (Γ(X, T i ⊓ T j))ˣ :=
  if i < j then H i j else if i = j then 1 else
    resU (le_inf inf_le_right inf_le_left : T i ⊓ T j ≤ T j ⊓ T i) (H j i)⁻¹

lemma altExt_of_lt (H : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) {i j : ι} (h : i < j) :
    altExt H i j = H i j := by simp [altExt, h]

lemma altExt_self (H : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (i : ι) : altExt H i i = 1 := by
  simp [altExt]

lemma altExt_of_gt (H : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) {i j : ι} (h : j < i) :
    altExt H i j = resU (le_inf inf_le_right inf_le_left : T i ⊓ T j ≤ T j ⊓ T i) (H j i)⁻¹ := by
  simp [altExt, not_lt_of_gt h, ne_of_gt h]

/-- On any open inside `T i ⊓ T j`, the alternating extension is antisymmetric. -/
lemma resU_altExt_swap (H : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) (i j : ι) {W : X.Opens}
    (hi : W ≤ T i) (hj : W ≤ T j) :
    resU (le_inf hj hi) (altExt H j i) = (resU (le_inf hi hj) (altExt H i j))⁻¹ := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [altExt_of_gt H h, altExt_of_lt H h, resU_resU, map_inv]
  · rw [altExt_self, map_one, inv_one]
  · rw [altExt_of_lt H h, altExt_of_gt H h, resU_resU, map_inv, inv_inv]

/-- **Alternating extension.** If the units `H i j` satisfy the cocycle identity on strictly
increasing triples, their alternating extension is a cocycle. -/
lemma isCocycle_altExt (H : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)
    (hH : ∀ i j k : ι, i < j → j < k →
      X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ⊓ T k ≤ T i ⊓ T j)).op
          (H i j : Γ(X, T i ⊓ T j)) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          T i ⊓ T j ⊓ T k ≤ T j ⊓ T k)).op (H j k : Γ(X, T j ⊓ T k)) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          T i ⊓ T j ⊓ T k ≤ T i ⊓ T k)).op (H i k : Γ(X, T i ⊓ T k))) :
    IsCocycle (altExt H) := by
  intro a b c
  set W := T a ⊓ T b ⊓ T c
  let S := {x : ι // x = a ∨ x = b ∨ x = c}
  have hW : ∀ x : S, W ≤ T x.1 := by
    rintro ⟨x, rfl | rfl | rfl⟩
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  let r : S → S → Additive (Γ(X, W))ˣ := fun x y =>
    Additive.ofMul (resU (le_inf (hW x) (hW y)) (altExt H x.1 y.1))
  have h0 : ∀ x, r x x = 0 := fun x => by
    change Additive.ofMul (resU _ (altExt H x.1 x.1)) = Additive.ofMul 1
    rw [altExt_self, map_one]
  have hs : ∀ x y, r y x = -r x y := fun x y => by
    have := resU_altExt_swap H x.1 y.1 (hW x) (hW y)
    exact congrArg Additive.ofMul this
  have hstrict : ∀ x y z : S, x < y → y < z → r x y + r y z = r x z := by
    intro x y z hxy hyz
    have hxyz : W ≤ T x.1 ⊓ T y.1 ⊓ T z.1 := le_inf (le_inf (hW x) (hW y)) (hW z)
    have e := congrArg (fun v => X.presheaf.map (homOfLE hxyz).op v) (hH x.1 y.1 z.1 hxy hyz)
    simp only [map_mul] at e
    have hm : resU (le_inf (hW x) (hW y)) (altExt H x.1 y.1) *
        resU (le_inf (hW y) (hW z)) (altExt H y.1 z.1) =
          resU (le_inf (hW x) (hW z)) (altExt H x.1 z.1) := by
      apply Units.ext
      rw [Units.val_mul, resU_val, resU_val, resU_val, altExt_of_lt H hxy, altExt_of_lt H hyz,
        altExt_of_lt H (hxy.trans hyz)]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp] at e
      exact e
    exact congrArg Additive.ofMul hm
  have key := Langlands.AlgebraicGeometry.Modules.CechResolution.add_eq_of_strict r h0 hs hstrict
    ⟨a, Or.inl rfl⟩ ⟨b, Or.inr (Or.inl rfl)⟩ ⟨c, Or.inr (Or.inr rfl)⟩
  have key' := congrArg (fun v : Additive (Γ(X, W))ˣ => ((Additive.toMul v : (Γ(X, W))ˣ) :
    Γ(X, W))) key
  simp only [r, toMul_add, toMul_ofMul, Units.val_mul, resU_val] at key'
  exact key'

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
