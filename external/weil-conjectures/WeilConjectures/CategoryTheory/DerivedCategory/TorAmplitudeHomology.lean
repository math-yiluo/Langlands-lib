/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Homology of a tensor product with an object of Tor amplitude zero

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions. If `L ∈ D(C)` has Tor amplitude in `[0, 0]`, tensoring with `L` is t-exact for
the canonical t-structure; in particular it preserves the vanishing of each homology object.

## Main statements

- `DerivedCategory.isZero_homologyFunctor_tensor_of_torAmplitudeIn`: if `Hⁿ(K) = 0` then
  `Hⁿ(L ⊗ᴸ K) = 0`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

open TStructure (t)

/-- Tensoring with an object of Tor amplitude in `[0, 0]` preserves the vanishing of a homology
object: if `Hⁿ(K) = 0` then `Hⁿ(L ⊗ᴸ K) = 0`. In the truncation triangle
`τ^{<n} K ⟶ K ⟶ τ^{≥n} K` the last term is `≥ n + 1`, and tensoring with `L` keeps the first
term `≤ n - 1` and the last `≥ n + 1`. -/
lemma isZero_homologyFunctor_tensor_of_torAmplitudeIn {L : DerivedCategory C}
    (hL : torAmplitudeIn C 0 0 L) (K : DerivedCategory C) (n : ℤ)
    (hK : IsZero ((homologyFunctor C n).obj K)) :
    IsZero ((homologyFunctor C n).obj (L ⊗ K)) := by
  let T := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished n K
  have h₃ : T.obj₃.IsGE (n + 1) := by
    rw [isGE_iff]
    intro i hi
    obtain hi | rfl := (show i < n ∨ i = n by omega)
    · exact T.obj₃.isZero_of_isGE n i hi
    · have := isIso_homologyFunctor_map_truncGEπ_app K i i le_rfl
      exact hK.of_iso (asIso ((homologyFunctor C i).map ((t.truncGEπ i).app K))).symm
  have h₁ : T.obj₁.IsLE (n - 1) := inferInstanceAs (t.IsLE ((t.truncLT n).obj K) (n - 1))
  have := isLE_tensor_of_torAmplitudeIn hL T.obj₁ (n - 1)
  have := isGE_tensor_of_torAmplitudeIn hL T.obj₃ (n + 1)
  have hT' := ((curriedTensor (DerivedCategory C)).obj L).map_distinguished T hT
  exact ((homologyFunctor C n).map_distinguished_exact _ hT').isZero_of_both_zeros
    (((L ⊗ T.obj₁).isZero_of_isLE (0 + (n - 1)) n (by omega)).eq_of_src _ _)
    (((L ⊗ T.obj₃).isZero_of_isGE (0 + (n + 1)) n (by omega)).eq_of_tgt _ _)

end DerivedCategory
