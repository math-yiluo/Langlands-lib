/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.MittagLeffler

/-!
# Uniform Mittag-Leffler property for towers of finite locally constant sheaves

Let `X` be a scheme with noetherian underlying space and `(Hₙ)ₙ` a tower of finite locally
constant étale sheaves with finite stalks. Suppose that at every point `x` the tower of stalks is
uniformly Mittag-Leffler: there is `c₀ x` such that for every `m` the images of
`(H_{m+j})_x ⟶ (H_m)_x` are the same for all `j ≥ c₀ x`. Then the tower is uniformly
Mittag-Leffler with a constant independent of `x`: there is `c` such that for every `m` the image
of `H_{m+c} ⟶ H_m` is contained in the image of `H_k ⟶ H_m` for all `k ≥ m + c`
(`AlgebraicGeometry.Etale.exists_imageSubobject_le_of_forall_range_sheafFiber_eq`).

Indeed, the stalk cardinalities of the image subsheaves are locally constant, hence determined by
their values at finitely many points (one in each irreducible component), and an inclusion of
subsheaves with equal stalk cardinalities is an equality.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The image of the stalk map of a morphism of étale sheaves at a geometric point is the image of
the stalk of its image subsheaf. -/
lemma range_sheafFiber_map_eq_range_imageSubobject_arrow {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) :
    Set.range ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map φ) =
      Set.range ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map
        (imageSubobject φ).arrow) := by
  let Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hsurj : Function.Surjective (Φ.map (factorThruImageSubobject φ)) :=
    (ModuleCat.epi_iff_surjective _).1 (Φ.map_epi _)
  have hφ : Φ.map φ = Φ.map (factorThruImageSubobject φ) ≫ Φ.map (imageSubobject φ).arrow := by
    rw [← Φ.map_comp, imageSubobject_arrow_comp]
  rw [hφ, ConcreteCategory.coe_comp, hsurj.range_comp]

/-- An inclusion of image subsheaves gives an inclusion of the images of the stalk maps. -/
lemma range_sheafFiber_map_subset_of_imageSubobject_le {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) {F F' G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {φ : F ⟶ G} {φ' : F' ⟶ G} (h : imageSubobject φ ≤ imageSubobject φ') :
    Set.range ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map φ) ⊆
      Set.range ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map φ') := by
  rw [range_sheafFiber_map_eq_range_imageSubobject_arrow, ← Subobject.ofLE_arrow h,
    Functor.map_comp, ConcreteCategory.coe_comp, Set.range_comp,
    range_sheafFiber_map_eq_range_imageSubobject_arrow s φ']
  exact Set.image_subset_range _ _

/-- The stalk of the image of a morphism of étale sheaves at a geometric point has as many
elements as the image of the map of stalks. -/
lemma natCard_sheafFiber_imageSubobject {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) :
    Nat.card ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      (imageSubobject φ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) =
      Nat.card (Set.range
        ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map φ)) := by
  have hinj : Function.Injective ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map
      (imageSubobject φ).arrow) :=
    (ModuleCat.mono_iff_injective _).1 (Functor.map_mono _ _)
  rw [range_sheafFiber_map_eq_range_imageSubobject_arrow, Nat.card_range_of_injective hinj]

/-- **Uniform Mittag-Leffler property from stalks.** Let `X` be a scheme with noetherian
underlying space and `H` a tower of finite locally constant étale sheaves with finite stalks.
Suppose that for every point `x` there is `c₀ x` such that for every `m` and `j ≥ c₀ x` the image of
the stalk map `(H_{m+j})_x ⟶ (H_m)_x` is that of `(H_{m+c₀ x})_x ⟶ (H_m)_x`. Then there is `c` such
that for every `m` and `k ≥ m + c`, the image of `H_{m+c} ⟶ H_m` is contained in that of
`H_k ⟶ H_m`. -/
theorem exists_imageSubobject_le_of_forall_range_sheafFiber_eq
    [TopologicalSpace.NoetherianSpace X]
    (H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (H.obj (op n))]
    (hfin : ∀ (n : ℕ) (x : X), Finite ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj (H.obj (op n))))
    (c₀ : X → ℕ) (hc₀ : ∀ (x : X) (m j : ℕ), c₀ x ≤ j →
      Set.range ((pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
        |>.map (H.map (homOfLE (Nat.le_add_right m j)).op)) =
      Set.range ((pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
        |>.map (H.map (homOfLE (Nat.le_add_right m (c₀ x))).op))) :
    ∃ c : ℕ, ∀ (m k : ℕ) (hk : m + c ≤ k),
      imageSubobject (H.map (homOfLE (Nat.le_add_right m c)).op) ≤
        imageSubobject (H.map (homOfLE (le_trans (Nat.le_add_right m c) hk)).op) := by
  let Φ (x : X) := (pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  obtain ⟨ι, _, p, hp⟩ := TopologicalSpace.NoetherianSpace.exists_finite_forall_isLocallyConstant X
  obtain ⟨c, hc⟩ := Finite.exists_le (fun i ↦ c₀ (p i))
  refine ⟨c, fun m k hk ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = m + (c + j) := ⟨k - (m + c), by omega⟩
  -- the images `S j ⊆ Hₘ` of the transition maps `H_{m + j} ⟶ Hₘ`
  let S (j : ℕ) : Subobject (H.obj (op m)) :=
    imageSubobject (H.map (homOfLE (Nat.le_add_right m j)).op)
  have hS : Antitone S := fun j j' hjj' ↦ by
    have : H.map (homOfLE (Nat.le_add_right m j')).op =
        H.map (homOfLE (Nat.add_le_add_left hjj' m)).op ≫
          H.map (homOfLE (Nat.le_add_right m j)).op := by
      rw [← H.map_comp]
      rfl
    dsimp only [S]
    rw [this]
    exact imageSubobject_comp_le _ _
  have hinj (j : ℕ) (x : X) : Function.Injective ((Φ x).map (S j).arrow) :=
    (ModuleCat.mono_iff_injective _).1 ((Φ x).map_mono _)
  have hfinS (j : ℕ) (x : X) : Finite ((Φ x).obj (S j)) :=
    have := hfin m x
    Finite.of_injective _ (hinj j x)
  let card (j : ℕ) (x : X) : ℕ := Nat.card ((Φ x).obj (S j))
  have hcard (j : ℕ) : IsLocallyConstant (card j) := by
    have := isLocallyConstantSheaf_imageSubobject (H.map (homOfLE (Nat.le_add_right m j)).op)
    exact (IsLocallyConstant.iff_isOpen_fiber).2 fun n ↦
      isOpen_setOf_natCard_sheafFiber (S j : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n
  -- at the points `p i`, the stalk cardinalities of `S (c + j)` and `S c` agree
  have hpt (i : ι) : card (c + j) (p i) = card c (p i) := by
    dsimp only [card, S, Φ]
    rw [natCard_sheafFiber_imageSubobject, natCard_sheafFiber_imageSubobject,
      hc₀ (p i) m (c + j) ((hc i).trans (Nat.le_add_right c j)), hc₀ (p i) m c (hc i)]
  have hle : S (c + j) ≤ S c := hS (Nat.le_add_right c j)
  have : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_natCard_sheafFiber_eq _ (hfinS c) fun x ↦ by
      obtain ⟨i, hi⟩ := hp x
      exact ((hi (card (c + j)) (hcard (c + j))).trans (hpt i)).trans
        (hi (card c) (hcard c)).symm
  have hle' : S c ≤ S (c + j) := (Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle))
    (Subobject.ofLE_arrow _)).symm.le
  exact hle'

end AlgebraicGeometry.Etale
