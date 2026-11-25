/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerTower
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Artinian.Module
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Stable images of towers of modules

For a tower of modules `G : ℕᵒᵖ ⥤ ModuleCat R`, the stable image at `n` is the intersection of
the images of all transitions `G m ⟶ G n` (`ModuleCat.stableImage`); they form a subtower
`ModuleCat.stableImageTower G`.

- `ModuleCat.exists_stableImage_eq_towerRange`: if `G n` is Artinian, the images stabilise;
- `ModuleCat.isMittagLefflerTower_of_isArtinian`, `ModuleCat.isMittagLefflerTower_of_finite`:
  towers of Artinian (e.g. finite) modules are Mittag-Leffler: the stable images have
  surjective transitions and the transitions factor through them;
- `ModuleCat.isMittagLefflerTower_comp_constantSheaf_of_finite`: so are towers of constant
  sheaves of finite modules.
-/

@[expose] public section

open CategoryTheory Opposite Limits

namespace ModuleCat

variable {R : Type*} [Ring R] (G : ℕᵒᵖ ⥤ ModuleCat R)

/-- Composition of transitions, elementwise. -/
lemma tower_map_hom_map_hom {n m m' : ℕ} (h : n ≤ m) (h' : m ≤ m') (x : G.obj (op m')) :
    (G.map (homOfLE h).op).hom ((G.map (homOfLE h').op).hom x) =
      (G.map (homOfLE (h.trans h')).op).hom x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp]
  rfl

/-- The image of the transition `G m ⟶ G n`. -/
abbrev towerRange {n m : ℕ} (h : n ≤ m) : Submodule R (G.obj (op n)) :=
  LinearMap.range (G.map (homOfLE h).op).hom

/-- Images of transitions shrink as the source moves up the tower. -/
lemma towerRange_antitone {n m m' : ℕ} (h : n ≤ m) (h' : m ≤ m') :
    towerRange G (h.trans h') ≤ towerRange G h := by
  rintro y ⟨x, rfl⟩
  exact ⟨_, tower_map_hom_map_hom G h h' x⟩

/-- The **stable image** of a tower at `n`: the intersection of the images of all transitions
`G m ⟶ G n`. -/
def stableImage (n : ℕ) : Submodule R (G.obj (op n)) :=
  ⨅ (m : ℕ) (h : n ≤ m), towerRange G h

/-- The stable image is contained in every image. -/
lemma stableImage_le_towerRange {n m : ℕ} (h : n ≤ m) : stableImage G n ≤ towerRange G h :=
  iInf₂_le m h

/-- Transitions map stable images into stable images. -/
lemma map_mem_stableImage {n m : ℕ} (h : n ≤ m) {x : G.obj (op m)}
    (hx : x ∈ stableImage G m) : (G.map (homOfLE h).op).hom x ∈ stableImage G n := by
  refine Submodule.mem_iInf _ |>.2 fun k ↦ Submodule.mem_iInf _ |>.2 fun hk ↦ ?_
  obtain ⟨y, rfl⟩ := stableImage_le_towerRange G (show m ≤ max m k from le_max_left _ _) hx
  rw [tower_map_hom_map_hom]
  exact towerRange_antitone G hk (show k ≤ max m k from le_max_right _ _) ⟨y, rfl⟩

/-- **Images stabilise in a tower of Artinian modules**: the stable image at `n` is the image
of `G m ⟶ G n` for all large `m`. -/
lemma exists_stableImage_eq_towerRange (n : ℕ) [IsArtinian R (G.obj (op n))] :
    ∃ (N : ℕ) (hN : n ≤ N), ∀ (m : ℕ) (hm : N ≤ m),
      stableImage G n = towerRange G (hN.trans hm) := by
  let f : ℕ →o (Submodule R (G.obj (op n)))ᵒᵈ :=
    ⟨fun k ↦ OrderDual.toDual (towerRange G (n.le_add_right k)), fun k k' hk ↦
      towerRange_antitone G (n.le_add_right k) (show n + k ≤ n + k' by lia)⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨n + N, n.le_add_right N, fun m hm ↦ le_antisymm (stableImage_le_towerRange G _) ?_⟩
  refine le_iInf₂ fun m' hm' ↦ ?_
  rcases le_total m' m with hmm' | hmm'
  · exact towerRange_antitone G hm' hmm'
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm'
    have hk : f N = f k := hN k (by lia)
    refine (towerRange_antitone G (n.le_add_right N) hm).trans (le_of_eq ?_)
    exact congrArg OrderDual.ofDual hk

/-- The **tower of stable images** of a tower of modules. -/
@[simps]
def stableImageTower (G : ℕᵒᵖ ⥤ ModuleCat R) : ℕᵒᵖ ⥤ ModuleCat R where
  obj n := ModuleCat.of R (stableImage G n.unop)
  map {n m} f := ModuleCat.ofHom <| (G.map f).hom.restrict fun _ hx ↦
    map_mem_stableImage G (leOfHom f.unop) hx
  map_id n := ModuleCat.hom_ext <| LinearMap.ext fun x ↦ Subtype.ext (by simp)
  map_comp f g := ModuleCat.hom_ext <| LinearMap.ext fun x ↦ Subtype.ext (by simp)

/-- The inclusion of the tower of stable images. -/
@[simps]
def stableImageTowerι (G : ℕᵒᵖ ⥤ ModuleCat R) : stableImageTower G ⟶ G where
  app n := ModuleCat.ofHom (stableImage G n.unop).subtype

/-- **Towers of Artinian modules are Mittag-Leffler** (e.g. towers of finite modules, or of
finitely generated modules over Artinian rings such as `𝒪_E ⧸ ℓⁿ`): the stable images form a
subtower with surjective transitions through which the transitions factor. -/
theorem isMittagLefflerTower_of_isArtinian [∀ n : ℕ, IsArtinian R (G.obj (op n))] :
    IsMittagLefflerTower G := by
  refine ⟨stableImageTower G, stableImageTowerι G, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_⟩
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    rintro ⟨y, hy⟩
    obtain ⟨N₁, hN₁, h₁⟩ := exists_stableImage_eq_towerRange G n
    obtain ⟨N₂, hN₂, h₂⟩ := exists_stableImage_eq_towerRange G (n + 1)
    have hM₂ : N₂ ≤ max N₁ N₂ := le_max_right _ _
    rw [h₁ (max N₁ N₂) (le_max_left _ _)] at hy
    obtain ⟨z, rfl⟩ := hy
    have hz : (G.map (homOfLE (hN₂.trans hM₂)).op).hom z ∈ stableImage G (n + 1) := by
      rw [h₂ _ hM₂]
      exact ⟨z, rfl⟩
    exact ⟨⟨_, hz⟩, Subtype.ext (tower_map_hom_map_hom G n.le_succ _ z)⟩
  · obtain ⟨N, hN, h⟩ := exists_stableImage_eq_towerRange G n
    refine ⟨N, hN, ModuleCat.ofHom ((G.map (homOfLE hN).op).hom.codRestrict _ fun x ↦ ?_), ?_⟩
    · rw [h N le_rfl]
      exact ⟨x, rfl⟩
    · rfl

/-- Towers of finite modules are Mittag-Leffler. -/
theorem isMittagLefflerTower_of_finite [∀ n : ℕ, Finite (G.obj (op n))] :
    IsMittagLefflerTower G :=
  have := fun n : ℕ ↦ isArtinian_of_finite (R := R) (M := G.obj (op n))
  isMittagLefflerTower_of_isArtinian G

/-- **Towers of constant sheaves of finite modules are Mittag-Leffler**, the constant sheaf
functor being exact. -/
theorem isMittagLefflerTower_comp_constantSheaf_of_finite {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [HasSheafify J (ModuleCat R)]
    [∀ n : ℕ, Finite (G.obj (op n))] :
    IsMittagLefflerTower (G ⋙ constantSheaf J (ModuleCat R)) :=
  (isMittagLefflerTower_of_finite G).map _

end ModuleCat
