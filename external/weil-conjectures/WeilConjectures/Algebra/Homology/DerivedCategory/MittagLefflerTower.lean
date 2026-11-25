/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMittagLeffler

/-!
# Mittag-Leffler towers

A tower `G : ℕᵒᵖ ⥤ C` is Mittag-Leffler (`CategoryTheory.Limits.IsMittagLefflerTower`) if it
has a subtower `G'` with epimorphic transitions (the stable images) through which some
transition `G m ⟶ G n` factors, for every `n`.

- `IsMittagLefflerTower.map`, `IsMittagLefflerTower.of_iso`: stability under functors
  preserving monomorphisms and epimorphisms, and under isomorphism;
- `IsMittagLefflerTower.shortExact`: in an abelian category, `G` is an extension of an
  essentially zero tower (the cokernel of `G' ⟶ G`) by `G'`;
- `CategoryTheory.Limits.epi_one_sub_of_isMittagLefflerTower`: `lim¹ G = 0` in a replete
  abelian category;
- `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfIsMittagLefflerTower`:
  `Hⁱ(R lim F) = lim Hⁱ(Fₙ)` when the tower `H^{i-1}(Fₙ)` is Mittag-Leffler.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- A tower `G : ℕᵒᵖ ⥤ C` is **Mittag-Leffler** if it has a subtower `G' ⊆ G` with
epimorphic transitions (the stable images) such that for every `n` some transition
`G m ⟶ G n` factors through `G' n`. In an abelian category this says that `G` is an extension
of an essentially zero tower by `G'` (`CategoryTheory.Limits.IsMittagLefflerTower.shortExact`). -/
def IsMittagLefflerTower (G : ℕᵒᵖ ⥤ C) : Prop :=
  ∃ (G' : ℕᵒᵖ ⥤ C) (ι : G' ⟶ G), (∀ n : ℕ, Mono (ι.app (op n))) ∧
    (∀ n : ℕ, Epi (G'.map (homOfLE n.le_succ).op)) ∧
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (f : G.obj (op m) ⟶ G'.obj (op n)),
      G.map (homOfLE h).op = f ≫ ι.app (op n)

namespace IsMittagLefflerTower

/-- Mittag-Leffler towers are preserved by functors preserving monomorphisms and
epimorphisms (e.g. exact functors). -/
lemma map {D : Type*} [Category* D] {G : ℕᵒᵖ ⥤ C} (hG : IsMittagLefflerTower G) (F : C ⥤ D)
    [F.PreservesMonomorphisms] [F.PreservesEpimorphisms] : IsMittagLefflerTower (G ⋙ F) := by
  obtain ⟨G', ι, hι, h', h''⟩ := hG
  refine ⟨G' ⋙ F, Functor.whiskerRight ι F, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_⟩
  · have := hι n
    dsimp
    infer_instance
  · have := h' n
    dsimp
    infer_instance
  · obtain ⟨m, h, f, hf⟩ := h'' n
    exact ⟨m, h, F.map f, by simp [hf]⟩

/-- Mittag-Leffler towers are invariant under isomorphism. -/
lemma of_iso {G H : ℕᵒᵖ ⥤ C} (hG : IsMittagLefflerTower G) (e : G ≅ H) :
    IsMittagLefflerTower H := by
  obtain ⟨G', ι, hι, h', h''⟩ := hG
  refine ⟨G', ι ≫ e.hom, fun n ↦ ?_, h', fun n ↦ ?_⟩
  · have := hι n
    dsimp
    infer_instance
  · obtain ⟨m, h, f, hf⟩ := h'' n
    refine ⟨m, h, e.inv.app _ ≫ f, ?_⟩
    simp [← reassoc_of% hf]

section Abelian

variable [Abelian C] {G : ℕᵒᵖ ⥤ C}

/-- The short exact sequence `0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0` of a Mittag-Leffler tower: the quotient
`G''` of `G` by its subtower `G'` with epimorphic transitions is essentially zero. -/
lemma shortExact (hG : IsMittagLefflerTower G) :
    ∃ (G' G'' : ℕᵒᵖ ⥤ C) (ι : G' ⟶ G) (π : G ⟶ G'')
      (hιπ : ∀ n : ℕ, ι.app (op n) ≫ π.app (op n) = 0),
      (∀ n : ℕ, (ShortComplex.mk _ _ (hιπ n)).ShortExact) ∧
      (∀ n : ℕ, Epi (G'.map (homOfLE n.le_succ).op)) ∧
      ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), G''.map (homOfLE h).op = 0 := by
  obtain ⟨G', ι, hι, h', h''⟩ := hG
  have : Mono ι := NatTrans.mono_of_mono_app _
  let S : ShortComplex (ℕᵒᵖ ⥤ C) := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  refine ⟨G', cokernel ι, ι, cokernel.π ι, fun n ↦ by simp [← NatTrans.comp_app],
    fun n ↦ hS.map_of_exact ((evaluation _ _).obj (op n)), h', fun n ↦ ?_⟩
  obtain ⟨m, h, f, hf⟩ := h'' n
  refine ⟨m, h, ?_⟩
  have : Epi ((cokernel.π ι).app (op m)) := (hS.map_of_exact ((evaluation _ _).obj (op m))).epi_g
  rw [← cancel_epi ((cokernel.π ι).app (op m)), ← NatTrans.naturality, hf, assoc,
    ← NatTrans.comp_app, cokernel.condition]
  simp

end Abelian

end IsMittagLefflerTower

variable [Abelian C] [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C]

/-- **`lim¹` vanishes for Mittag-Leffler towers in a replete abelian category**: `1 - t` is an
epimorphism on `∏ Gₙ`. -/
lemma epi_one_sub_of_isMittagLefflerTower (hC : EpiπAppZeroOfEpi C) {G : ℕᵒᵖ ⥤ C}
    (hG : IsMittagLefflerTower G) {P : Fan fun n : ℕ ↦ G.obj (op n)} (hP : IsLimit P)
    (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op) :
    Epi (𝟙 P.pt - t) := by
  obtain ⟨G', G'', ι, π, hιπ, hS, h', h''⟩ := hG.shortExact
  exact epi_one_sub_of_shortExact hC ι π hιπ hS h' h'' hP t ht

end CategoryTheory.Limits

namespace DerivedCategory

open CategoryTheory.Limits Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

/-- **The Milnor sequence for Mittag-Leffler towers**: if `c` is a homotopy limit cone over a
tower `F` in `D(C)` (`C` replete in the sense of `EpiπAppZeroOfEpi`) and the tower
`H^{i-1}(Fₙ)` is Mittag-Leffler, then `Hⁱ(R lim F) = lim Hⁱ(Fₙ)`. -/
noncomputable def isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfIsMittagLefflerTower
    (hC : EpiπAppZeroOfEpi C) (hc : IsHomotopyLimit c) (i : ℤ)
    (hF : IsMittagLefflerTower (F ⋙ homologyFunctor C (i - 1))) :
    IsLimit ((homologyFunctor C i).mapCone c) :=
  have ht (n : ℕ) : piTowerShift (F ⋙ homologyFunctor C (i - 1)) ≫ Pi.π _ n =
      Pi.π _ (n + 1) ≫ (F ⋙ homologyFunctor C (i - 1)).map (homOfLE n.le_succ).op :=
    Pi.lift_comp_π _ _
  have := isIso_lift_homologyFunctor_mapCone_of_isHomotopyLimit hc (i - 1) i (by lia)
    (productIsProduct _) _ ht (epi_one_sub_of_isMittagLefflerTower hC hF
      (productIsProduct _) _ ht)
    (limit.isLimit _)
  IsLimit.ofPointIso (limit.isLimit _)

end DerivedCategory
