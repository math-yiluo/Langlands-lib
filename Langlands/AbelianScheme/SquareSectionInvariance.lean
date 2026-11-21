import Langlands.AbelianScheme.SeparatingLineBundle.Assembly

/-! # Sections of `L ⊗ L` from translates, and generic invariance of their zero sets

Let `G` be a commutative group scheme over a field and `L` a line bundle on `G` satisfying
the theorem of the square. For a section `s` of `L`:

* for a rational point `a`, the theorem of the square identifies `τ_a^* L ⊗ τ_{a⁻¹}^* L`
  with `L ⊗ L`, so `τ_a^* s ⊗ τ_{a⁻¹}^* s` is a section of `L ⊗ L`
  (`pairSection`); over an algebraically closed field this shows that `L ⊗ L` has no
  rational base point when `s` is nonzero at some rational point;
* for a rational point `a` and a section `σ` of `L ⊗ L`, the theorem of the square (in the
  form `tripleIso` of the Library) identifies `τ_{a⁻²}^* L ⊗ τ_a^*(L ⊗ L)` with
  `(L ⊗ L) ⊗ L`, so `τ_{a⁻²}^* s ⊗ τ_a^* σ` is a section of `(L ⊗ L) ⊗ L`
  (`squarePairSection`).

If the sections of `(L ⊗ L) ⊗ L` vanishing at `x₀` all vanish at `x₁` (respectively along
a tangent vector `t` at `x₀`), then for every rational `a` with `s((a a)⁻¹ x₁) ≠ 0`
(respectively `s((a a)⁻¹ x₀) ≠ 0`), every section `σ` of `L ⊗ L` vanishing at `a x₀` also
vanishes at `a x₁` (respectively along the `a`-translate of `t`). These implications
adapt Mumford's zero-sum triple construction in *Abelian Varieties*, §17: here the
opposite pair of translates generates the square, and the diagonal choice `tripleIso hsq a a`
allows an arbitrary section of the square and only one auxiliary translate. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.GroupScheme.SeparatingLineBundle

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

section Sections

variable {K : Type u} [Field K] (G : Grp (Over (Spec (CommRingCat.of K))))
  (L : LineBundle G.X.left) (s : GlobalSections L.obj)

/-- The line bundle `L ⊗ L`. -/
abbrev squareLB : LineBundle G.X.left := tensorLB L L

/-- Pullback along a translation commutes with `L ⊗ L`. -/
def transSquareIso (c : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    (transLB G (squareLB G L) c).obj ≅ (tensorLB (transLB G L c) (transLB G L c)).obj :=
  letI := pullbackTensorComparisonIsIso (translation G c).left
  asIso ((pullbackTensorComparison (translation G c).left).app (L.obj, L.obj))

variable {G L} in
/-- The theorem of the square identifies `τ_a^* L ⊗ τ_{a⁻¹}^* L` with `L ⊗ L`. -/
def pairIso (hsq : SquareFor G L) (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    (tensorLB (transLB G L a) (transLB G L a⁻¹)).obj ≅ (squareLB G L).obj :=
  (hsq a a⁻¹).some.symm ≪≫ tensorMapIso (transOneIso G L _ (mul_inv_cancel a)) (Iso.refl _)

variable {G L} in
/-- The section `τ_a^* s ⊗ τ_{a⁻¹}^* s` of `L ⊗ L`. -/
def pairSection (hsq : SquareFor G L) (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    GlobalSections (squareLB G L).obj :=
  (pairIso hsq a).hom.app ⊤
    (tensorSection _ _ (transSection G L s a) (transSection G L s a⁻¹))

variable {G L} in
/-- At a rational point `d` the pair section vanishes exactly when `s` vanishes at `a d`
or at `a⁻¹ d`. -/
theorem vanishesAlong_pairSection_point_iff (hsq : SquareFor G L)
    (a d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    VanishesAlong (squareLB G L) d.left (pairSection s hsq a) ↔
      VanishesAlong L (a * d).left s ∨ VanishesAlong L (a⁻¹ * d).left s := by
  rw [pairSection, vanishesAlong_mapIso_iff, vanishesAlong_tensor_field_iff,
    vanishesAlong_transSection_iff, vanishesAlong_transSection_iff, left_comp_translation,
    left_comp_translation]

variable {G L} in
/-- The theorem of the square identifies `τ_{(a a)⁻¹}^* L ⊗ τ_a^*(L ⊗ L)` with
`(L ⊗ L) ⊗ L`. -/
def squarePairIso (hsq : SquareFor G L) (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    (tensorLB (transLB G L (a * a)⁻¹) (transLB G (squareLB G L) a)).obj ≅
      (cubeLB G L).obj :=
  tensorMapIso (Iso.refl _) (transSquareIso G L a) ≪≫ tripleIso hsq a a

variable {G L} in
/-- The section `τ_{(a a)⁻¹}^* s ⊗ τ_a^* σ` of `(L ⊗ L) ⊗ L`, for a section `σ` of
`L ⊗ L`. -/
def squarePairSection (hsq : SquareFor G L) (σ : GlobalSections (squareLB G L).obj)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) : GlobalSections (cubeLB G L).obj :=
  (squarePairIso hsq a).hom.app ⊤
    (tensorSection _ _ (transSection G L s (a * a)⁻¹) (transSection G (squareLB G L) σ a))

variable {G L} in
/-- At a rational point `d` the section `τ_{(a a)⁻¹}^* s ⊗ τ_a^* σ` vanishes exactly when
`s` vanishes at `(a a)⁻¹ d` or `σ` vanishes at `a d`. -/
theorem vanishesAlong_squarePairSection_point_iff (hsq : SquareFor G L)
    (σ : GlobalSections (squareLB G L).obj)
    (a d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    VanishesAlong (cubeLB G L) d.left (squarePairSection s hsq σ a) ↔
      VanishesAlong L ((a * a)⁻¹ * d).left s ∨ VanishesAlong (squareLB G L) (a * d).left σ := by
  rw [squarePairSection, vanishesAlong_mapIso_iff, vanishesAlong_tensor_field_iff,
    vanishesAlong_transSection_iff, vanishesAlong_transSection_iff, left_comp_translation,
    left_comp_translation]

variable {G L} in
/-- Along a tangent vector at a rational point `d` where `s` is nonzero at `(a a)⁻¹ d`, the
section `τ_{(a a)⁻¹}^* s ⊗ τ_a^* σ` vanishes exactly when `σ` vanishes along the
`a`-translate of the tangent vector. -/
theorem vanishesAlong_squarePairSection_tangent_iff (hsq : SquareFor G L)
    (σ : GlobalSections (squareLB G L).obj)
    (a d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ G.X.left}
    (ht : IsTangentVectorAt G.X.hom d.left t)
    (hc : ¬ VanishesAlong L ((a * a)⁻¹ * d).left s) :
    VanishesAlong (cubeLB G L) t (squarePairSection s hsq σ a) ↔
      VanishesAlong (squareLB G L) (t ≫ (translation G a).left) σ := by
  rw [← left_comp_translation, ← vanishesAlong_transSection_iff] at hc
  rw [squarePairSection, vanishesAlong_mapIso_iff,
    vanishesAlong_tensor_left_iff _ _ _ _ t (mem_trivializationOpen_of_isTangentVectorAt ht hc),
    vanishesAlong_transSection_iff]

variable {G L} in
/-- If every section of `(L ⊗ L) ⊗ L` vanishing at `x₀` vanishes at `x₁`, then for every
rational point `a` with `s((a a)⁻¹ x₁) ≠ 0`, every section of `L ⊗ L` vanishing at `a x₀`
vanishes at `a x₁`. -/
theorem vanishesAlong_square_of_not_separates (hsq : SquareFor G L)
    (x₀ x₁ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    (hsep : ∀ σ : GlobalSections (cubeLB G L).obj,
      VanishesAlong (cubeLB G L) x₀.left σ → VanishesAlong (cubeLB G L) x₁.left σ)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    (ha : ¬ VanishesAlong L ((a * a)⁻¹ * x₁).left s)
    (σ : GlobalSections (squareLB G L).obj) (hσ : VanishesAlong (squareLB G L) (a * x₀).left σ) :
    VanishesAlong (squareLB G L) (a * x₁).left σ := by
  have h0 : VanishesAlong (cubeLB G L) x₀.left (squarePairSection s hsq σ a) :=
    (vanishesAlong_squarePairSection_point_iff s hsq σ a x₀).mpr (Or.inr hσ)
  rcases (vanishesAlong_squarePairSection_point_iff s hsq σ a x₁).mp (hsep _ h0) with h | h
  · exact absurd h ha
  · exact h

variable {G L} in
/-- If every section of `(L ⊗ L) ⊗ L` vanishing at `x₀` vanishes along a tangent vector `t`
at `x₀`, then for every rational point `a` with `s((a a)⁻¹ x₀) ≠ 0`, every section of
`L ⊗ L` vanishing at `a x₀` vanishes along the `a`-translate of `t`. -/
theorem vanishesAlong_square_translate_tangent_of_not_separates (hsq : SquareFor G L)
    (x₀ : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ G.X.left}
    (ht : IsTangentVectorAt G.X.hom x₀.left t)
    (hsep : ∀ σ : GlobalSections (cubeLB G L).obj,
      VanishesAlong (cubeLB G L) x₀.left σ → VanishesAlong (cubeLB G L) t σ)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
    (ha : ¬ VanishesAlong L ((a * a)⁻¹ * x₀).left s)
    (σ : GlobalSections (squareLB G L).obj) (hσ : VanishesAlong (squareLB G L) (a * x₀).left σ) :
    VanishesAlong (squareLB G L) (t ≫ (translation G a).left) σ := by
  have h0 : VanishesAlong (cubeLB G L) x₀.left (squarePairSection s hsq σ a) :=
    (vanishesAlong_squarePairSection_point_iff s hsq σ a x₀).mpr (Or.inr hσ)
  exact (vanishesAlong_squarePairSection_tangent_iff s hsq σ a x₀ ht ha).mp (hsep _ h0)

end Sections

section BasePoints

variable {K : Type u} [Field K] [IsAlgClosed K] (G : Grp (Over (Spec (CommRingCat.of K))))
  [IsCommMonObj G.X] [LocallyOfFiniteType G.X.hom] [IrreducibleSpace G.X.left]

/-- If `L` satisfies the theorem of the square and has a section nonzero at some rational
point, then `L ⊗ L` has no rational base point. -/
theorem exists_squareSection_not_vanishesAlong (L : LineBundle G.X.left) (hsq : SquareFor G L)
    (s : GlobalSections L.obj)
    (hs : ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, ¬ VanishesAlong L y.left s)
    (d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    ∃ σ : GlobalSections (squareLB G L).obj, ¬ VanishesAlong (squareLB G L) d.left σ := by
  obtain ⟨b, hb1, hb2⟩ := exists_good_second G L s hs d 1
  refine ⟨pairSection s hsq b, ?_⟩
  rw [vanishesAlong_pairSection_point_iff]
  rw [one_mul] at hb2
  rintro (h | h)
  exacts [hb1 h, hb2 h]

/-- If `L` satisfies the theorem of the square and has a section nonzero at some rational
point, then `(L ⊗ L) ⊗ L` has no rational base point. -/
theorem exists_cubeSection_not_vanishesAlong (L : LineBundle G.X.left) (hsq : SquareFor G L)
    (s : GlobalSections L.obj)
    (hs : ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X, ¬ VanishesAlong L y.left s)
    (d : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    ∃ σ : GlobalSections (cubeLB G L).obj, ¬ VanishesAlong (cubeLB G L) d.left σ := by
  obtain ⟨a, b, hab⟩ := exists_good_pair G L s hs d
  refine ⟨tripleSection s hsq a b, ?_⟩
  rw [vanishesAlong_tripleSection_point_iff]
  rintro (h | h | h)
  exacts [hab.2.2 h, hab.1 h, hab.2.1 h]

end BasePoints

end Langlands.GroupScheme.SeparatingLineBundle
