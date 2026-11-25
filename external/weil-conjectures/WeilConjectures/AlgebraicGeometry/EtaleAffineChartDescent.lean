/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleDirectedColimitDescent
import WeilConjectures.AlgebraicGeometry.AffineChartDirectedRingModel

/-!
# Descent on one affine chart of an inverse system

Source: Stacks Project, Limits, Tag 07RP, affine reduction, and Algebra, Tag 07RI.
(blueprint: lem-weil-pbc-etale-affine-chart-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem etale_on_open_of_isPullback
    {X' Y' X Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (h : IsPullback a f' f b)
    (U : X.Opens) (hf : Etale (U.ι ≫ f)) :
    Etale ((a ⁻¹ᵁ U).ι ≫ f') := by
  exact MorphismProperty.of_isPullback
    ((isPullback_morphismRestrict a U).paste_vert h) hf

private theorem over_pullback_square
    {S T : Scheme.{u}} (p : T ⟶ S) (X Y : Over S) (f : X ⟶ Y) :
    IsPullback ((Over.pullback p).map f).left (pullback.fst X.hom p)
      (pullback.fst Y.hom p) f.left := by
  apply IsPullback.of_right
    (t := (IsPullback.of_hasPullback Y.hom p).flip)
    (s := ?_) (by simp)
  simpa only [pullback.lift_snd, Over.pullback_map_left, Over.w] using
    (IsPullback.of_hasPullback X.hom p).flip

private theorem etale_on_open_pullback_comp
    {S T R : Scheme.{u}} (p : T ⟶ S) (q : R ⟶ T)
    (X Y : Over S) (f : X ⟶ Y) (U : X.left.Opens)
    (hf : Etale (((pullback.fst X.hom p) ⁻¹ᵁ U).ι ≫
      ((Over.pullback p).map f).left)) :
    Etale (((pullback.fst X.hom (q ≫ p)) ⁻¹ᵁ U).ι ≫
      ((Over.pullback (q ≫ p)).map f).left) := by
  let a := pullback.map X.hom (q ≫ p) X.hom p (𝟙 X.left) q (𝟙 S)
    (by simp) (by simp)
  let b := pullback.map Y.hom (q ≫ p) Y.hom p (𝟙 Y.left) q (𝟙 S)
    (by simp) (by simp)
  have ha : a ≫ pullback.fst X.hom p = pullback.fst X.hom (q ≫ p) := by
    simp [a]
  have hb : b ≫ pullback.fst Y.hom p = pullback.fst Y.hom (q ≫ p) := by
    simp [b]
  have h : IsPullback a ((Over.pullback (q ≫ p)).map f).left
      ((Over.pullback p).map f).left b := by
    apply IsPullback.flip
    apply IsPullback.of_bot (t := over_pullback_square p X Y f)
      (s := ?_) ?_
    · simpa only [ha, hb] using over_pullback_square (q ≫ p) X Y f
    · apply pullback.hom_ext <;> simp [a, b, Over.pullback_map_left]
  have het := etale_on_open_of_isPullback h ((pullback.fst X.hom p) ⁻¹ᵁ U) hf
  have hU : a ⁻¹ᵁ ((pullback.fst X.hom p) ⁻¹ᵁ U) =
      (pullback.fst X.hom (q ≫ p)) ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ha]
  rw [hU] at het
  exact het

/-- Étaleness on a fixed affine triple descends and persists at all later stages.
No quasi-compactness or quasi-separatedness of the ambient schemes is required.

Source: Stacks Project, Limits, Tag 07RP (the affine reduction), Algebra, Tag 07RI.
(blueprint: lem-weil-pbc-etale-affine-chart-descent).

Proof: Restrict the inverse system to the upper tail above i₀ and to the inverse
images of W. These are affine, since every transition is affine, and the restricted
limit is the inverse image of W in c.pt. Its coordinate ring is the directed colimit
of the coordinate rings of those inverse images. Write A₀ = Γ(W), B₀ = Γ(V), and
C₀ = Γ(U). The containment hypotheses give an A₀-algebra map φ₀ : B₀ → C₀,
which is finitely presented by local finite presentation of f₀. At each stage,
the inverse images of U and V identify with Spec(Aᵢ ⊗[A₀] C₀) and
Spec(Aᵢ ⊗[A₀] B₀), respectively. The restricted map is Spec(id ⊗ φ₀):
check this on the two pullback projections. The same identifications at the limit
turn hf into étaleness of Spec(id ⊗ φ₀) over the colimit. Apply
Etale.exists_stage_of_directedColimit to obtain an index i. For j ≥ i,
pullback pasting identifies the chart morphism into Yⱼ with the base change of
the chart morphism into Yᵢ. Restrict the resulting pullback square to the preimage
of U; étaleness is preserved by base change.
This argument concerns only U, not a covering or the whole of X₀. -/
theorem Etale.exists_stage_on_affine_chart
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀)))
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (V : Y₀.left.Opens) (hV : IsAffineOpen V) (eV : V ≤ Y₀.hom ⁻¹ᵁ W)
    (U : X₀.left.Opens) (hU : IsAffineOpen U) (eU : U ≤ f₀.left ⁻¹ᵁ V)
    (hf : Etale (((pullback.fst X₀.hom (c.π.app (op i₀))) ⁻¹ᵁ U).ι ≫
      ((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (_ : i₀ ≤ i), ∀ (j : I) (_ : i ≤ j) (hj : i₀ ≤ j),
      Etale (((pullback.fst X₀.hom (D.map (homOfLE hj).op)) ⁻¹ᵁ U).ι ≫
        ((Over.pullback (D.map (homOfLE hj).op)).map f₀).left) := by
  obtain ⟨F, B, C, aB, aC, φ, hfp, hlimit, hstage⟩ :=
    exists_affineChart_directedRingModel D c hc i₀ X₀ Y₀ f₀ W hW V hV eV U hU eU
  let := aB
  let := aC
  have : IsDirected {i : I // i₀ ≤ i} (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨j, haj, hbj⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨j, le_trans a.property haj⟩, haj, hbj⟩⟩
  obtain ⟨i, hi, het⟩ := Etale.exists_stage_of_directedColimit F ⟨i₀, le_rfl⟩
    B C φ hfp (hlimit.mp hf)
  refine ⟨i.val, i.property, ?_⟩
  intro j hij hj
  have heq : D.map (homOfLE hj).op =
      D.map (homOfLE hij).op ≫ D.map (homOfLE i.property).op := by
    rw [← D.map_comp]
    congr 1
  rw [heq]
  exact etale_on_open_pullback_comp (D.map (homOfLE i.property).op)
    (D.map (homOfLE hij).op) X₀ Y₀ f₀ U (hstage i het)

end AlgebraicGeometry
