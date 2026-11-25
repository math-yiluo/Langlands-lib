/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GradedLineFractionChart.GradedLineFractionChart
import WeilConjectures.AlgebraicGeometry.Graded.GradedLineFractionSameBase
import WeilConjectures.AlgebraicGeometry.Graded.GradedLineFractionBaseRefinement

/-! # Agreement of graded line fraction charts

Source: Stacks Project, Constructions, Tags 01NK and 01O9
(blueprint: lem-trf-graded-line-fraction-overlap).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] Scheme.GradedAlgebraData.relProj
attribute [local irreducible] Scheme.GradedAlgebraData.relProjι

/-- The spectrum maps of any two framed homogeneous fractions agree over their overlap.
No generation hypothesis is required.

Source: Stacks Project, Constructions, Tag 01NK, lemma-invertible-map-into-proj,
and Tag 01O9, lemma-invertible-map-into-relative-proj, affine gluing
(blueprint: lem-trf-graded-line-fraction-overlap).

Proof: Work locally on the pullback of the two source open immersions. At each
point choose an affine base open V in the intersection of the two original base
opens. Apply the local base-refinement lemma to each chart and intersect the inverse
images of its comparison neighborhoods. This gives two charts over the same V and
source and target comparison equations. The source equations and the original
pullback condition give a morphism from this common neighborhood into the pullback
of the restricted charts. Apply the fixed-base overlap lemma there: it constructs
the homogeneous coefficient ring maps, uses the fraction formula to identify their
chart maps with Proj.fromOfGlobalSections, and applies unit-power invariance to
compare the two frames. Pull this equality back and use the target comparison
equations. Scheme morphism locality gives the asserted global pullback equality.
Empty opens and zero divisors require no exception: all scalar cancellation occurs
either in a free frame or after the corresponding denominator has become a unit. -/
theorem gradedLineFraction_overlap
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ) :
    ∀ i j : GradedLineFractionChart h A L,
      pullback.fst (i.source c) (j.source c) ≫ i.target c ρ =
        pullback.snd (i.source c) (j.source c) ≫ j.target c ρ := by
  intro i j
  let p := pullback.fst (i.source c) (j.source c)
  let q := pullback.snd (i.source c) (j.source c)
  have hbase (k : GradedLineFractionChart h A L) (z : k.domain c) :
      (k.source c ≫ h) z ∈ k.U.1 := by
    apply k.hWU
    change k.source c z ∈ k.W.1
    dsimp only [GradedLineFractionChart.source, Scheme.Hom.comp_apply]
    exact Subtype.mem _
  apply Scheme.hom_ext_of_forall
  intro x
  have hxi : (p ≫ i.source c ≫ h) x ∈ i.U.1 := hbase i (p x)
  have hxj : (p ≫ i.source c ≫ h) x ∈ j.U.1 := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact hbase j (q x)
  obtain ⟨V₀, hV₀, hxV, hVij⟩ := exists_isAffineOpen_mem_and_subset
    (show (p ≫ i.source c ≫ h) x ∈ i.U.1 ⊓ j.U.1 from ⟨hxi, hxj⟩)
  let V : S.affineOpens := ⟨V₀, hV₀⟩
  have hVi : V ≤ i.U := hVij.trans inf_le_left
  have hVj : V ≤ j.U := hVij.trans inf_le_right
  have hxVj : (j.source c ≫ h) (q x) ∈ V.1 := by
    change (q ≫ j.source c ≫ h) x ∈ V.1
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
    exact hxV
  obtain ⟨Wi, hWi, hWVi, Oi, hxiO, fi, hfi, hti⟩ :=
    gradedLineFraction_baseRefinement ψ P hP0 hPs c hc ρ hρ i V hVi (p x) hxV
  obtain ⟨Wj, hWj, hWVj, Oj, hxjO, fj, hfj, htj⟩ :=
    gradedLineFraction_baseRefinement ψ P hP0 hPs c hc ρ hρ j V hVj (q x) hxVj
  let ki : GradedLineFractionChart h A L :=
    ⟨V, Wi, hWVi, L.presheaf.map (homOfLE (X := T.Opens) hWi).op i.l, i.hl.map hWi,
      i.d, i.hd, ⟨A.res hVi i.e, (A.res hVi).map_mem i.e.property⟩⟩
  let kj : GradedLineFractionChart h A L :=
    ⟨V, Wj, hWVj, L.presheaf.map (homOfLE (X := T.Opens) hWj).op j.l, j.hl.map hWj,
      j.d, j.hd, ⟨A.res hVj j.e, (A.res hVj).map_mem j.e.property⟩⟩
  let B := (p ⁻¹ᵁ Oi) ⊓ (q ⁻¹ᵁ Oj)
  let ai : B.toScheme ⟶ Oi.toScheme := p.resLE Oi B inf_le_left
  let aj : B.toScheme ⟶ Oj.toScheme := q.resLE Oj B inf_le_right
  have hai : ai ≫ Oi.ι = B.ι ≫ p := by simp only [ai, Scheme.Hom.resLE_comp_ι]
  have haj : aj ≫ Oj.ι = B.ι ≫ q := by simp only [aj, Scheme.Hom.resLE_comp_ι]
  have hw : (ai ≫ fi) ≫ ki.source c = (aj ≫ fj) ≫ kj.source c := by
    calc
      (ai ≫ fi) ≫ ki.source c = ai ≫ (Oi.ι ≫ i.source c) := by rw [Category.assoc, hfi]
      _ = B.ι ≫ (p ≫ i.source c) := by rw [← Category.assoc, hai, Category.assoc]
      _ = B.ι ≫ (q ≫ j.source c) :=
        congrArg (fun z ↦ B.ι ≫ z)
          (show p ≫ i.source c = q ≫ j.source c from pullback.condition)
      _ = aj ≫ (Oj.ι ≫ j.source c) := by simp only [← Category.assoc, haj]
      _ = (aj ≫ fj) ≫ kj.source c := by rw [Category.assoc, hfj]
  let a := pullback.lift (ai ≫ fi) (aj ≫ fj) hw
  have heq := congrArg (fun z ↦ a ≫ z)
    (gradedLineFraction_sameBase ψ P hP0 hPs c hc ρ hρ ki kj rfl)
  have hlocal : B.ι ≫ (p ≫ i.target c ρ) = B.ι ≫ (q ≫ j.target c ρ) := by
    calc
      B.ι ≫ (p ≫ i.target c ρ) = ai ≫ (fi ≫ ki.target c ρ) := by
        rw [hti]
        simp only [← Category.assoc, hai]
      _ = aj ≫ (fj ≫ kj.target c ρ) := by
        simpa only [a, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] using heq
      _ = B.ι ≫ (q ≫ j.target c ρ) := by
        rw [htj]
        simp only [← Category.assoc, haj]
  exact ⟨B, ⟨hxiO, hxjO⟩, hlocal⟩

end AlgebraicGeometry.Scheme.Modules
