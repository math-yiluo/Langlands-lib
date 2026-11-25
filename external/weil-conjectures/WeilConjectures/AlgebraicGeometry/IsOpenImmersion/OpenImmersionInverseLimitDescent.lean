/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent

/-!
# Eventual descent of open immersions along qcqs inverse limits

## References

* Stacks Project, Limits, Tag 0EUU in Situation 081D, and stability of open immersions under base
  change
* Stacks Project, Limits, Tag 0EUU in Situation 081D
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A property stable under base change persists after another change of base. -/
private theorem property_over_pullback_comp
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {S T R : Scheme.{u}} (p : T ⟶ S) (q : R ⟶ T)
    (X Y : Over S) (f : X ⟶ Y)
    (hf : P ((Over.pullback p).map f).left) :
    P ((Over.pullback (q ≫ p)).map f).left := by
  let a := pullback.map X.hom (q ≫ p) X.hom p (𝟙 X.left) q (𝟙 S)
    (by simp) (by simp)
  let b := pullback.map Y.hom (q ≫ p) Y.hom p (𝟙 Y.left) q (𝟙 S)
    (by simp) (by simp)
  have ha : a ≫ pullback.fst X.hom p = pullback.fst X.hom (q ≫ p) := by
    simp [a]
  have hb : b ≫ pullback.fst Y.hom p = pullback.fst Y.hom (q ≫ p) := by
    simp [b]
  have hp : IsPullback ((Over.pullback p).map f).left (pullback.fst X.hom p)
      (pullback.fst Y.hom p) f.left := by
    apply IsPullback.of_right
      (t := (IsPullback.of_hasPullback Y.hom p).flip)
      (s := ?_) (by simp)
    simpa only [pullback.lift_snd, Over.pullback_map_left, Over.w] using
      (IsPullback.of_hasPullback X.hom p).flip
  have hqp : IsPullback ((Over.pullback (q ≫ p)).map f).left
      (pullback.fst X.hom (q ≫ p)) (pullback.fst Y.hom (q ≫ p)) f.left := by
    apply IsPullback.of_right
      (t := (IsPullback.of_hasPullback Y.hom (q ≫ p)).flip)
      (s := ?_) (by simp)
    simpa only [pullback.lift_snd, Over.pullback_map_left, Over.w] using
      (IsPullback.of_hasPullback X.hom (q ≫ p)).flip
  have h : IsPullback a ((Over.pullback (q ≫ p)).map f).left
      ((Over.pullback p).map f).left b := by
    apply IsPullback.flip
    apply IsPullback.of_bot (t := hp)
      (s := ?_) ?_
    · simpa only [ha, hb] using hqp
    · apply pullback.hom_ext <;> simp [a, b, Over.pullback_map_left]
  exact P.of_isPullback h hf

/-- A locally finitely presented morphism between qcqs schemes over a stage of a
qcqs inverse system with affine transitions is an open immersion at every sufficiently
late stage if its base change to the limit is an open immersion. Neither its source
nor its target is required to be affine. -/
theorem IsOpenImmersion.eventually_of_inverseLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : IsOpenImmersion (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
      IsOpenImmersion
        (((Over.pullback (D.map (homOfLE (hi.trans hij)).op)).map f₀).left) := by
  have := hf
  obtain ⟨a, ha, het⟩ := Etale.exists_stage_of_inverseLimit D c hc i₀ X₀ Y₀ f₀
    (inferInstance : Etale ((Over.pullback (c.π.app (op i₀))).map f₀).left)
  obtain ⟨b, hb, hmono⟩ := exists_mono_baseChange_stage D c hc i₀ X₀ Y₀ f₀
    (inferInstance : Mono ((Over.pullback (c.π.app (op i₀))).map f₀).left)
  obtain ⟨i, hai, hbi⟩ := exists_ge_ge a b
  refine ⟨i, ha.trans hai, ?_⟩
  intro j hij
  have hcomp (k : I) (hk : i₀ ≤ k) (hkj : k ≤ j) :
      D.map (homOfLE (hk.trans hkj)).op =
        D.map (homOfLE hkj).op ≫ D.map (homOfLE hk).op := by
    rw [← D.map_comp]
    congr 1
  have hj : Etale ((Over.pullback
      (D.map (homOfLE ((ha.trans hai).trans hij)).op)).map f₀).left := by
    rw [hcomp a ha (hai.trans hij)]
    exact property_over_pullback_comp (@Etale)
      (D.map (homOfLE ha).op) (D.map (homOfLE (hai.trans hij)).op) X₀ Y₀ f₀ het
  have hjmono : Mono ((Over.pullback
      (D.map (homOfLE ((ha.trans hai).trans hij)).op)).map f₀).left := by
    rw [hcomp b hb (hbi.trans hij)]
    exact property_over_pullback_comp (MorphismProperty.monomorphisms Scheme.{u})
      (D.map (homOfLE hb).op) (D.map (homOfLE (hbi.trans hij)).op) X₀ Y₀ f₀ hmono
  exact IsOpenImmersion.of_etale_of_universallyInjective _

end AlgebraicGeometry
