/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentCompatibility

/-! # Fractions across relative Proj twist charts

## References

* Stacks Project, Constructions, Tag 01NR
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.GradedAlgebraData
private theorem normalized_homogeneousSection
    {R T : Type u} [CommRing R] [CommRing T]
    {σ τ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    [SetLike τ T] [AddSubgroupClass τ T]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ,
      (Scheme.Modules.tensorPullback r).obj (Proj.twist 𝒜 j) ≅ Proj.twist ℬ j)
    (hθ : Proj.IsScalarExtensionTwistComparison ψ r θ)
    (n : ℕ) (a : R) (ha : a ∈ 𝒜 n) (W : (Proj 𝒜).Opens) :
    Proj.scalarExtensionTwistSection r θ (0 + n) W
      ((Proj.unitToTwist ha).app W (1 : Γ(Proj 𝒜, W))) =
      (Proj.unitToTwist (ψ.map_mem ha)).app (r ⁻¹ᵁ W)
        (1 : Γ(Proj ℬ, r ⁻¹ᵁ W)) := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  have hx := hθ (0 + n) n 0 a 1 ha (SetLike.one_mem_graded 𝒜) (by simp) W
    (by intro y hy; exact y.asHomogeneousIdeal.toIdeal.one_notMem)
    ((Proj.unitToTwist ha).app W (1 : Γ(Proj 𝒜, W)))
    (by intro y; simp [Proj.val_unitToTwist_app_apply, Localization.mk_one]) 1 x
  simpa [Proj.val_unitToTwist_app_apply, Localization.mk_one] using hx

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSection relProj relProjHom relProjι

/-- The normalized transition sends a degree-one homogeneous fraction to its restriction. -/
theorem twist_chart_transition_fraction
    (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
        Proj.twist (A.grading U) 1)
    (U V : S.affineOpens) (h : U ≤ V)
    (θ : ∀ j : ℤ,
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
          (Proj.twist (A.grading V) j) ≅ Proj.twist (A.grading U) j)
    (hθ : Proj.IsScalarExtensionTwistComparison (A.res h)
      (A.relProjFunctor.map (homOfLE h)) θ)
    (hsq :
      eqToIso (congrArg (fun f ↦
          (Scheme.Modules.tensorPullback f).obj L)
        (A.relProjFunctor_map_relProjι (homOfLE h)).symm) ≪≫
        (Scheme.Modules.tensorPullbackSectionComp
          (A.relProjFunctor.map (homOfLE h)) (A.relProjι V)).app L ≪≫
        (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).mapIso
          (chart V) ≪≫ θ 1 = chart U)
    (hopen : A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ A.twistChartOpen V =
      A.twistChartOpen U) :
    ∀ a : A.grading V 1,
      let t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
          Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
        ConcreteCategory.hom
          (((Scheme.Modules.tensorPullbackSectionAdjunction
              (A.relProjFunctor.map (homOfLE h))).unit.app
              (Proj.twist (A.grading V) 1)).app (A.twistChartOpen V) ≫
            (θ 1).hom.app
              (A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ A.twistChartOpen V) ≫
            eqToHom (congrArg
              (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen))
      t (A.twistChartFraction V a) =
        A.twistChartFraction U ⟨A.res h a, (A.res h).map_mem a.property⟩ := by
  have _ := hsq
  intro a
  let r := A.relProjFunctor.map (homOfLE h)
  let W := A.twistChartOpen V
  have hf : Proj.scalarExtensionTwistSection r θ 1 W (A.twistChartFraction V a) =
      (Proj.unitToTwist ((A.res h).map_mem a.property)).app (r ⁻¹ᵁ W)
        (1 : Γ(Proj (A.grading U), r ⁻¹ᵁ W)) :=
    normalized_homogeneousSection (A.res h) r θ hθ 1 a a.property W
  have hunit :
      (((Scheme.Modules.tensorPullbackSectionAdjunction r).unit.app
        (Proj.twist (A.grading V) 1)).app W (A.twistChartFraction V a)) =
        Scheme.Modules.tensorPullbackSection r (Proj.twist (A.grading V) 1) W
          (A.twistChartFraction V a) :=
    (Classical.choose_spec
      (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction r)).1
      (Proj.twist (A.grading V) 1) W (A.twistChartFraction V a)
  have transport (W W' : (Proj (A.grading U)).Opens) (e : W = W') :
      (eqToHom (congrArg (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) e))
        ((Proj.unitToTwist ((A.res h).map_mem a.property)).app W
          (1 : Γ(Proj (A.grading U), W))) =
        (Proj.unitToTwist ((A.res h).map_mem a.property)).app W'
          (1 : Γ(Proj (A.grading U), W')) := by
    subst W'
    rfl
  change (eqToHom (congrArg (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen))
    ((θ 1).hom.app (r ⁻¹ᵁ W)
      (((Scheme.Modules.tensorPullbackSectionAdjunction r).unit.app
        (Proj.twist (A.grading V) 1)).app W (A.twistChartFraction V a))) = _
  exact (congrArg (fun s ↦
    (eqToHom (congrArg (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen))
      ((θ 1).hom.app (r ⁻¹ᵁ W) s)) hunit).trans
    ((congrArg (fun s ↦
      (eqToHom (congrArg (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen)) s) hf).trans
        (transport _ _ hopen))

end AlgebraicGeometry.Scheme.GradedAlgebraData
