/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComposition

/-! # Coherence of chart pullback comparisons

Source: Stacks Project, Tags 0095 and 0096; Mathlib's pullback pseudofunctor.
(blueprint: lem-pc-chart-tensor-pullback-comparison-coherence).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two comparison paths from an iterated ordinary chart pullback to the
restriction of an iterated tensor pullback agree, on a single module, for any
chart refinement v satisfying the two projection equations. The supplied ordinary
comparison isomorphisms d and b are required to equal the canonical constructions.
Source: Stacks Project, Tags 0095 and 0096, composition of pullback;
Mathlib `Scheme.Modules.pseudofunctor_associativity` and
`Adjunction.leftAdjointCompIso_assoc`.
(blueprint: lem-pc-chart-tensor-pullback-comparison-coherence).

Proof: First substitute the supplied equalities identifying d and b with the
canonical comparisons. Identify the tensor pullbacks with ordinary pullbacks using the comparison
of their pinned adjunctions to the same pushforward. By the defining mate formula,
the tensor compositor becomes the ordinary compositor followed by pullbackCongr(w).
After this substitution, both paths are composites of ordinary pullbackComp and
pullbackCongr comparisons. Apply ordinary pullback associativity to the paths through
v, the direct chart projection and q₀, and to the paths through the two iterated chart
projections and U.f(a). The supplied first and second projection equations for v identify
the resulting composites of scheme maps. Equality transport (pullbackCongr) respects
these equations by equality induction. The two reduced composites are consequently
the same. Equivalently, take right mates of both paths: they are the same pushforward
composition comparison, since pushforward composition is sectionwise the identity;
injectivity of the mate equivalence gives equality of the left paths. No map between
modules or recovery hypothesis enters this comparison identity. -/
theorem chart_tensor_pullback_comparison_coherence
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (q₀ : Z ⟶ X)
    (w : p ≫ q = q₀) (U : X.OpenCover.{u}) (a : U.I₀) (F : X.Modules) :
    let Uk : Y.OpenCover.{u} := U.pullback₁ q
    let V : Z.OpenCover.{u} := Uk.pullback₁ p
    let W : Z.OpenCover.{u} := U.pullback₁ q₀
    ∀ (v : V.X a ⟶ W.X a)
      (hv₁ : v ≫ W.f a = V.f a)
      (hv₂ : v ≫ U.pullbackHom q₀ a = Uk.pullbackHom p a ≫ U.pullbackHom q a),
    ∀ (d : Scheme.Modules.pullback (U.pullbackHom q₀ a) ⋙ Scheme.Modules.pullback v ≅
        Scheme.Modules.pullback (U.pullbackHom q a) ⋙
          Scheme.Modules.pullback (Uk.pullbackHom p a)),
    d = Scheme.Modules.pullbackComp v (U.pullbackHom q₀ a) ≪≫
      Scheme.Modules.pullbackCongr hv₂ ≪≫
      (Scheme.Modules.pullbackComp (Uk.pullbackHom p a) (U.pullbackHom q a)).symm →
    ∀ (b : Scheme.Modules.pullback (W.f a) ⋙ Scheme.Modules.pullback v ≅
        Scheme.Modules.pullback (V.f a)),
    b = Scheme.Modules.pullbackComp v (W.f a) ≪≫
      Scheme.Modules.pullbackCongr hv₁ →
    let tq := Scheme.Modules.openCoverTensorPullbackComparison q U a
    let tp := Scheme.Modules.openCoverTensorPullbackComparison p Uk a
    let t₀ := Scheme.Modules.openCoverTensorPullbackComparison q₀ U a
    let e := Scheme.Modules.tensorPullbackCompositionIso p q q₀ w
    (Scheme.Modules.pullback (Uk.pullbackHom p a)).map (tq.hom.app F) ≫
        tp.hom.app ((Scheme.Modules.tensorPullback q).obj F) =
      d.inv.app ((Scheme.Modules.pullback (U.f a)).obj F) ≫
        (Scheme.Modules.pullback v).map (t₀.hom.app F) ≫
        b.hom.app ((Scheme.Modules.tensorPullback q₀).obj F) ≫
        (Scheme.Modules.pullback (V.f a)).map (e.hom.app F) := by
  classical
  dsimp only
  intro v hv₁ hv₂ d hd b hb
  subst d b
  -- The projection equations force v to be the canonical chart isomorphism.
  let s : ((U.pullback₁ q).pullback₁ p).X a ≅ (U.pullback₁ q₀).X a :=
    pullbackRightPullbackFstIso q (U.f a) p ≪≫ pullback.congrHom w rfl
  have hs₁ : s.hom ≫ (U.pullback₁ q₀).f a = ((U.pullback₁ q).pullback₁ p).f a := by
    change ((pullbackRightPullbackFstIso q (U.f a) p).hom ≫
      (pullback.congrHom w rfl).hom) ≫ pullback.fst q₀ (U.f a) =
        pullback.fst p (pullback.fst q (U.f a))
    simp
  have hs₂ : s.hom ≫ U.pullbackHom q₀ a =
      Scheme.Cover.pullbackHom (U.pullback₁ q) p a ≫ U.pullbackHom q a := by
    change ((pullbackRightPullbackFstIso q (U.f a) p).hom ≫
      (pullback.congrHom w rfl).hom) ≫ pullback.snd q₀ (U.f a) =
        pullback.snd p (pullback.fst q (U.f a)) ≫ pullback.snd q (U.f a)
    simp
  have hvs : v = s.hom := by
    apply pullback.hom_ext
    · exact hv₁.trans hs₁.symm
    · exact hv₂.trans hs₂.symm
  subst v
  -- Reuse the composition square, then move the ordinary comparison to the other side.
  have h := Scheme.Modules.openCoverTensorPullbackComparison_composition
    q p q₀ w U a s hs₁ hs₂ F
  dsimp only at h
  rw [← cancel_epi
    ((Scheme.Modules.pullbackComp s.hom (U.pullbackHom q₀ a) ≪≫
      Scheme.Modules.pullbackCongr hs₂ ≪≫
      (Scheme.Modules.pullbackComp (Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (U.pullbackHom q a)).symm).hom.app
          ((Scheme.Modules.pullback (U.f a)).obj F))]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h.symm

end AlgebraicGeometry
