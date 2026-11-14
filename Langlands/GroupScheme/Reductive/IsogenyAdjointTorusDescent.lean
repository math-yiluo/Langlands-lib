import Langlands.GroupScheme.Adjoint.SplitTorus
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.AutomorphicActionPointIso
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of local torus conjugators to a supplied adjoint torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

private theorem fppfCover_effectiveEpiFamily {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S) :
    EffectiveEpiFamily 𝒰.X 𝒰.f := by
  apply (Sieve.effectiveEpimorphic_family 𝒰.X 𝒰.f).mp
  apply (Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mpr
  intro Y
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) (yoneda.obj Y)).isSheafFor _
      𝒰.mem_grothendieckTopology


private theorem exists_basePoint_of_fppf_local_points {S : Scheme.{u}} (Y : Over S)
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (s : ∀ a : 𝒰.I₀, Over.mk (𝒰.f a) ⟶ Y)
    (hs : ∀ (V : Over S) (a b : 𝒰.I₀)
      (g₁ : V ⟶ Over.mk (𝒰.f a)) (g₂ : V ⟶ Over.mk (𝒰.f b)),
      g₁ ≫ s a = g₂ ≫ s b) :
    ∃ x : Over.mk (𝟙 S) ⟶ Y,
      ∀ a : 𝒰.I₀, Over.homMk (𝒰.f a) (by simp) ≫ x = s a := by
  let := fppfCover_effectiveEpiFamily 𝒰
  let e : ∀ a : 𝒰.I₀, 𝒰.X a ⟶ Y.left := fun a => (s a).left
  have he : ∀ {Z : Scheme.{u}} (a b : 𝒰.I₀) (g₁ : Z ⟶ 𝒰.X a)
      (g₂ : Z ⟶ 𝒰.X b), g₁ ≫ 𝒰.f a = g₂ ≫ 𝒰.f b →
      g₁ ≫ e a = g₂ ≫ e b := by
    intro Z a b g₁ g₂ hg
    exact congrArg (fun f => f.left)
      (hs (Over.mk (g₁ ≫ 𝒰.f a)) a b
        (Over.homMk g₁ rfl) (Over.homMk g₂ hg.symm))
  let x₀ := EffectiveEpiFamily.desc 𝒰.X 𝒰.f e he
  have hx₀ : x₀ ≫ Y.hom = 𝟙 S := by
    apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
    intro a
    rw [← Category.assoc, EffectiveEpiFamily.fac]
    exact (s a).w.trans (Category.comp_id _).symm
  refine ⟨Over.homMk x₀ hx₀, ?_⟩
  intro a
  apply Over.OverMorphism.ext
  exact EffectiveEpiFamily.fac 𝒰.X 𝒰.f e he a

/-- A torus point conjugates the second homomorphism into the first on every
relative test scheme. This is the predicate used in the general rigidity statement. -/
def TorusConjugates {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
    (i : T.toGrp ⟶ H) (f F : G ⟶ H) {V : Over S} (t : V ⟶ T.X) : Prop :=
  ∀ (U : Over S) (a : U ⟶ V) (g : U ⟶ G.X),
    g ≫ f.hom.hom =
      (a ≫ t ≫ i.hom.hom) * (g ≫ F.hom.hom) * (a ≫ t ≫ i.hom.hom)⁻¹

/-- Conjugating points remain conjugating after restriction to any test scheme. -/
theorem TorusConjugates.comp {S : Scheme.{u}} {G H : GroupScheme S}
    {T : CommGroupScheme S} {i : T.toGrp ⟶ H} {f F : G ⟶ H}
    {V W : Over S} {t : V ⟶ T.X} (ht : TorusConjugates i f F t) (b : W ⟶ V) :
    TorusConjugates i f F (b ≫ t) := by
  intro U a g
  simpa only [Category.assoc] using ht U (a ≫ b) g

namespace IsAdjointSplitTorusImage

variable {k : Type u} [Field k]
    {H A : GroupScheme (Spec (CommRingCat.of k))}
    {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
    {q : H ⟶ A} {i : T.toGrp ⟶ H} {j : T_ad.toGrp ⟶ A} {π : T ⟶ T_ad}
    (h : IsAdjointSplitTorusImage q i j π)

include h in
/-- Two torus points whose difference is central have the same actual adjoint-torus image. -/
theorem point_comp_eq_of_difference_central
    {V : Over (Spec (CommRingCat.of k))} (s t : V ⟶ T.X)
    (hc : (s ≫ i.hom.hom)⁻¹ * (t ≫ i.hom.hom) ∈ (center H).carrier V) :
    s ≫ (CommGroupScheme.groupHom π).hom.hom =
      t ≫ (CommGroupScheme.groupHom π).hom.hom := by
  have he := (h.comp_eq_one_iff_mem_center V (s⁻¹ * t)).mpr (by
    simpa only [MonObj.mul_comp, GrpObj.inv_comp] using hc)
  rw [MonObj.mul_comp, GrpObj.inv_comp, inv_mul_eq_one] at he
  exact he


set_option maxHeartbeats 800000 in
include h in
/-- Local torus conjugators with central differences descend to an actual
rational point of the supplied adjoint torus, inducing the prescribed homomorphism. -/
theorem exists_basePoint_of_local_conjugates
    {G : GroupScheme (Spec (CommRingCat.of k))} (f F : G ⟶ H)
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
      (Spec (CommRingCat.of k)))
    (t : ∀ a : 𝒰.I₀, Over.mk (𝒰.f a) ⟶ T.X)
    (ht : ∀ a : 𝒰.I₀, TorusConjugates i f F (t a))
    (hc : ∀ (V : Over (Spec (CommRingCat.of k))) (s t : V ⟶ T.X),
      TorusConjugates i f F s → TorusConjugates i f F t →
      (s ≫ i.hom.hom)⁻¹ * (t ≫ i.hom.hom) ∈ (center H).carrier V) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T_ad.X,
      F ≫ (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom = f := by
  obtain ⟨x, hx⟩ := exists_basePoint_of_fppf_local_points T_ad.X 𝒰
    (fun a => t a ≫ (CommGroupScheme.groupHom π).hom.hom) (by
      intro V a b g₁ g₂
      simpa only [Category.assoc] using h.point_comp_eq_of_difference_central
        (g₁ ≫ t a) (g₂ ≫ t b) (hc V _ _ ((ht a).comp g₁) ((ht b).comp g₂)))
  refine ⟨x, ?_⟩
  have hx_local (a : 𝒰.I₀) (V : Over (Spec (CommRingCat.of k)))
      (b : V ⟶ Over.mk (𝒰.f a)) :
      A.constantPoint (x ≫ j.hom.hom) V = b ≫ t a ≫ i.hom.hom ≫ q.hom.hom := by
    have hb : (Over.homMk V.hom (by simp) : V ⟶ Over.mk (𝟙 _)) =
        b ≫ (Over.homMk (𝒰.f a) (by simp) :
          Over.mk (𝒰.f a) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      apply Over.OverMorphism.ext
      exact b.w.symm
    change (Over.homMk V.hom (by simp) ≫ x) ≫ j.hom.hom = _
    rw [hb, Category.assoc b _ x, hx a]
    have hsquare := congrArg (fun z : T.toGrp ⟶ A => z.hom.hom) h.comp_eq
    change (CommGroupScheme.groupHom π).hom.hom ≫ j.hom.hom =
      i.hom.hom ≫ q.hom.hom at hsquare
    simpa only [Category.assoc] using congrArg (fun z => b ≫ t a ≫ z) hsquare
  apply hom_ext_points
  intro V g
  apply Over.OverMorphism.ext
  let 𝒱 := 𝒰.pullback₁ V.hom
  let := fppfCover_effectiveEpiFamily 𝒱
  apply EffectiveEpiFamily.hom_ext 𝒱.X 𝒱.f
  intro a
  let W := Over.mk (𝒱.f a ≫ V.hom)
  let b : W ⟶ V := Over.homMk (𝒱.f a) rfl
  let c : W ⟶ Over.mk (𝒰.f a) :=
    Over.homMk (𝒰.pullbackHom V.hom a) (𝒰.pullbackHom_map V.hom a)
  have he : b ≫ g ≫
      (F ≫ (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom).hom.hom =
      b ≫ g ≫ f.hom.hom := by
    rw [Grp.comp_hom_hom, ← Category.assoc b g, ← Category.assoc,
      AutomorphicAction.comp_basePointIso_hom, hx_local a W c,
      ← Category.assoc c (t a), ← Category.assoc,
      h.isAdjointQuotient.innerAction_act_lift]
    exact (ht a W c (b ≫ g)).symm
  exact congrArg (fun z => z.left) he

end IsAdjointSplitTorusImage
end Langlands.GroupScheme
