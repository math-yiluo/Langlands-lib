/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Components of module base change under restriction

Source: Stacks Project, Sheaves, Tag 00A0 and Cohomology, Tags 0ATL and 0ATM.
(blueprint: lem-weil-pbc-module-open-square-isiso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The adjoint-defined base change map of a full inverse-image open square is an
isomorphism, for every module; no quasi-coherence assumption is required.
Source: Stacks Project, Sheaves, Lemma 00A0, parts (2) and (5) and its module variant;
Cohomology on Sites, Remark 08HY for the adjoint-defined map.
(blueprint: lem-weil-pbc-module-open-square-isiso)

Proof: identify tensor pullback along jU and jX with restriction using uniqueness of
left adjoints to their pushforwards. These identifications preserve the units.
On an open W of U, the source has sections F(f⁻¹(jU(W))), while the target has
sections F(jX(fU⁻¹(W))). The commutative square gives one inclusion of these opens.
For the other, a point whose image lies in jU(W) lies in the image of jX by the
full inverse-image hypothesis; injectivity of jU then places its preimage in fU⁻¹(W).
Thus the opens are equal. Under this equality the adjoint of the identity section map
is precisely the pushforward of the jX restriction unit, followed by the pushforward
composition comparisons. Injectivity of the jU Hom equivalence identifies its mate
with bc. The identity section maps are invertible and commute with all restrictions
and scalar actions; they therefore give an isomorphism of modules. Transport through
the two restriction/pullback identifications proves the claim. This argument also
covers empty opens and isomorphisms of schemes. -/
theorem moduleBaseChangeMap_open_square_isIso
    {X S U XU : Scheme.{u}} (f : X ⟶ S) (fU : XU ⟶ U)
    (jU : U ⟶ S) (jX : XU ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jX]
    (hf : jX ≫ f = fU ≫ jU) (hX : Set.range jX = f ⁻¹' Set.range jU)
    (F : X.Modules) :
    let bc : ∀ {A B C D : Scheme.{u}} (p : A ⟶ B) (q : C ⟶ D)
        (r : D ⟶ B) (s : C ⟶ A) (_hs : s ≫ p = q ≫ r) (M : A.Modules),
        (tensorPullback r).obj ((pushforward p).obj M) ⟶
          (pushforward q).obj ((tensorPullback s).obj M) :=
      fun {_A _B _C _D : Scheme.{u}} p q r s hs M ↦
        ((Classical.choose (exists_tensorPullbackAdjunction r)).homEquiv _ _).symm
          ((pushforward p).map
            ((Classical.choose (exists_tensorPullbackAdjunction s)).unit.app M) ≫
            (pushforwardComp s p).hom.app ((tensorPullback s).obj M) ≫
            (pushforwardCongr hs).hom.app ((tensorPullback s).obj M) ≫
            (pushforwardComp q r).inv.app ((tensorPullback s).obj M))
    IsIso (bc f fU jU jX hf F) := by
  intro bc
  let aU := restrictAdjunction jU
  let aX := restrictAdjunction jX
  let tU := Classical.choose (exists_tensorPullbackAdjunction jU)
  let tX := Classical.choose (exists_tensorPullbackAdjunction jX)
  let eU := aU.leftAdjointUniq tU
  let eX := aX.leftAdjointUniq tX
  let q : pushforward jX ⋙ pushforward f ⟶ pushforward fU ⋙ pushforward jU :=
    (pushforwardComp jX f).hom ≫ (pushforwardCongr hf).hom ≫
      (pushforwardComp fU jU).inv
  let d := ((aU.homEquiv _ _).symm
    ((pushforward f).map (aX.unit.app F) ≫ q.app ((restrictFunctor jX).obj F)))
  have he (W : U.Opens) : f ⁻¹ᵁ (jU ''ᵁ W) = jX ''ᵁ (fU ⁻¹ᵁ W) := by
    have hp (y : XU) : f (jX y) = jU (fU y) :=
      congrArg (fun k : XU ⟶ S ↦ k y) hf
    ext x
    change f x ∈ jU '' (W : Set U) ↔ x ∈ jX '' (fU ⁻¹' (W : Set U))
    constructor
    · rintro ⟨w, hw, hfw⟩
      have hx : x ∈ Set.range jX := by
        rw [hX]
        exact ⟨w, hfw⟩
      obtain ⟨y, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      have hy : fU y = w := jU.isOpenEmbedding.injective ((hp y).symm.trans hfw.symm)
      simpa only [Set.mem_preimage, hy] using hw
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fU y, hy, (hp y).symm⟩
  have hi {A B : (TopologicalSpace.Opens X)ᵒᵖ} (e : A = B) (k : A ⟶ B) :
      IsIso k := by
    subst B
    have hk : k = 𝟙 A := Subsingleton.elim _ _
    rw [hk]
    infer_instance
  have hd : IsIso d := by
    apply Hom.isIso_iff_isIso_app.mpr
    intro W
    dsimp only [d, aU]
    rw [Adjunction.homEquiv_counit]
    simp only [Hom.comp_app, restrictAdjunction_counit_app_app, Functor.map_comp]
    change IsIso ((((pushforward f).map (aX.unit.app F)).app (jU ''ᵁ W) ≫
      (q.app ((restrictFunctor jX).obj F)).app (jU ''ᵁ W)) ≫ _)
    dsimp only [q, aX]
    simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
      NatTrans.comp_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    change IsIso (F.presheaf.map _ ≫ F.presheaf.map _ ≫ F.presheaf.map _)
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine @Functor.map_isIso _ _ _ _ _ _ F.presheaf _ ?_
    exact hi (congrArg Opposite.op (he W)) _
  have hbAdj : tU.unit.app ((pushforward f).obj F) ≫
      (pushforward jU).map (bc f fU jU jX hf F) =
      (pushforward f).map (tX.unit.app F) ≫ q.app ((tensorPullback jX).obj F) := by
    exact (tU.homEquiv _ _).apply_symm_apply _
  have hdAdj : aU.unit.app ((pushforward f).obj F) ≫ (pushforward jU).map d =
      (pushforward f).map (aX.unit.app F) ≫ q.app ((restrictFunctor jX).obj F) := by
    exact (aU.homEquiv _ _).apply_symm_apply _
  have hcompat : eU.hom.app ((pushforward f).obj F) ≫ bc f fU jU jX hf F =
      d ≫ (pushforward fU).map (eX.hom.app F) := by
    apply (aU.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app]
    rw [hbAdj, hdAdj]
    have hn := q.naturality (eX.hom.app F)
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn]
    rw [← Category.assoc, ← Functor.map_comp, Adjunction.unit_leftAdjointUniq_hom_app]
  have : IsIso (eU.hom.app ((pushforward f).obj F) ≫ bc f fU jU jX hf F) := by
    rw [hcompat]
    infer_instance
  exact IsIso.of_isIso_comp_left (eU.hom.app ((pushforward f).obj F)) _

end
end AlgebraicGeometry.Scheme.Modules
