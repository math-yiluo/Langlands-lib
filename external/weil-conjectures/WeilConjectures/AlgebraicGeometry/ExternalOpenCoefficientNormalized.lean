/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import WeilConjectures.AlgebraicGeometry.TensorPullbackOpenTriangle
import WeilConjectures.AlgebraicGeometry.TensorPullbackOpenSquare

/-! # Normalized open-base-change isomorphism of external coefficients

Source: Stacks Project, Tags 0BED, 0096, 0097 and 01CD.
(blueprint: lem-sc-external-open-coefficient-normalized).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

-- Tensor section transports require additional elaboration of restriction instances.
private theorem restriction_tensor_hom_tmul {A B : Scheme.{w}}
    (j : A ⟶ B) [IsOpenImmersion j] (M N : B.Modules)
    (e : (MonoidalCategory.tensorObj M N).restrict j ≅
      MonoidalCategory.tensorObj (M.restrict j) (N.restrict j))
    (he : ∀ (U : A.Opens) (s : Γ(M.restrict j, U)) (t : Γ(N.restrict j, U)),
      ((MonoidalCategory.tensorObj M N).restrictAppIso j U).hom (e.inv.app U (tmulSection s t)) =
        tmulSection ((M.restrictAppIso j U).hom s) ((N.restrictAppIso j U).hom t))
    (U : B.Opens) (h : j ''ᵁ ⊤ = U) (s : Γ(M, U)) (t : Γ(N, U)) :
    e.hom.app ⊤ ((MonoidalCategory.tensorObj M N).presheaf.map (eqToHom h).op (tmulSection s t)) =
      tmulSection (M := M.restrict j) (N := N.restrict j)
        (M.presheaf.map (eqToHom h).op s) (N.presheaf.map (eqToHom h).op t) := by
  have ht := tmulSection_map (M := M) (N := N) (leOfHom (eqToHom h)) s t
  have hh : homOfLE (leOfHom (eqToHom h)) = eqToHom h := Subsingleton.elim _ _
  simp only [hh] at ht
  have hi := he ⊤ (M.presheaf.map (eqToHom h).op s)
    (N.presheaf.map (eqToHom h).op t)
  change e.inv.app ⊤ (tmulSection (M := M.restrict j) (N := N.restrict j)
      (M.presheaf.map (eqToHom h).op s) (N.presheaf.map (eqToHom h).op t)) =
    tmulSection (M := M) (N := N)
      (M.presheaf.map (eqToHom h).op s) (N.presheaf.map (eqToHom h).op t) at hi
  apply Eq.trans (congrArg
    (fun x : Γ((MonoidalCategory.tensorObj M N).restrict j, ⊤) ↦ e.hom.app ⊤ x)
    (ht.trans hi.symm))
  exact congrArg (fun a ↦ a.app ⊤ (tmulSection
    (M := M.restrict j) (N := N.restrict j)
    (M.presheaf.map (eqToHom h).op s) (N.presheaf.map (eqToHom h).op t)))
    e.inv_hom_id

-- Tensor section transports require additional elaboration of restriction instances.
/-- Restriction of the external coefficient to an open base change, normalized on
sections by the pullback units.
Source: Stacks Project, Tag 0BED, omitted canonical-cup verification; Tags 0096,
0097 and 01CD.
(blueprint: lem-sc-external-open-coefficient-normalized).

Proof: use the proved restriction-tensor comparison to identify the restricted
coefficient with the tensor of the restricted factors. The normalized open-triangle
comparison identifies the first factor with the new first-projection pullback by
hfst. The normalized open-square comparison identifies the second factor with the
new second-projection pullback of the restricted G, using hj and hsnd. Tensor these
two factor isomorphisms and compose with the restriction-tensor isomorphism.
Its inverse pure-section equation, together with naturality of tensor sections,
gives the forward equation after transport along hj. The triangle section formula
and composition of restriction maps identify the first section with the new first
projection unit. The square formula identifies the second section with the new
second projection unit of the transported section of G. tensorHom_app_tmulSection
combines them. Every comparison also applies to the empty open.
-/
theorem exists_externalOpenCoefficient_normalized
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (V : Y.Opens)
    (j : Limits.pullback f (V.ι ≫ g) ⟶ Limits.pullback f g) [IsOpenImmersion j]
    (hj : j ''ᵁ ⊤ = pullback.snd f g ⁻¹ᵁ V)
    (hfst : j ≫ pullback.fst f g = pullback.fst f (V.ι ≫ g))
    (hsnd : j ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι) :
    ∃ κ : (externalCupCoefficients f g F G).restrict j ≅
        externalCupCoefficients f (V.ι ≫ g) F (G.restrict V.ι),
      ∀ (s : Γ(F, ⊤)) (t : Γ(G, V)),
        κ.hom.app ⊤
          ((externalCupCoefficients f g F G).presheaf.map (eqToHom hj).op
            (tmulSection (M := (tensorPullback (pullback.fst f g)).obj F)
              (N := (tensorPullback (pullback.snd f g)).obj G)
              (((tensorPullback (pullback.fst f g)).obj F).presheaf.map
                (homOfLE (by simp : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ ⊤)).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.fst f g))).unit.app F).app ⊤ s))
              (((Classical.choose (exists_tensorPullbackAdjunction
                (pullback.snd f g))).unit.app G).app V t))) =
          tmulSection (M := (tensorPullback (pullback.fst f (V.ι ≫ g))).obj F)
            (N := (tensorPullback (pullback.snd f (V.ι ≫ g))).obj (G.restrict V.ι))
            (tensorPullbackTopSection (pullback.fst f (V.ι ≫ g)) F s)
            (tensorPullbackTopSection (pullback.snd f (V.ι ≫ g)) (G.restrict V.ι)
              (G.presheaf.map (eqToHom (by simp : V.ι ''ᵁ ⊤ = V)).op t)) := by
  let M := (tensorPullback (pullback.fst f g)).obj F
  let N := (tensorPullback (pullback.snd f g)).obj G
  obtain ⟨eR, heR⟩ := exists_restriction_tensor_comparison j M N
  obtain ⟨eF, heF⟩ := exists_tensorPullback_openTriangle j (pullback.fst f g)
    (pullback.fst f (V.ι ≫ g)) hfst F
  obtain ⟨eG, heG⟩ := exists_tensorPullback_openSquare j (pullback.snd f g) V
    (pullback.snd f (V.ι ≫ g)) hj hsnd G
  refine ⟨eR ≪≫ (MonoidalCategory.tensorIso eF eG), ?_⟩
  intro s t
  let ss := M.presheaf.map
    (homOfLE (by simp : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ ⊤)).op
    (((Classical.choose (exists_tensorPullbackAdjunction
      (pullback.fst f g))).unit.app F).app ⊤ s)
  let tt := ((Classical.choose (exists_tensorPullbackAdjunction
    (pullback.snd f g))).unit.app G).app V t
  have hr := restriction_tensor_hom_tmul j M N eR heR _ hj ss tt
  change (MonoidalCategory.tensorHom eF.hom eG.hom).app ⊤
    (eR.hom.app ⊤ ((MonoidalCategory.tensorObj M N).presheaf.map
      (eqToHom hj).op (tmulSection ss tt))) = _
  rw [hr, tensorHom_app_tmulSection]
  have hF : eF.hom.app ⊤ (M.presheaf.map (eqToHom hj).op ss) =
      tensorPullbackTopSection (pullback.fst f (V.ι ≫ g)) F s := by
    dsimp only [ss]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact heF s
  rw [hF]
  exact congrArg (tmulSection
    (M := (tensorPullback (pullback.fst f (V.ι ≫ g))).obj F)
    (N := (tensorPullback (pullback.snd f (V.ι ≫ g))).obj (G.restrict V.ι))
    (tensorPullbackTopSection (pullback.fst f (V.ι ≫ g)) F s)) (heG t)

end
end AlgebraicGeometry.Scheme.Modules
