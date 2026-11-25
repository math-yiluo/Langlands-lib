/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility

/-! # Pullback of free abelian representable sheaves

Source: Stacks Project, Tags 03CB and 03Q8, inverse-image and evaluation adjunctions.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable def freeRepresentableHomEquiv (S : Scheme.{u}) (U : S.Etale)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((abelianComparisonFree S).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ _).trans
    (((AddCommGrpCat.adj.whiskerRight (C := S.Etaleᵒᵖ)).homEquiv _ _).trans
      uliftYonedaEquiv)

theorem freeRepresentableHomEquiv_comp (S : Scheme.{u}) (U : S.Etale)
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (x : (abelianComparisonFree S).obj U ⟶ F) (a : F ⟶ G) :
    freeRepresentableHomEquiv S U G (x ≫ a) =
      a.hom.app (op U) (freeRepresentableHomEquiv S U F x) := by
  rfl

/-- Pullback of the free abelian sheaf on U is the free abelian sheaf on its
scheme-theoretic pullback. Both objects corepresent sections on that pullback:
apply inverse-image/direct-image adjunction, sheafification, the free abelian
adjunction, and Yoneda. Naturality in the coefficient sheaf gives the unique
representing isomorphism. Empty U is included in the same adjunction argument.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: def-sc-abelian-free-representable-pullback). -/
noncomputable def abelianFreeRepresentablePullbackIso {S T : Scheme.{u}}
    (a : T ⟶ S) (U : S.Etale) :
    ((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree S).obj U) ≅
      (abelianComparisonFree T).obj (a.Etale.obj U) := by
  let e (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).homEquiv _ F).trans
      ((freeRepresentableHomEquiv S U (((a)_*[AddCommGrpCat.{u + 1}]).obj F)).trans
        (freeRepresentableHomEquiv T (a.Etale.obj U) F).symm)
  have he {F G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (x : ((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree S).obj U) ⟶ F)
      (b : F ⟶ G) : e G (x ≫ b) = e F x ≫ b := by
    apply (freeRepresentableHomEquiv T (a.Etale.obj U) G).injective
    simp only [e, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_right, freeRepresentableHomEquiv_comp]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  exact Coyoneda.ext _ _ (fun x ↦ e _ x) (fun x ↦ (e _).symm x)
    (fun x ↦ (e _).symm_apply_apply x) (fun x ↦ (e _).apply_symm_apply x) (fun x b ↦ by
      apply (e _).injective
      rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- The same free-sheaf comparison for a specified pullback square, with the
free sheaf on its given apex rather than on a chosen fibre product.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: def-sc-abelian-free-representable-pullback). -/
noncomputable def abelianFreeRepresentablePullbackSquareIso {S T : Scheme.{u}}
    (a : T ⟶ S) (V : S.Etale) (U : T.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a) :
    (abelianComparisonFree T).obj U ≅
      ((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree S).obj V) := by
  let e : U ≅ a.Etale.obj V :=
    MorphismProperty.Over.isoMk hr.isoPullback (by
      change hr.isoPullback.hom ≫ pullback.snd V.hom a = U.hom
      simp)
  exact (abelianComparisonFree T).mapIso e ≪≫
    (abelianFreeRepresentablePullbackIso a V).symm

end AlgebraicGeometry.Etale
