/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda

/-!
# Inverse images of representable abelian sheaves

If the underlying sheaf of sets of an abelian sheaf `G` on the small étale site of `S` is
represented by an étale `S`-scheme `P`, then the underlying sheaf of sets of its inverse image
along `i : Z ⟶ S` is represented by the base change `P ×_S Z`. In particular it is finite
locally constant when this base change is finite over `Z`.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb
(representables commute with inverse image; finite étale representables are finite locally
constant; forgetting abelian groups commutes with inverse image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Transport finite local constancy along an isomorphism of sheaves of sets. -/
private theorem isFiniteLocallyConstantSheafOfTypes_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
    (hF : IsFiniteLocallyConstantSheafOfTypes F) :
    IsFiniteLocallyConstantSheafOfTypes G := by
  obtain ⟨⟨𝒰, h𝒰⟩, hf⟩ := hF
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · have := h𝒰 i
    exact Sheaf.isConstant_congr _ ((X.smallEtaleTopology.overPullback _ _).mapIso e)
  · exact (hf.isFinitelyGenerated_sheafFiber Ω s).of_iso ((pointSmallEtale s).sheafFiber.mapIso e)

/-- If the underlying sheaf of sets of an abelian sheaf `G` is represented by an étale
`S`-scheme `P`, and the base change of `P` along `i : Z ⟶ S` is finite, then the underlying
sheaf of sets of the inverse image of `G` along `i` is finite locally constant.

Proof: forgetting abelian groups commutes with inverse image
(`etaleInverseImageAlgebraicStructures`), the inverse image of sheaves of sets sends the sheaf
represented by `P` to the sheaf represented by `P ×_S Z`
(`Adjunction.uliftYonedaCompIso`), and the sheaf represented by a finite étale scheme is
finite locally constant (`isFiniteLocallyConstant_uliftYoneda`). -/
theorem isFiniteLocallyConstant_forget_upperStar_of_iso_uliftYoneda {S Z : Scheme.{u}}
    (i : Z ⟶ S) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (P : S.Etale)
    (e : (sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G ≅
      S.smallEtaleTopology.uliftYoneda.{u + 1}.obj P)
    [IsFinite (pullback.snd P.hom i)] :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Z.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} i).obj G)) := by
  obtain ⟨-, ea, -⟩ := etaleInverseImageAlgebraicStructures Z S i
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    i.Etale (Type (u + 1)) S.smallEtaleTopology Z.smallEtaleTopology
  let Q : Z.Etale := i.Etale.obj P
  have : IsFinite Q.hom := ‹IsFinite (pullback.snd P.hom i)›
  obtain ⟨h, hloc, hfin⟩ := isFiniteLocallyConstant_uliftYoneda (T := Z) Q.left Q.hom
  refine isFiniteLocallyConstantSheafOfTypes_of_iso
    ((adj.uliftYonedaCompIso.app P).symm ≪≫ (etaleSetPullback i).mapIso e.symm ≪≫
      (ea.app G).symm) ⟨hloc, hfin⟩

end AlgebraicGeometry.Scheme
