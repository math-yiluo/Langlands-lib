/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.GenericFinitePushforward
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleNoetherianCriterion
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Finite pushforward preserves constructibility over a Noetherian scheme

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1579;
Stacks Project, Lemma 59.73.9 (Tag 095R)
(blueprint: lemma-detection-proper-direct-image--1).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Lissity of set sheaves is invariant under isomorphism. -/
private theorem lisse_of_iso {T : Scheme.{u}}
    {F G : Sheaf T.smallEtaleTopology (Type (u + 1))}
    (e : F ≅ G) (hF : IsLisseEtaleSheafOfSets F) : IsLisseEtaleSheafOfSets G := by
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := hF
  refine ⟨⟨𝒰, ?_⟩, ?_⟩
  · intro i
    have := h𝒰 i
    exact Sheaf.isConstant_congr _
      ((T.smallEtaleTopology.overPullback (Type (u + 1))
        (𝒰.etalePrecoverageToEtale i)).mapIso e)
  · refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ t ↦ ?_
    have := (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
      (hfin.isFinitelyGenerated_sheafFiber Ω t)
    exact Finite.of_equiv _
      (((pointSmallEtale t).sheafFiber (A := Type (u + 1))).mapIso e).toEquiv

/-- The direct image of a constructible abelian etale sheaf along a finite morphism
with Noetherian target is constructible. Constructibility is that of the underlying
set sheaf, with finite geometric stalks on constructible locally closed strata.

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1579;
Stacks Project, Tag 095R
(blueprint: lemma-detection-proper-direct-image--1).

Proof: Apply `isConstructibleEtaleSheafOfSets_of_generic_lisse`, which packages the
Noetherian induction of steps 2 and 3. For each integral Noetherian affine subscheme S,
form the Cartesian square V ×_U S. The new finite-stalk pullback lemma of step 1 makes
the pulled-back abelian sheaf constructible in precisely the set-sheaf sense used here.
The existing generic finite-pushforward theorem supplies a dense lisse open W of S.
Finite exchange gives an isomorphism between the abelian pullback of h_*E and this
base-changed direct image. `etaleInverseImageAlgebraicStructures` identifies underlying
abelian inverse image with set inverse image. Forget the exchange isomorphism and pull
it back to W, then transport lissity across the resulting set-sheaf isomorphism. The
criterion now supplies the finite constructible stratification on U. No Krull dimension
bound and no identification of finite stalks with finitely generated stalks is used. -/
theorem isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian
    {U V : Scheme.{u}} [IsNoetherian U] (h : V ⟶ U) [IsFinite h]
    (E : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose V.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose U.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj E)) := by
  classical
  apply isConstructibleEtaleSheafOfSets_of_generic_lisse U
  intro S _ _ _ g _
  let E' := (Etale.upperStar AddCommGrpCat.{u + 1} (Limits.pullback.fst h g)).obj E
  have hE' : IsConstructibleEtaleSheafOfSets
      ((sheafCompose (Limits.pullback h g).smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E') :=
    isConstructibleEtaleSheafOfSets_upperStar (Limits.pullback.fst h g) E hE
  obtain ⟨W, hW, hL⟩ := exists_dense_open_lisse_finite_directImage S
    (Limits.pullback.snd h g) E' hE'
  let ea := (AlgebraicGeometry.etaleInverseImageAlgebraicStructures S U g).2.choose
  have := Etale.isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback h g)
  let bc := asIso ((Etale.baseChangeMap AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback h g).toCommSq).app E)
  let e : (etaleSetPullback g).obj
      ((sheafCompose U.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj E)) ≅
      (sheafCompose S.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} (Limits.pullback.snd h g)).obj E') :=
    (ea.app ((Etale.lowerStar AddCommGrpCat.{u + 1} h).obj E)).symm ≪≫
      (sheafCompose S.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso bc
  exact ⟨W, hW, lisse_of_iso ((etaleSetPullback W.ι).mapIso e).symm hL⟩

end AlgebraicGeometry.Scheme
