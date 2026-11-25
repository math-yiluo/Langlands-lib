/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence

/-! # Pasting a Cartesian affine prefix with a base-change square

(blueprint: lem-pur-vector-integration-cartesian-prefix-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearCompactComparison
  affineLinearCoefficientDescent affineLinearBaseCoefficient
  leftDerivedUpperStarComp derivedSquareUpperStarIso upperStar Functor.leftDerivedFunctor

private lemma inverse_paste
    {C : Type*} [Category C] {P Q R S T : C}
    (a : P ≅ Q) (b : Q ≅ R) (c : R ≅ S) (d : S ≅ T) (e : P ≅ T)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom = e.hom) :
    d.inv ≫ c.inv ≫ b.inv = e.inv ≫ a.hom := by
  have hi : a ≪≫ b ≪≫ c ≪≫ d = e := Iso.ext h
  have hh := congrArg Iso.inv hi
  simp only [Iso.trans_inv, Category.assoc] at hh
  calc
    _ = (d.inv ≫ c.inv ≫ b.inv ≫ a.inv) ≫ a.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by rw [hh]

/-- A Cartesian affine prefix after base change is the prefix for the pasted square.
This concerns arbitrary Cartesian maps, without module frames or a trace counit.
Source: blueprint vector-bundle purity proof, paragraph 2, pasting of the bundle and
inverse-coordinate exchange squares.
(blueprint: lem-pur-vector-integration-cartesian-prefix-base-change).

Proof: naturality moves the coefficient comparison through the second exchange.
Compact-support exchange pasting identifies the two exchange factors with exchange
for the composite square and the inverse-image compositors. Inverse square pasting
and naturality identify the successive coefficient maps; composition of normalized
ordered Tate pullback identifies their base factors. Functoriality combines them
under compact support, yielding the Cartesian prefix for the composite square.
No property of a chosen frame or of a counit is used, including at rank zero.
-/
theorem vectorIntegrationCartesianPrefix_baseChange
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' S T W : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian S] [IsNoetherian T]
    [IsNoetherian W]
    (p : X ⟶ S) (p' : X' ⟶ T) (f : T ⟶ S) (v : X' ⟶ X)
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] [HasCompactification p]
    [IsSeparated p'] [LocallyOfFiniteType p'] [QuasiCompact p'] [HasCompactification p']
    (sq : IsPullback v p' p f) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (j : W ⟶ T) (hW : IsUnit (N : Γ(W, ⊤)))
    (q : affineTraceTower W d ⟶ X')
    (sqW : IsPullback q (affineTraceProjection W d) p' j)
    (m : W ⟶ S) (hm : m = j ≫ f)
    (z : affineTraceTower W d ⟶ X) (hz : z = q ≫ v)
    (sqZ : IsPullback z (affineTraceProjection W d) p m) :
    let L := affineLinearBaseCoefficient A N hA S d
    let L' := affineLinearBaseCoefficient A N hA T d
    let c := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app L ≪≫
      (ordinaryFinitePullback A p').mapIso
        (vectorIntegrationBaseCoefficientPullback A N hA t f hS d)
    (ordinaryFinitePullback A j).map
        ((rightDerivedLowerShriekBaseChangeMap A sq).app
          ((ordinaryFinitePullback A p).obj L) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p').map c.hom) ≫
      vectorIntegrationCartesianPrefix N hN A hA t p' j hW d q sqW L'
        (vectorIntegrationBaseCoefficientPullback A N hA t j
          (affineTracePullbackInvertible N f hS) d) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f m hm).inv.app _ ≫
      vectorIntegrationCartesianPrefix N hN A hA t p m hW d z sqZ L
        (vectorIntegrationBaseCoefficientPullback A N hA t m hS d) := by
  subst m z
  let := affineTraceNoetherian W d
  let L := affineLinearBaseCoefficient A N hA S d
  let L' := affineLinearBaseCoefficient A N hA T d
  let K := (ordinaryFinitePullback A p).obj L
  let c := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app L ≪≫
    (ordinaryFinitePullback A p').mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA t f hS d)
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection W d)
  have hp := affineLinearExchange_paste A sq sqW K
  have hn := (rightDerivedLowerShriekBaseChangeMap A sqW).naturality c.hom
  simp only [Functor.comp_map] at hn
  have hgeom := derivedSquareUpperStarIso_paste (ModuleCat.{u + 1} A)
    sq.toCommSq sqW.toCommSq sqZ.toCommSq rfl rfl L
  have hinv := inverse_paste
    ((ordinaryFinitePullback A (affineTraceProjection W d)).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j f).app L))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqW.toCommSq).app
      ((ordinaryFinitePullback A f).obj L))
    ((ordinaryFinitePullback A q).mapIso
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).app L))
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q v).symm.app
      ((ordinaryFinitePullback A p).obj L))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqZ.toCommSq).app L) hgeom
  have hnat := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqW.toCommSq).inv.naturality
    (vectorIntegrationBaseCoefficientPullback A N hA t f hS d).hom
  simp only [Functor.comp_map] at hnat
  have hb := orderedTateCoefficientComposition A N hA t j f (j ≫ f) rfl hS
    (affineTracePullbackInvertible N f hS) d
  have hc :
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q v).hom.app K ≫
        (ordinaryFinitePullback A q).map c.hom ≫
        (vectorIntegrationCartesianCoefficient A N hA t p' j hW d q sqW L'
          (vectorIntegrationBaseCoefficientPullback A N hA t j
            (affineTracePullbackInvertible N f hS) d)).hom =
      (vectorIntegrationCartesianCoefficient A N hA t p (j ≫ f) hW d (q ≫ v) sqZ L
        (vectorIntegrationBaseCoefficientPullback A N hA t (j ≫ f) hS d)).hom := by
    simp only [c, vectorIntegrationCartesianCoefficient, Iso.trans_hom,
      Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    simp only [Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv,
      Functor.mapIso_hom, Iso.app_hom] at hinv
    dsimp only [K, L, L', ordinaryFinitePullback] at hnat hinv hb ⊢
    rw [reassoc_of% hnat, reassoc_of% hinv]
    simp only [← Functor.map_comp_assoc]
    rw [hb]
  dsimp only
  unfold vectorIntegrationCartesianPrefix
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [c, K, L, L', R, ordinaryFinitePullback] at hn hp hc ⊢
  rw [reassoc_of% hn, reassoc_of% hp]
  simp only [← Functor.map_comp_assoc]
  rw [hc]

end AlgebraicGeometry.Etale
