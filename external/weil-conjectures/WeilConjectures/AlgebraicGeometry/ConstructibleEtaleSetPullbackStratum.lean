/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import all WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant
public import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Finite local constancy on pulled-back strata

Source: the fixed-stratum proof of `lem-weil-pbc-constructible-etale-set-pullback`,
using Stacks Project, Tags 095A, 03Q1 (3), and 03CB.
(blueprint: lem-stage3-finite-lc-pullback-stratum).
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The pullback of each stratum in a constructible set sheaf remains finite locally constant.
Source: the three-step proof of `lem-weil-pbc-constructible-etale-set-pullback`, with the
stratification fixed.  Pull back the trivializing covers and use the inverse-image
composition, restriction, constant-sheaf, stalk, and algebraic-structure comparisons.
Proof: Pull back finite trivializing covers along g. Composition, restriction, and constant-sheaf
comparisons preserve local constancy; stalk-germ bijections preserve finiteness; the
algebraic-structure comparison identifies the result with the underlying set sheaf.
(blueprint: lem-stage3-finite-lc-pullback-stratum). -/
theorem finiteLocallyConstant_pullback_stratum
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (S : Stratification X)
    (hS : ∀ i : Fin S.n, IsFiniteLocallyConstantSheafOfTypes
      ((etaleSetPullback (S.immersion i)).obj
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E))) :
    ∀ i : Fin S.n, IsFiniteLocallyConstantSheafOfTypes
      ((etaleSetPullback ((S.pullback g).immersion i)).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E))) := by
  intro i
  obtain ⟨_, ea, _⟩ := etaleInverseImageAlgebraicStructures (S.domain i) X (S.immersion i)
  have hi := finiteLocallyConstant_of_iso (ea.app E).symm (hS i)
  have hp := (pullback_finite_locally_constant
    (CategoryTheory.Limits.pullback.fst (S.immersion i) g) (S.immersion i) E hi).2
  let e := eqToIso (congrArg
      (fun m ↦ (Etale.upperStar AddCommGrpCat.{u + 1} m).obj E)
      (CategoryTheory.Limits.pullback.condition (f := S.immersion i) (g := g))) ≪≫
    (Etale.upperStarComp AddCommGrpCat.{u + 1}
      (CategoryTheory.Limits.pullback.snd (S.immersion i) g) g).app E
  have ht := finiteLocallyConstant_of_iso
    ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e) hp
  obtain ⟨_, eb, _⟩ := etaleInverseImageAlgebraicStructures
    ((S.pullback g).domain i) Y ((S.pullback g).immersion i)
  exact finiteLocallyConstant_of_iso
    (eb.app ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E)) ht
end AlgebraicGeometry.Scheme
