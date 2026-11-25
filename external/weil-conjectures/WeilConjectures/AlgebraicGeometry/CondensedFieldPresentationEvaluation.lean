/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
public import Mathlib.Algebra.Category.ModuleCat.Basic

import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars

/-!
# Compatible evaluation functors for two lifts of a scheme point

Source: the geometric evaluation step of the rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Compatible geometric evaluation, independent of any chosen module or presentation.
Source: the geometric evaluation step of the rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11
(auxiliary; not a blueprint node).

Proof: use the supplied maps from the common algebraically closed field. First
extend scalars along the canonical coefficient isomorphism for p or g, then apply
module inverse image along a or d. Both routes end in modules over the condensed
coefficient ring on Spec(Omega). Evaluate their underlying sheaves and actions at
the final object. The continuous realization identifies that ring with ULift E,
since the spectrum of a field has one point. Define the E-action on each evaluated
module by applying its internal action to ULift(e) tensor m. The tensor universal
property and internal unit and associativity equations give an ordinary E-module;
the internal linearity diagram makes every evaluated morphism E-linear.

A pro-etale cover of an algebraically closed field splits through a member, so
abelian evaluation preserves cokernels. Finite colimits of internal modules are
computed on their underlying abelian sheaves, as tensoring preserves these
colimits. The ordinary module forgetful functor reflects these colimits, proving
finite-colimit preservation of evaluation. Inverse image and change of scalars
preserve finite colimits too. Each construction is additive. The module inverse
image composition comparisons, coefficient comparisons and the equality had give
the displayed natural isomorphism on all modules over X.

The regular coefficient module evaluates to E, giving b and c by evaluation at 1.
An endomorphism of the regular module is multiplication by its value on 1. The
adjoint-test characterization of the canonical continuous realization identifies
its image under geometric pullback with the value of its continuous coefficient
at a(z) or d(z). This proves both scalar formulas. The maps from the field exclude
empty source schemes V and W. No finite presentation or finite rank is required. -/
theorem exists_condensedField_compatible_evaluations
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X V W : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (p : V ⟶ X) (g : W ⟶ X)
    (a : Spec (.of Ω) ⟶ V) (d : Spec (.of Ω) ⟶ W)
    (had : a ≫ p = d ≫ g) (z : Spec (.of Ω)) :
    let R := condensedRingObj (condensedFieldCoefficientRingObj E) X
    let Ri := (upperStar AddCommGrpCat.{u + 1} p).obj R
    let Rj := (upperStar AddCommGrpCat.{u + 1} g).obj R
    ∃ (F : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) Ri ⥤
        ModuleCat.{u + 1} E)
      (G : Mod (Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}) Rj ⥤
        ModuleCat.{u + 1} E),
      F.Additive ∧ G.Additive ∧ PreservesFiniteColimits F ∧ PreservesFiniteColimits G ∧
      Nonempty (((upperStar AddCommGrpCat.{u + 1} p).mapMod R) ⋙ F ≅
        ((upperStar AddCommGrpCat.{u + 1} g).mapMod R) ⋙ G) ∧
      ∃ (b : F.obj (Mod.regular Ri) ≃ₗ[E] E)
        (c : G.obj (Mod.regular Rj) ≃ₗ[E] E),
        (∀ f : Mod.regular Ri ⟶ Mod.regular Ri,
          b (F.map f (b.symm 1)) =
            condensedFieldContinuousCoefficientMap E V
              (inv (condensedFieldPullbackRealization E p) ≫ f.hom ≫
                condensedFieldPullbackRealization E p) (a z)) ∧
        (∀ f : Mod.regular Rj ⟶ Mod.regular Rj,
          c (G.map f (c.symm 1)) =
            condensedFieldContinuousCoefficientMap E W
              (inv (condensedFieldPullbackRealization E g) ≫ f.hom ≫
                condensedFieldPullbackRealization E g) (d z)) := by
  let Λ := condensedFieldCoefficientRingObj E
  let R := condensedRingObj Λ X
  obtain ⟨H, hHa, hHc, hHs⟩ := exists_condensedField_point_evaluation E Ω z
  let := hHa
  let := hHc
  let P := condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) p a
  let Q := condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) g d
  let F := P ⋙ H
  let G := Q ⋙ H
  let e : (upperStar AddCommGrpCat.{u + 1} p).mapMod R ⋙ F ≅
      (upperStar AddCommGrpCat.{u + 1} g).mapMod R ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (condensedFieldGeometricModulePullbackComp Λ p a) H ≪≫
      Functor.isoWhiskerRight (eqToIso (congrArg (CondensedRing.upperStar Λ) had)) H ≪≫
      (Functor.isoWhiskerRight (condensedFieldGeometricModulePullbackComp Λ g d) H).symm ≪≫
      Functor.associator _ _ _
  obtain ⟨b, hb⟩ := condensedField_geometric_evaluation_scalars E X V Ω p a z H hHs
  obtain ⟨c, hc⟩ := condensedField_geometric_evaluation_scalars E X W Ω g d z H hHs
  refine ⟨F, G, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨e⟩, b, c, ?_, ?_⟩
  · exact hb
  · exact hc

end AlgebraicGeometry.ProEtale
