/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CompletedTowerIndependent.IntegralCompletedTowerPullbackUniverses
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement

/-! # Canonical generators and normalization for pulled principal Koszul towers

Source: Stacks Project, sites-modules.tex, Tags 03D2, 03EK and 03EL;
sites-cohomology.tex, Tag 07A4; algebraization.tex, Tag 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization).

The index n denotes exponent n+1. These constructions require neither a good
complex nor invertibility of ell on the schemes. They depend only on the recorded
ordinary completed pullback, total tensor generators and principal Koszul tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent

namespace WeilConjectures.PulledKoszulTowerModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical total-tensor generator, in the existing direct-sum totalization.
Source: Stacks 03EK, 06YM
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def tensorGenerator (W : Scheme.{t}) (P Q : CochainComplex (Modules l E W) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k).val.obj U) :=
  coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq U x y

/-- The cone's degree-zero free generator, fixed by the standard cone inclusion.
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def koszulZero (W : Scheme.{t}) (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X 0 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).inv ≫
      (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (Modules l E W) 0).map
          (PrincipalKoszulStrictReplacement.multiplication l E W n))).f 0

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Ordinary G on cochain complexes, with no exactness assumption.
Source: Stacks 03D2
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def G : CochainComplex (Modules l E Y) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (pull l E g).mapHomologicalComplex (.up ℤ)

/-- The canonical generator of ordinary pullback, fixed by its adjunction unit.
Source: Stacks 03D2
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def generator (M : Modules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pull l E g).obj M).val.obj (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  ((adjunction l E g).unit.app M).val.app (op V) x

/-- The strict replacement H(P) with transitions id_P tensor (t,1).
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def H (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  PrincipalKoszulStrictReplacement.sourceTower l E W P

end WeilConjectures.PulledKoszulTowerModel
