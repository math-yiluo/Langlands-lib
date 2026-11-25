/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Shared definitions for homology evaluation

Source: Stacks Project, Tags 0A8X, 08DH and 0BQY.
(blueprint: lem-sc-homology-evaluation-formal-complex). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Restriction to an open scheme followed by an over site preserves zero morphisms.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). 
(blueprint: new-b2-homology-evaluation-definitions)
-/
theorem moduleOpenOver_preservesZeroMorphisms (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    (Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext A x
  rfl

/-- Termwise restriction to an open scheme followed by an over site.
Source: Stacks Project, Tag 08DL, termwise restriction.
(blueprint: lem-sc-homology-evaluation-formal-complex). 
(blueprint: new-b2-homology-evaluation-definitions)
-/
noncomputable def moduleOpenOverComplexFunctor (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens) :
    CochainComplex X.Modules ℤ ⥤
      CochainComplex (SheafOfModules.{u} (V.toScheme.ringCatSheaf.over W)) ℤ :=
  letI := moduleOpenOver_preservesZeroMorphisms X V W
  (Scheme.Modules.restrictFunctor V.ι ⋙
    SheafOfModules.overFunctor V.toScheme.ringCatSheaf W).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- A complex admits a finite free, zero-differential model by a quasi-isomorphism roof.
Source: Stacks Project, Tag 0BQY, zero-differential Koszul calculation.
(blueprint: lem-sc-homology-evaluation-formal-complex). 
(blueprint: new-b2-homology-evaluation-definitions)
-/
def HasFiniteFreeZeroModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (T : CochainComplex (SheafOfModules.{u} R) ℤ) : Prop :=
  ∃ (E L : CochainComplex (SheafOfModules.{u} R) ℤ)
    (q : L ⟶ T) (p : L ⟶ E),
    QuasiIso q ∧ QuasiIso p ∧
      (∀ a b : ℤ, E.d a b = 0) ∧
      (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k)) ∧
      (∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
        SheafOfModules.free (R := R) (ULift.{u} (Fin r))))

/-- The degree component used to evaluate a Hom cocycle on a cycle.
Source: Stacks Project, Tag 0A8X, product definition of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). 
(blueprint: new-b2-homology-evaluation-definitions)
-/
noncomputable def homologyEvaluationProjection (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    (homComplex (R := X.sheaf) T J).X n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 0) :=
  (Classical.choose (homComplex_projections_exists.{u, u, u, u}
    (R := X.sheaf))) T J n (-n) 0 (by omega)

/-- Characterization of evaluation on classes by its action on local cycle representatives.
Source: Stacks Project, Tags 0A8X and 08DH, evaluation of the Hom complex.
(blueprint: lem-sc-homology-evaluation-formal-complex). 
(blueprint: new-b2-homology-evaluation-definitions)
-/
def IsHomologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0)) : Prop :=
  let P := homComplex (R := X.sheaf) T J
  ∀ (U : X.Opens)
    (φ : (P.cycles n).val.obj (op U))
    (z : (T.cycles (-n)).val.obj (op U)) (b : (J.cycles 0).val.obj (op U)),
    (J.iCycles 0).val.app (op U) b =
      ((homologyEvaluationProjection X T J n).val.app (op U)
        ((P.iCycles n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) →
    (e.val.app (op U)
      ((P.homologyπ n).val.app (op U) φ)).app
        (op (Over.mk (𝟙 U))) ((T.homologyπ (-n)).val.app (op U) z) =
      (J.homologyπ 0).val.app (op U) b

end CategoryTheory
