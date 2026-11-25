/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechComplexAugmentations
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.Functor

/-! # Resolution columns of the Cech map induced by lambda

Source: Stacks Project, Tags 01FD and 01EX; Derived Categories, Tag 015E.
(blueprint: lem-sc-cech-pushforward-lambda-columns)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- Cech of a quasi-isomorphism from pushed-forward injectives to injectives is
columnwise a quasi-isomorphism in the resolution direction.
Source: Stacks 01FD, the arrow B-double-prime to B-prime; 01EX and Derived Categories 015E.
(blueprint: lem-sc-cech-pushforward-lambda-columns)

Proof: For each source tuple intersection V, pushforwards of injectives are acyclic
for sections on V by 01EX. The target injectives are section-acyclic as well. Apply
Leray acyclicity 015E to the given bounded-below quasi-isomorphism, restricted to V.
It follows that evaluation of lambda on V is a quasi-isomorphism. In each fixed
Cech degree q the resolution column is the product over all (q+1)-tuples of those
section complexes. Products of module groups are exact, so their homology is the
product of the homology groups. Thus the product map is a quasi-isomorphism. The
finite-product open chosen by the Cech functor is canonically the intersection V,
so its scalar restriction does not change this conclusion. Empty tuple sets give
zero complexes, and empty intersections and zero terms cause no exception. No
covering, quasi-coherence, or invertibility of an alpha map is used.
-/
theorem cech_pushforward_lambda_columns {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι : Type v} (U : ι → X.Opens) (A : CochainComplex X'.Modules ℕ)
    (K : CochainComplex X.Modules ℕ)
    (hA : ∀ n : ℕ, Injective (A.X n)) (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ⟶ K)
    (hl : QuasiIso l) (q : ℕ) :
    QuasiIso (((HomologicalComplex₂.flipFunctor (ModuleCat.{v} Γ(X, ⊤))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
        ((moduleCechDoubleFunctor U).map l)).f q) := by
  classical
  have : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : QuasiIso l := hl
  let J := Fin (q + 1) → ι
  let V (y : J) : X.Opens := ∏ᶜ fun i => U (y i)
  let S (y : J) := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op (V y))
  let R (y : J) := ModuleCat.restrictScalars
    (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op (V y)))).hom
  have hs (y : J) : QuasiIso (((S y).mapHomologicalComplex (ComplexShape.up ℕ)).map l) := by
    have : PreservesFiniteLimits (S y) := by
      change PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op (V y)))
      infer_instance
    apply (S y).quasiIso_map_of_rightAcyclic_nat l
    · intro n
      have : Injective (A.X n) := hA n
      exact (module_pushforward_injective_acyclic f (A.X n)).2 (V y)
    · intro n
      have : Injective (K.X n) := hK n
      exact Functor.rightAcyclic_of_injective (F := S y) (K.X n)
  let T : X.Modules ⥤ Discrete J ⥤ ModuleCat.{v} Γ(X, ⊤) :=
    { obj := fun M => Discrete.functor fun y => (S y ⋙ R y).obj M
      map := fun a => Discrete.natTrans fun y => (S y.as ⋙ R y.as).map a }
  have : T.Additive := by
    constructor
    intro M N a b
    apply NatTrans.ext
    funext y
    exact (S y.as ⋙ R y.as).map_add
  -- A map of discrete diagrams is a quasi-isomorphism if each evaluation is one.
  have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map l) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro y
    have := hs y.as
    change QuasiIso (((R y.as).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((S y.as).mapHomologicalComplex (ComplexShape.up ℕ)).map l))
    infer_instance
  -- ModuleCat satisfies AB4*: arbitrary products preserve homology.
  let L := lim (J := Discrete J) (C := ModuleCat.{v} Γ(X, ⊤))
  have hh : QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map l)) := by
    infer_instance
  -- These termwise products are definitionally the fixed Cech column.
  exact hh

end AlgebraicGeometry.Scheme.Modules
