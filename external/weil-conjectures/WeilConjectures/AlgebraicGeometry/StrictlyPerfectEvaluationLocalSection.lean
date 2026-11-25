/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectLocalHomComputations
import WeilConjectures.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential

/-! # A local section of canonical derived evaluation

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ,
proof of lemma-dual-perfect-complex; Tags 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-local-section).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem section_of_comparison_square {C : Type*} [Category* C]
    {A B A' B' : C} (g : A ⟶ B) (f : A' ⟶ B') [IsIso f]
    (a : A ≅ A') (b : B ≅ B') (h : g ≫ b.hom = a.hom ≫ f) :
    ∃ s : B ⟶ A, s ≫ g = 𝟙 B := by
  refine ⟨b.hom ≫ inv f ≫ a.inv, ?_⟩
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, Category.id_comp]
  rw [h]
  simp

set_option synthInstance.maxSize 2048 in
-- The localized carriers and canonical tensor-Hom expression need extra elaboration steps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A local section of canonical derived evaluation.
Only one inverse identity is asserted. No representative of N and no
comparison square with a prescribed ordinary chain map is part of the statement.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ,
proof of lemma-dual-perfect-complex; Tags 08DM and 08DL.
(blueprint: lem-pc-strictly-perfect-evaluation-local-section).

Proof:
1. Represent RN by the localization preimage F and its canonical isomorphism.
   strictlyPerfect_localHom_computations gives preservation of quasi-isomorphisms
   by Hom(P,-) and K-flatness of Hom(P,O[0]).
2. Construct the ordinary evaluation chain map from localEvaluationDegreeMap
   and its differential identity. The component formula gives its evaluation
   predicate. exists_exactSource_evaluation_local_comparisons gives the two
   model isomorphisms a,b and the square R(g);b = a;Q(f).
3. Strictly perfect ordinary evaluation makes every component of f invertible,
   hence f and Q(f) are isomorphisms.
4. Set s = b.hom;inv(Q(f));a.inv. Postcompose the desired identity with b.hom,
   use the square, and cancel the two inverse pairs.
Rank zero, zero complexes and empty opens give the same identities on zero
objects; F may be unbounded because the finite support is that of P.
-/
theorem exists_strictlyPerfect_evaluation_local_section (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ s : R.obj (H.obj (op K, N)) ⟶ R.obj (N ⊗ D),
      s ≫ R.map g = 𝟙 (R.obj (H.obj (op K, N))) := by
  classical
  let : Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    inferInstance
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
  let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
    ((α_ N D K).hom ≫ N ◁
      ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
        (ρ_ N).hom)
  let Q := DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
  let F := Q.objPreimage (R.obj N)
  let eN : R.obj N ≅ Q.obj F := (Q.objObjPreimageIso (R.obj N)).symm
  have hlocal := strictlyPerfect_localHom_computations X U P hstrict
  let f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F :=
    { f := localEvaluationDegreeMap X U P F
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P F n m h }
  have hf : IsLocalOrdinaryEvaluation X U P F f := by
    intro p q n r hpq
    exact localEvaluationDegreeMap_formula X U P F p q n r hpq
  obtain ⟨a, b, hab⟩ := exists_exactSource_evaluation_local_comparisons
    X K N U P F hlocal.1 hlocal.2 eK eN f hf
  have : ∀ n : ℤ, IsIso (f.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  have : IsIso (Q.map f) := inferInstance
  exact section_of_comparison_square (R.map g) (Q.map f) a b hab

end AlgebraicGeometry
