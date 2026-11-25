/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons

/-! # The local ordinary model of canonical derived evaluation

Source: Stacks Project, Cohomology of Sheaves, Tags 08DL, 08DM and 08DQ.
(blueprint: lem-pc-strictly-perfect-evaluation-model).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Conversion between the localized carrier and the Hom carrier needs extra elaboration steps.
/-- The restricted canonical adjunct is the localization of ordinary evaluation,
with the source and target comparison isomorphisms included in the commuting square.
This assertion does not say that the evaluation chain map is invertible.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of Lemma 20.50.5;
Tag 08DM, Lemma 20.46.9; Tag 08DL, Lemma 20.42.3.
(blueprint: lem-pc-strictly-perfect-evaluation-model).

Proof:
1. Represent N restricted to U by a complex F. Exact restriction commutes with
   the tensor and Hom-complex constructions. The restriction comparison for
   RHom and the given isomorphism K|U ≅ QP identify the first Hom input with P.
2. The Hom complex from P computes RHom(P,F) and RHom(P,O[0]). This holds on
   arbitrary U: each term of P is a retract of a finite free module, so its
   internal Hom preserves exact sequences. The finite stupid filtration of P
   shows that Hom(P,-) preserves quasi-isomorphisms. Equivalently, check on
   affine subopens and then on cohomology sheaves, as in Tag 08DM.
3. The dual Hom(P,O[0]) is bounded, and its terms are retracts of finite free
   modules, obtained by dualizing the retractions for P. Thus its terms are flat
   and it is K-flat. Its total tensor with F computes the derived tensor without
   requiring F to be bounded or K-flat. These computations give a and b.
4. Define f by its tensor-summand components: for r+q=0, curry the map that
   evaluates the degree-q dual on P^r, then acts on F^p by the unit; for
   r+q≠0 set the component to zero. The Hom-product and tensor-coproduct universal
   properties give the degree maps. The Hom differential and total tensor
   differential have matching signs, so these maps form a chain map.
5. Apply the representative equation of the canonical tensor-Hom family to
   the evaluation map into a K-injective resolution. On each summand its
   uncurrying is the same evaluation in step 4. Naturality transports this
   equation along K|U ≅ QP and the chosen representative of N|U. The comparison
   maps to the resolutions commute with evaluation, hence the displayed square
   commutes after localization. Empty U and zero P use the same zero maps.
-/
theorem strictlyPerfect_evaluation_local_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      Nonempty (R.obj N ≅ DerivedCategory.Q.obj F) ∧
      ∃ f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F,
        IsLocalOrdinaryEvaluation X U P F f ∧
        ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
          ∃ b : R.obj (H.obj (op K, N)) ≅
              DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
            R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  classical
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let Q := DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
  let F := Q.objPreimage (R.obj N)
  let eN : R.obj N ≅ Q.obj F := (Q.objObjPreimageIso (R.obj N)).symm
  let f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F :=
    { f := localEvaluationDegreeMap X U P F
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P F n m h }
  have hf : IsLocalOrdinaryEvaluation X U P F f := by
    intro p q n r h
    exact localEvaluationDegreeMap_formula X U P F p q n r h
  obtain ⟨eK⟩ := hP
  obtain ⟨a, b, hab⟩ := exists_strictlyPerfect_evaluation_comparisons
    X K N U P F hstrict eK eN f hf
  exact ⟨F, ⟨eN⟩, f, hf, a, b, hab⟩

end AlgebraicGeometry
