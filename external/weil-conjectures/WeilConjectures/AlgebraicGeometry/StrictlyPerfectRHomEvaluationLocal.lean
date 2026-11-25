/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationModel
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation

/-! # Strictly perfect local tensor--RHom evaluation

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ and 08DM.
(blueprint: lem-pc-strictly-perfect-rhom-evaluation-local).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical tensor--RHom evaluation is invertible on an open where its first
argument has a strictly perfect representative. There is no quasi-coherence or
boundedness assumption on the second argument.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of Lemma 20.50.5,
and Tag 08DM, Lemma 20.46.9.
(blueprint: lem-pc-strictly-perfect-rhom-evaluation-local).

Proof:
1. Restriction to U is exact, commutes with derived tensor, and commutes with
   derived internal Hom (Tag 08DL). Transport the first argument through hP.
   The representative equation defining schemeDerivedTensorHomEquiv identifies
   the restricted adjunct with the ordinary tensor--Hom evaluation comparison.
2. Write E for P. By Tag 08DM, RHom(E,O_U) is represented by the bounded complex
   E-dual with degree q term Hom(E^(-q),O_U). Each dual term is a direct summand
   of a finite free module, hence flat; the complex is bounded and K-flat.
   Its tensor with an arbitrary representative F of N|U therefore computes the
   derived tensor, even for unbounded F.
3. Again by Tag 08DM, RHom(E,F) is computed by the ordinary Hom complex. In
   degree n the comparison is the sum over p+q=n of
   F^p tensor Hom(E^(-q),O_U) to Hom(E^(-q),F^p). Only finitely many q occur.
   For a finite free module this map is the finite direct-sum identity. The map
   is natural in E, so passing to a retract proves the same for each E^(-q).
4. These degreewise isomorphisms form a chain map: evaluation commutes with the
   differentials, with the signs in the Hom and total-tensor differentials.
   Its localization is thus invertible. Step 1 identifies that localization
   with the displayed restricted canonical adjunct. Empty U and the zero
   complex give the same calculation with zero objects. -/
theorem strictlyPerfect_rhom_evaluation_isIso_on_open
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)) :
    let D := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op K, 𝟙_ (schemeDerivedCategory X))
    IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.map
        (((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
          ((α_ N D K).hom ≫ N ◁
            ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
              (ρ_ N).hom))) := by
  obtain ⟨F, _, f, hf, a, b, h⟩ :=
    strictlyPerfect_evaluation_local_model.{u, w} X K N U P hstrict hP
  have (n : ℤ) : IsIso (f.f n) :=
    isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  have hIso : IsIso (a.hom ≫ DerivedCategory.Q.map f) := inferInstance
  rw [← h] at hIso
  have := hIso
  exact IsIso.of_isIso_comp_right _ b.hom

end AlgebraicGeometry
