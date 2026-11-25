/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.StalkTensorComplex
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian

/-! # Derived tensor preserves vanishing of cohomology at a stalk

Source: Stacks Project, Cohomology, Tag 06YB; Tag 08EH, support conclusion
(blueprint: lem-sc-derived-tensor-stalk-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- Tensoring a representative with a K-flat complex preserves vanishing
of all cohomology at an individual stalk. No affine, perfect, or closed-support
hypothesis is needed.
Source: Stacks Project, Cohomology, Tag 06YB; Tag 08EH, support conclusion
(blueprint: lem-sc-derived-tensor-stalk-vanishing).

Proof:
1. Exactness of the module stalk functor identifies the homology of the stalk
   complex of P with the stalks of the cohomology sheaves of Q(P). Transport
   along eA: by the hypothesis these modules are zero, so P_x is acyclic.
2. By the stalk criterion for K-flatness, J_x tensors every acyclic complex to
   an acyclic complex. Thus Tot(P_x tensor J_x) is acyclic.
3. The natural stalk-total-tensor comparison identifies this complex with the
   stalk of Tot(P tensor J). Exactness of the stalk functor again identifies
   its zero homology with the stalks of the cohomology of Q(Tot(P tensor J)).
   Their underlying groups are therefore subsingletons. -/
theorem derived_tensor_stalk_vanishing
    (X : Scheme.{uX})
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (A : schemeDerivedCategory X)
    (P J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (eA : DerivedCategory.Q.obj P ≅ A)
    (hJ : CochainComplex.IsKFlatTensor (R := X.sheaf) J) (x : X)
    (hx : ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj A).val.presheaf x))) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    ∀ n : ℤ, Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj
        (DerivedCategory.Q.obj
          (CochainComplex.mapBifunctor P J (curriedTensor _)))).val.presheaf x)) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let F := forget₂ (ModuleCat.{uX} (X.presheaf.stalk x)) AddCommGrpCat.{uX}
  have hbL : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x) := inferInstance
  have hbC : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x) := inferInstance
  have : PreservesFiniteLimits T := by
    have : PreservesFiniteLimits (T ⋙ F) := by
      change PreservesFiniteLimits
        (SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
          (TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x))
      exact comp_preservesFiniteLimits (SheafOfModules.toSheaf (moduleRings X.toRingedSpace))
        (TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x)
    exact preservesFiniteLimits_of_reflects_of_preserves T F
  have : PreservesFiniteColimits (SheafOfModules.toSheaf
      (moduleRings X.toRingedSpace)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful (moduleRings X.toRingedSpace)).2.2.1
  have : PreservesFiniteColimits T := by
    have : PreservesFiniteColimits (T ⋙ F) := by
      change PreservesFiniteColimits
        (SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
          (TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x))
      exact comp_preservesFiniteColimits (SheafOfModules.toSheaf (moduleRings X.toRingedSpace))
        (TopCat.Sheaf.forget AddCommGrpCat.{uX} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{uX} x)
    exact preservesFiniteColimits_of_reflects_of_preserves T F
  let S := T.mapHomologicalComplex (.up ℤ)
  have hP : (S.obj P).Acyclic := by
    intro n
    have hz : IsZero (T.obj ((DerivedCategory.homologyFunctor _ n).obj A)) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hx n)
    let e := T.mapIso
      ((DerivedCategory.homologyFunctor _ n).mapIso eA.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app P)
    have hz' : IsZero (T.obj (P.homology n)) := hz.of_iso e.symm
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hz'.of_iso ((P.sc n).mapHomologyIso T))
  have ht := (RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace J).mp hJ x
    (S.obj P) hP
  obtain ⟨e, _⟩ := CochainComplex.exists_stalk_tensor_complex_iso X.toRingedSpace x
  have htotal : (S.obj (CochainComplex.mapBifunctor P J (curriedTensor _))).Acyclic :=
    fun n ↦ (ht n).of_iso (e P J).symm
  intro n
  let K := CochainComplex.mapBifunctor P J (curriedTensor _)
  have hz : IsZero (T.obj (K.homology n)) :=
    (htotal n).isZero_homology.of_iso ((K.sc n).mapHomologyIso T).symm
  have hz' : IsZero (T.obj ((DerivedCategory.homologyFunctor _ n).obj
      (DerivedCategory.Q.obj K))) :=
    hz.of_iso (T.mapIso ((DerivedCategory.homologyFunctorFactors _ n).app K))
  exact ModuleCat.isZero_iff_subsingleton.mp hz'

end AlgebraicGeometry.Scheme
