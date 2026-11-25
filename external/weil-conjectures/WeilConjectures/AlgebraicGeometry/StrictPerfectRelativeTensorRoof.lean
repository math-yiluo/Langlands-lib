/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.RelativeTensorRoofComparison
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # A relative tensor representative roof

Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: lem-pc-strict-perfect-relative-tensor-roof).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.module_overFunctor_preservesZero
  Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem common_quasiIso_roof
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K T : CochainComplex C ℤ} (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj T) :
    ∃ (H : CochainComplex C ℤ) (s : H ⟶ K) (t : H ⟶ T), QuasiIso s ∧ QuasiIso t := by
  obtain ⟨H, s, hs, t, ht⟩ := DerivedCategory.right_fac e.hom
  let := hs
  have heq : DerivedCategory.Q.map t = DerivedCategory.Q.map s ≫ e.hom := by
    rw [ht, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htIso : IsIso (DerivedCategory.Q.map t) := by
    rw [heq]
    infer_instance
  exact ⟨H, s, t, (DerivedCategory.isIso_Q_map_iff_quasiIso C s).1 hs,
    (DerivedCategory.isIso_Q_map_iff_quasiIso C t).1 htIso⟩

namespace AlgebraicGeometry.Scheme

/-- The explicit local tensor and scalar-restricted K have a common quasi-isomorphic
complex. This is only the representative-comparison step; no relative flatness or
prescribed interval is assumed or asserted. Source: Stacks Project, Tags 0DJQ,
06YH and 05RT, local tensor computation and the calculus of fractions.

Proof: each term of L is a finite-free retract, hence flat over O_X on the open
site. Its boundedness implies K-flatness. Exact monoidal open restriction carries
eK to an isomorphism with the restricted derived tensor; eL identifies its first
factor with QL. The K-flat tensor comparison identifies that derived tensor with
Q of the ordinary total tensor of L and G restricted to U. Restriction of scalars
is exact and therefore descends to localization at quasi-isomorphisms. It carries
this comparison to the two base-ring complexes on U, commuting with open
restriction sectionwise. In the homotopy category, right fractions represent the
resulting derived isomorphism by a roof with a quasi-isomorphic left leg. The right
leg becomes an isomorphism after localization, hence is a quasi-isomorphism as
well (homology reflects this). Choose actual chain maps representing both
homotopy classes. Their homology maps are unchanged, so both are quasi-isomorphisms.
Only an existential proposition uses this roof, not a definition of data.
On the empty open all complexes have zero terms and the same comparison applies.
(blueprint: lem-pc-strict-perfect-relative-tensor-roof). -/
theorem strictPerfect_relativeTensor_roof
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    ∃ (H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ)
      (s : H ⟶ ((SheafOfModules.overFunctor.{u} A U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
      (t : H ⟶ strictPerfectRelativeTensorComplex f U L G),
      QuasiIso s ∧ QuasiIso t := by
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let C := SheafOfModules.{u} (A.over U)
  let : HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
  obtain ⟨e⟩ := strictPerfect_relativeTensor_roof_comparison f E G K eK U L hL eL
  exact common_quasiIso_roof (C := C) e

end AlgebraicGeometry.Scheme
