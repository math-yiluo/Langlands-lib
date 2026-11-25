/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAlgebraTower
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import all WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Finite reductions of completed constant perfect complexes

Source: Stacks Project, proetale.tex, Tag 09C6; Cohomology on Sites, Tag 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] CategoryTheory.ConstantCompletion.completed

/-- Reduction of a completed constant perfect complex is the constant algebraic reduction.
The algebraic extension is specified by its adjunction to actual restriction of scalars.
There is no completeness or Noetherian hypothesis on the coefficient ring or scheme.
Source: Stacks Project, Tags 06YY, 093J and 09C6.
(auxiliary; not a blueprint node).

Proof: A bounded complex of finite projective modules is K-flat. Exact constant
realization preserves its differential and its finite projective splittings, hence
produces a K-flat complex of flat sheaves. Scalar extension to the completed ring
and then to the quotient is computed termwise. Scalar balancing identifies this
with scalar extension directly to the constant quotient: the composite of the
coefficient map and completed projection is the actual quotient map, by the limit
cone equation. Constant module sheafification commutes with scalar extension;
before sheafification the comparison is (p tensor b) tensor c mapped to
p tensor bc, with inverse p tensor c mapped to (p tensor 1) tensor c. These maps
are natural in the modules, so give chain isomorphisms. Exact restriction to a
slice commutes with this tensor calculation. Finally any left adjoint L of actual
algebraic scalar restriction is uniquely isomorphic, compatibly with its unit, to
derived scalar extension. Apply this isomorphism to the bounded projective complex
and then exact constant realization and restriction. Compose the resulting
isomorphisms. This argument also covers the zero ring, zero complex and empty slice. -/
theorem adicResidue_perfect_reduction_comparison
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ)
    (L : DerivedCategory (ModuleCat.{max v (u + 1)} A) ⥤
      DerivedCategory (ModuleCat.{max v (u + 1)} (A ⧸ J ^ (n + 1))))
    (_adj : L ⊣ DerivedCategory.adicLevelRestriction J n)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ)
    (_hc : P.IsStrictlyGE c) (_hd : P.IsStrictlyLE d)
    (_hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) :
    Nonempty
      ((adicResidueLocalReduction.{u, v} X J U n).obj
        ((adicResidueRestriction
          (CategoryTheory.ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
              (adicResidueConstantPerfect X J P)) ≅
        (adicResidueFiniteConstant.{u, v} X J U n).obj
          (L.obj (DerivedCategory.Q.obj P))) := by
  classical
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := CategoryTheory.ConstantCompletion.completed T A J
  let k := CategoryTheory.ConstantCompletion.finite T A J n
  let q := Ideal.Quotient.mk (J ^ (n + 1))
  let φ := CategoryTheory.ConstantCompletion.coefficientMap T A J
  let π := CategoryTheory.ConstantCompletion.projection T A J n
  let Q₀ := CategoryTheory.ConstantCompletion.quotient T A J n
  let F := commutativeSiteConstantModuleFunctor T A
  let G := commutativeSiteConstantModuleFunctor T (A ⧸ J ^ (n + 1))
  let K := AdicPerfectModel.model T J P
  let R := AdicPerfectModel.overComplex B U
  let S := AdicPerfectModel.overComplex k U
  let Pq := ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P
  let Kq := ((G.mapHomologicalComplex (.up ℤ)).obj Pq)
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod B)
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod k)
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (B.over U))
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (k.over U))
  let : HasDerivedCategory.{max v (u + 1) + 1}
      (SheafOfModules.{max v (u + 1)} ((siteModuleRings B).over U)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{max v (u + 1) + 1}
      (SheafOfModules.{max v (u + 1)} ((siteModuleRings k).over U)) :=
    HasDerivedCategory.standard _
  let pres : (SheafOfModules.strictPerfectConstantSheaf T A ⋙
      SheafOfModules.restrictScalars (constantModuleHomRingIso T A).inv) ≅ F :=
    AdicPerfectModel.constantPresentationIso
  let ep : adicResidueConstantPerfect X J P ≅
      (CategoryTheory.ConstantCompletion.Q B).obj K :=
    (CategoryTheory.ConstantCompletion.Q B).mapIso
      ((NatIso.mapHomologicalComplex
        ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight pres
          (CategoryTheory.ConstantCompletion.change φ)) (.up ℤ)).app P)
  have hpflat (i : ℤ) : Module.Flat A (P.X i) := by
    have := (_hP i).2
    infer_instance
  have hbounded (i : ℤ) (hi : d < i) : IsZero (P.X i) :=
    (P.isStrictlyLE_iff d).1 _hd i hi
  have hk : CochainComplex.IsKFlatTensor (R := B) K :=
    AdicPerfectModel.model_kflat J P d hbounded (fun i ↦ (_hP i).2)
  have hks : CochainComplex.IsKFlatTensor (R := B.over U) (R.obj K) :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
      ((SheafOfModules.ringedSite_restriction_exact_kflat T B U).2.2 K
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mpr hk))
  have hcomp : φ ≫ π = Q₀ :=
    limit.lift_π (CategoryTheory.ConstantCompletion.quotientCone T A J) (Opposite.op n)
  let bal := AdicPerfectModel.scalarChangeCompTo φ π Q₀ hcomp
  let fc := ConstantScalarRealization.complexComparison T q P
  have : ∀ i, IsIso (fc.f i) := fun i ↦
    (ConstantScalarRealization.moduleComparison_tensor T q (P.X i)).1
  have : IsIso fc := HomologicalComplex.Hom.isIso_of_components fc
  let eq : ((CategoryTheory.ConstantCompletion.change Q₀).mapHomologicalComplex
      (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ≅ Kq :=
    (NatIso.mapHomologicalComplex
      (AdicPerfectModel.constantChangeIso (J := T) q) (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫ asIso fc
  let ek : ((CategoryTheory.ConstantCompletion.change π).mapHomologicalComplex
      (.up ℤ)).obj K ≅ Kq :=
    (Functor.mapHomologicalComplexCompIso bal (.up ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫ eq
  let es := AdicPerfectModel.changeOverComplexIso π U K ≪≫ S.mapIso ek
  let rB := SheafOfModules.overFunctor.{max v (u + 1)} (siteModuleRings B) U
  let rQ := SheafOfModules.overFunctor.{max v (u + 1)} (siteModuleRings k) U
  let er : (adicResidueRestriction B U).obj (adicResidueConstantPerfect X J P) ≅
      (CategoryTheory.ConstantCompletion.Q (B.over U)).obj (R.obj K) :=
    (adicResidueRestriction B U).mapIso ep ≪≫ rB.mapDerivedCategoryFactors.app K
  have hi : IsIso ((CategoryTheory.ConstantCompletion.extendComparison
      (adicResidueLocalProjection X J U n)).app (R.obj K)) :=
    (CategoryTheory.ConstantCompletion.derivedExtension
      (adicResidueLocalProjection X J U n)).computation (R.obj K) hks
  let el : (adicResidueLocalReduction X J U n).obj
      ((adicResidueRestriction B U).obj (adicResidueConstantPerfect X J P)) ≅
        (CategoryTheory.ConstantCompletion.Q (k.over U)).obj (S.obj Kq) :=
    (adicResidueLocalReduction X J U n).mapIso er ≪≫
      asIso ((CategoryTheory.ConstantCompletion.extendComparison
        (adicResidueLocalProjection X J U n)).app (R.obj K)) ≪≫
      (CategoryTheory.ConstantCompletion.Q (k.over U)).mapIso es
  let := _hd
  have hpk : P.IsKFlatForTotalTensor :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P d
      (fun i ↦ (ModuleCat.flat_iff_flat _).2 (hpflat i))
  have hm : IsIso (ConstantScalarRealization.moduleRepresentative.{max v (u + 1),
      max v (u + 1), max v (u + 1)} q P) :=
    ConstantScalarRealization.moduleRepresentative_isIso q P hpk
  let ea : L.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj Pq :=
    (Adjunction.leftAdjointUniq _adj
      (ConstantScalarRealization.moduleDerivedAdjunction q)).app
        (DerivedCategory.Q.obj P) ≪≫
      asIso (ConstantScalarRealization.moduleRepresentative.{max v (u + 1),
      max v (u + 1), max v (u + 1)} q P)
  let ec : (adicResidueFiniteConstant X J U n).obj
      (L.obj (DerivedCategory.Q.obj P)) ≅
        (CategoryTheory.ConstantCompletion.Q (k.over U)).obj (S.obj Kq) :=
    rQ.mapDerivedCategory.mapIso
      (G.mapDerivedCategory.mapIso ea ≪≫ G.mapDerivedCategoryFactors.app Pq) ≪≫
      rQ.mapDerivedCategoryFactors.app Kq
  exact ⟨el ≪≫ ec.symm⟩

end AlgebraicGeometry.Scheme
