/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedPullbackExact
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.AlgebraicGeometry.CoefficientRestrictedTensorComparison
import all WeilConjectures.AlgebraicGeometry.NilpotentReductionStep
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Flat models for a restricted tensor with constant coefficients

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.ConstantCompletion CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- A bounded-above restricted complex has a bounded-above K-flat model whose ordinary
constant tensor computes the restricted derived tensor. This comparison has no finite
module, Noetherian ring, or local constancy hypotheses.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4,
lemma-pullback-tensor-product, and Tag 06YU, definition-derived-tor.
(auxiliary; not a blueprint node).

Proof: use the target constant-scalar equivalence to regard exact inverse image of K as
an intrinsic derived object L. The exact functors commute with homology; hence the bound
on K is a bound on L. Choose a bounded-above flat-term K-flat representative P of L using
the existing bounded flat representative theorem. Its derived scalar image represents
inverse image of K by the equivalence counit and the representative factorization. Apply
the derived restricted tensor comparison to K and M. Transport its first target tensor
factor from L to Q(P). The K-flat single-tensor comparison identifies this tensor with Q
of termwise tensorRight by the constant realization of M. The braiding identifies that
complex with termwise tensorLeft. Finally use the exact functor's representative
factorization to obtain the stated comparison in the fixed-scalar derived category.
No finiteness or flatness of M is needed; the zero ring and empty schemes are allowed. -/
theorem coefficient_restricted_tensor_flat_model
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A]
    (K : adicFiniteAmbient.{u, v} X A)
    (hK : ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((coefficientModelCohomology _ j).obj K)) :
    let R := constant (coefficientProEtaleModelTopology.{u, v} Y) A
    let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
    let E := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} Y) A
    let F := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} X) A ⋙
      coefficientProEtaleFixedModulePullback.{u, v} f A
    letI := HasDerivedCategory.standard (Mod S)
    letI := HasDerivedCategory.standard
      (Sheaf (coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat.{max v (u + 1)} A))
    letI := SheafOfModules.monoidalCategory R
    ∃ P : CochainComplex (Mod R) ℤ,
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.X j)) ∧
      P.IsKFlatTensor ∧
      Nonempty (F.mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
      ∀ M : ModuleCat.{max v (u + 1)} A,
        Nonempty (F.mapDerivedCategory.obj
            (((SheafOfModules.KFlatFixedTensor.derivedTensor S).obj K).obj
              ((Q S).obj ((HomologicalComplex.single (Mod S) (.up ℤ) 0).obj
                ((commutativeSiteConstantModuleFunctor
                  (coefficientProEtaleModelTopology.{u, v} X) A).obj M)))) ≅
          DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj
            (((tensorLeft ((commutativeSiteConstantModuleFunctor
              (coefficientProEtaleModelTopology.{u, v} Y) A).obj M)).mapHomologicalComplex
                (.up ℤ)).obj P))) := by
  dsimp only
  classical
  let R := constant (coefficientProEtaleModelTopology.{u, v} Y) A
  let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
  let E := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} Y) A
  let F := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    coefficientProEtaleFixedModulePullback.{u, v} f A
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard
    (Sheaf (coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat A))
  let := SheafOfModules.monoidalCategory R
  let G := E.mapDerivedCategory
  let L := G.inv.obj (F.mapDerivedCategory.obj K)
  let e : G.obj L ≅ F.mapDerivedCategory.obj K :=
    G.asEquivalence.counitIso.app _
  have hL : ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (Mod R) j).obj L) := by
    obtain ⟨b, hb⟩ := hK
    refine ⟨b, ?_⟩
    intro j hj
    let i := (E.mapDerivedCategoryHomologyFunctorIso j).app L ≪≫
      (DerivedCategory.homologyFunctor _ j).mapIso e ≪≫
      ((F.mapDerivedCategoryHomologyFunctorIso j).app K).symm
    have hz := (Functor.map_isZero F (hb j hj)).of_iso i
    exact IsZero.of_full_of_faithful_of_isZero E _ hz
  obtain ⟨P, ⟨eP⟩, hb, hf, hP⟩ := SheafOfModules.bounded_flat_representative
    (coefficientProEtaleModelTopology.{u, v} Y) A L hL
  refine ⟨P, hb, hP, ⟨e.symm ≪≫ G.mapIso eP.symm ≪≫
    E.mapDerivedCategoryFactors.app P⟩, ?_⟩
  intro M
  let N := (commutativeSiteConstantModuleFunctor
    (coefficientProEtaleModelTopology.{u, v} Y) A).obj M
  let sing := (Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj N)
  let dt := SheafOfModules.KFlatFixedTensor.derivedTensor R
  let c := (SheafOfModules.ringed_kFlat_single_tensor_comparison R).choose P hP N
  let swap : ((SheafOfModules.KFlatFixedTensor.ordinaryTensor R).flip.obj N) ≅
      tensorLeft N := BraidedCategory.tensorLeftIsoTensorRight N |>.symm
  exact ⟨(coefficient_restricted_tensor_comparison f A K M).some ≪≫
    G.mapIso (((Functor.flip dt).obj sing).mapIso eP.symm) ≪≫
    G.mapIso c ≪≫ G.mapIso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex swap (.up ℤ)).app P)) ≪≫
    E.mapDerivedCategoryFactors.app _⟩

end AlgebraicGeometry.Scheme
