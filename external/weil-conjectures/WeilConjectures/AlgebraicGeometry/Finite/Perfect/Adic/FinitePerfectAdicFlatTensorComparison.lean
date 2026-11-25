/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicFreeTensorCone
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientDiagram
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicOrdinaryTensorTransition
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Derived comparison for the explicit bounded flat tensor model

Source: Stacks Project, Tag 09C6, the quotient-complex calculation;
Modules on Sites, Tags 093J--093M; More on Algebra, Tag 09AW.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local irreducible] completedAdicChangeData completedAdicScalar

local instance finitePerfectAdicFlatTensorCategory
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    Category.{t + 2} (DerivedCategory (CompletedAdicModules X d)) := inferInstance

private theorem completedExactComparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [PreservesFiniteLimits (completedAdicScalarExtension X d)]
    [PreservesFiniteColimits (completedAdicScalarExtension X d)] :
    Nonempty (completedAdicDerivedChange X (completedAdicScalar X d) ≅
      (completedAdicScalarExtension X d).mapDerivedCategory) := by
  let E := completedAdicScalarExtension X d
  let T := completedAdicDerivedChange X (completedAdicScalar X d)
  let h := (completedAdicScalarExtensionData X d).choose_spec.choose_spec.choose_spec
    |>.choose_spec.2.2
  obtain ⟨ε, hε, _⟩ := h.choose_spec
  have : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) := hε
  have : E.mapDerivedCategory.IsLeftDerivedFunctor E.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ E.mapDerivedCategoryFactorsh
  exact ⟨Functor.leftDerivedUnique E.mapDerivedCategory T ε E.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso _ (.up ℤ))⟩

/-- Ordinary tensor models of a bounded flat algebraic complex compute the completed
realization and its entire canonical derived quotient diagram.

Source: Stacks Project, Tag 09C6, the finite-projective quotient calculation;
Modules on Sites, Tags 093J--093M; More on Algebra, Tag 09AW.
(blueprint: lem-weil-pbc-finite-perfect-adic-flat-tensor-comparison).

Proof: ordinary completed scalar extension E is exact, and its quotient tensor
comparison gives a natural isomorphism H(M) tensor_(A_T) (A/I^(n+1))_T ≅
H(M tensor_A A/I^(n+1)), including all coefficient transitions, where H is exact
constant realization followed by E. Apply this natural isomorphism degreewise
to P, and transpose complexes of diagrams to diagrams of complexes. Exactness
of H lets localization commute with the resulting diagram.
A bounded-above complex of flat A-modules is K-flat. At each quotient, transpose
the localized ordinary insertion unit under the supplied adjunction. The K-flat
representative criterion makes this transpose invertible; exact restriction and
tensor symmetry give the algebraic level comparison. The consecutive transition
square for these explicit maps, and the constructor for natural transformations
of inverse sequences, assemble the whole algebraic quotient-diagram isomorphism.
Finally, because E is exact, its exact derived functor is a left derived functor.
Uniqueness of left derived functors identifies it with the selected completed
derived scalar extension. The exact derived composition isomorphism for H gives
both the diagram's final realization and the asserted cone-point isomorphism.
The proof uses only the upper bound, while keeping both bounds in the statement.
No finite-projective splitting or inverse-limit assertion enters. -/
theorem finitePerfectAdicFlatTensor_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ DerivedCategory.adicLevelRestriction d.ideal n)
    (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Flat A (P.X i)) :
    Nonempty (finitePerfectAdicTensorComplexDiagram X d P ⋙ DerivedCategory.Q ≅
      finitePerfectAdicQuotientDiagram d.ideal L adj (DerivedCategory.Q.obj P) ⋙
        finitePerfectAdicDerivedConstant X A ⋙
          completedAdicDerivedChange X (completedAdicScalar X d)) ∧
    Nonempty (DerivedCategory.Q.obj (finitePerfectAdicOrdinaryComplex X d P) ≅
      (completedAdicDerivedChange X (completedAdicScalar X d)).obj
        ((finitePerfectAdicDerivedConstant X A).obj (DerivedCategory.Q.obj P))) := by
  have _ := ha
  have := (finitePerfectAdicOrdinaryCoefficient_comparison X d).1.1
  have := (finitePerfectAdicOrdinaryCoefficient_comparison X d).1.2
  let F := finitePerfectAdicConstant X A
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  let E := completedAdicScalarExtension X d
  let H := finitePerfectAdicOrdinary X d
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits F E
  have : PreservesFiniteColimits H := comp_preservesFiniteColimits F E
  let D := H.mapDerivedCategory
  obtain ⟨e⟩ := completedExactComparison X d
  let dc : D ≅ finitePerfectAdicDerivedConstant X A ⋙
      completedAdicDerivedChange X (completedAdicScalar X d) :=
    (Functor.mapDerivedCategoryCompIso F E).symm ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory e.symm
  obtain ⟨c⟩ := finitePerfectAdicTensorComplexDiagram_ordinaryComparison X d P
  have := hb
  have hk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P b
    (fun i ↦ (ModuleCat.flat_iff_flat _).2 (hP i))
  let hp : P.IsKFlatForTotalTensor :=
    ⟨fun s hs ↦ hk.1 s hs, fun s hs ↦ hk.2 s hs⟩
  obtain ⟨q⟩ := adicOrdinaryTensorComplexDiagram_comparison d.ideal L adj P hp
  exact ⟨⟨Functor.isoWhiskerRight c DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft (adicOrdinaryTensorComplexDiagram d.ideal P)
      H.mapDerivedCategoryFactors.symm ≪≫
    Functor.isoWhiskerRight q D ≪≫
    Functor.isoWhiskerLeft (finitePerfectAdicQuotientDiagram d.ideal L adj
      (DerivedCategory.Q.obj P)) dc⟩,
    ⟨(H.mapDerivedCategoryFactors.app P).symm ≪≫ dc.app (DerivedCategory.Q.obj P)⟩⟩

end AlgebraicGeometry.Scheme
