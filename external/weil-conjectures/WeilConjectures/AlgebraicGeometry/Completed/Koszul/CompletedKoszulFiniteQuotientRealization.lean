/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentation
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientExactness

/-! # Exact finite quotient realization over completed coefficients

Source: Stacks Project, Tags 099M, 0921 and 093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] koszulConstantFunctor_preservesZero
local instance finiteQuotientRealizationCochainMonoidal
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategory (CochainComplex (CompletedAdicModules T d) ℤ) :=
  CategoryTheory.flatConstantCochainMonoidal
    (J := ProEt.topology T) (O := completedAdicCommRing T d)
local instance finiteQuotientRealizationCochainMonoidalStruct
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    MonoidalCategoryStruct (CochainComplex (CompletedAdicModules T d) ℤ) :=
  (finiteQuotientRealizationCochainMonoidal T d).toMonoidalCategoryStruct

/-- Exactness and the normalized finite quotient comparison for the concrete
constant-module/scalar-extension functor. This statement has no exterior complexes,
augmentation maps, cones, or inverse limits of complexes.

Source: Stacks Project, sites-modules.tex, Tags 093J--093M, and proetale.tex,
proof of lemma-naive-completion (099M).
(blueprint: lem-weil-pbc-completed-koszul-finite-quotient-realization).

Proof: constant module sheafification is additive and exact. Identify the completed
ring and its scalar map with the constant-presentation completion through the
finite coefficient comparisons, using their section formulas and the uniqueness
of the scalar map. Completed constant sheaf reduction makes the completed unit
flat over the constant ring. Consequently scalar extension preserves finite
limits and colimits. Multiplication identifies the extension of the regular
module with the completed unit; take its inverse as c. The ring equivalence
ULift.ringEquiv identifies the span of the lifted generators with the lifted
ideal d.ideal, by ha, and identifies every positive quotient with its lift.
Finite coefficient identification, then extension of the single-complex
comparison and the left tensor unitor, gives eQ. On a local pure tensor its map
sends s tensor [x] to the residue of s times the recorded constant section [x].
For x=1 this is exactly the specified quotient tensor unit, proving the displayed
normalization. These formulas include the zero ring, unit ideal, empty scheme,
and the empty generator list; no nonzero generator is required. -/
theorem completedKoszulFiniteQuotientRealization
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
    ∃ (_hadd : E.Additive) (_hlim : PreservesFiniteLimits E)
      (_hcolim : PreservesFiniteColimits E)
      (c : U.X 0 ≅ E.obj (ModuleCat.of (ULift.{t + 1} A) (ULift.{t + 1} A)))
      (eQ : ∀ n : ℕ, (E.mapHomologicalComplex (.up ℤ)).obj
        (((ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (n + 1)))).extend ComplexShape.embeddingDownNat) ≅
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj U).asFunctor.obj
          (op n)),
      ∀ n : ℕ, c.hom ≫ E.map (ModuleCat.ofHom
        ((Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
          (n + 1)).mkQ) ≫
        E.map ((((ChainComplex.single₀ (ModuleCat.{t + 1} (ULift.{t + 1} A))).obj
          (ModuleCat.of (ULift.{t + 1} A)
            ((ULift.{t + 1} A) ⧸
              (Ideal.span (Set.range (fun i ↦ (ULift.up (a i) : ULift.{t + 1} A)))) ^
                (n + 1)))).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv) ≫
        (eQ n).hom.f 0 = (completedQuotientTensorUnit T d U n).f 0 := by
  let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  obtain ⟨hadd, hlim, hcolim⟩ := completedKoszulFiniteQuotientExactness T d
  obtain ⟨c, eQ, hQ⟩ := completedKoszulFiniteQuotientComparison T d r a ha
  exact ⟨hadd, hlim, hcolim, c, eQ, hQ⟩

end AlgebraicGeometry.Scheme
