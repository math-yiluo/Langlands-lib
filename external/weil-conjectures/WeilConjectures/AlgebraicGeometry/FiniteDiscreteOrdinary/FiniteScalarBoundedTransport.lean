/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteNormalizedScalarRestriction
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteScalarRestrictionConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Bounded constructibility under normalized finite scalar restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-- Restriction along a normalized map of finite coefficient rings preserves bounded
constructibility. Source: integral-finite-levels, first paragraph; the finite scalar
restriction step of integral-criterion reductions.
(blueprint: lem-pe-finite-scalar-bounded-transport).

Proof: use normalized encodings for both finite rings. Their coefficient square identifies
internal restriction with ordinary restriction, which preserves constructible sheaves.
Transport back through the coefficient comparison. Exact restriction preserves the standard
cohomological bounds and commutes with each homology functor, so the sheaf statement in
every degree proves the assertion for complexes. -/
theorem finite_scalar_bounded_transport
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [Finite A] [Finite B] [DiscreteTopology A] [DiscreteTopology B]
    (a : A →+* B) (ρ : coefficient A ⟶ coefficient B) [IsMonHom ρ]
    (hρ : pointConstants A ≫ ρ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫ pointConstants B)
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Internal B X))
    (hK : constantModelBoundedConstructible (coefficient B) X K) :
    constantModelBoundedConstructible (coefficient A) X
      ((Mod.comap ((upperStarFromPoint X).map ρ)).mapDerivedCategory.obj K) := by
  obtain ⟨eA, hA⟩ := finiteCoefficientModelComparison A X
  obtain ⟨eB, hB⟩ := finiteCoefficientModelComparison B X
  obtain ⟨e⟩ := finite_normalized_scalar_restriction A B a ρ hρ X eA eB
  let R : Internal B X ⥤ Internal A X :=
    Mod.comap ((upperStarFromPoint X).map ρ)
  have hc (M : Internal B X) (hM : IsConstantModelConstructible (coefficient B) X M) :
      IsConstantModelConstructible (coefficient A) X (R.obj M) := by
    apply (hA.constructible _).mpr
    apply constructible_of_iso A X (e.app M).symm
    exact (Scheme.proEtaleFiniteScalarRestriction_constructible X A B a).2.2.1
      _ ((hB.constructible M).mp hM)
  have := (constantModelConstructibleFiniteTor_wellDefined (coefficient A) X).1
  refine ⟨R.bounded_mapDerivedCategory_obj hK.1, fun q ↦ ?_⟩
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible (coefficient A) X)
    ((R.mapDerivedCategoryHomologyFunctorIso q).app K) (hc _ (hK.2 q))

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
