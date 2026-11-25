/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.CategoryTheory.Exact.NormalizedTensorAdjunctionInsertion
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAdjunctionInsertion
import WeilConjectures.Tactic.TransportExact

/-! # Tensor of normalized scalar-adjunction insertions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), finite-level scalar/tensor reduction.
(blueprint: lem-pur-tate-tensor-adjunction-insertion)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
-- Elaborate sheaf and derived tensor products along the instance paths of `derivedTensor` and
-- `singleFunctorObjTensorIso`, and check declarations one at a time, to bound kernel memory.
attribute [local instance 10000] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

/-- The scalar extension–restriction adjunction of étale sheaves is monoidal for the ordinary
sheafified scalar balancing map. -/
private theorem etaleSheafExtendScalarsAdjunction_isMonoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T).IsMonoidal :=
  isMonoidal_sheafAdjunction T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

/-- The canonical scalar representative is the transpose of the localized ordinary unit. -/
private theorem scalarExtensionRepresentative_eq_homEquiv_symm
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    scalarExtensionRepresentative φ T P =
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory).homEquiv _ _).symm
      (DerivedCategory.Q.map
        (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex
          (.up ℤ)).unit.app P) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
          (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P)) := by
  unfold scalarExtensionRepresentative
  rw [mapComplex_unit_formula (ProEtale.etaleSheafExtendScalarsAdjunction φ T) P]
  rfl

/-- The published scalar tensor comparison is normalized on representatives. -/
private theorem tensorIso_tensorNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ExceptionalCoefficients.TensorNormalization φ T (ExceptionalCoefficients.tensorIso φ T) := by
  have he : ExceptionalCoefficients.tensorIso φ T =
      (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose :=
    eq_of_heq (ExceptionalCoefficients.siteTensorIso_existsUnique φ T).choose_spec.1
  rw [he]
  exact (ExceptionalCoefficients.tensorIso_existsUnique φ T).choose_spec.1

/-- The scalar insertion is the exact-single insertion for the derived scalar adjunction. -/
private theorem scalarAdjointInsertion_eq_adjointInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (f : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P) :
    SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ f =
      SheafExactDegreeZero.adjointInsertion (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) f := by
  unfold SheafExactDegreeZero.scalarAdjointInsertion
  rfl

-- The proof instantiates a general-coefficient lemma by first-order matching and transports it
-- along small congruence proofs (`fo_apply`): a direct `exact` makes the kernel unfold the
-- derived tensor structures and runs out of memory.
/-- Tensoring the two normalized scalar insertions agrees with inserting their ordinary
semilinear tensor product, under the published scalar tensorator and flat-single comparisons.
The ordinary restriction tensorator is `Functor.LaxMonoidal.μ` of exact scalar restriction.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), finite-level scalar/tensor reduction.
(blueprint: lem-pur-tate-tensor-adjunction-insertion)

Proof:
1. The tensor of the two flat source sheaves is flat by exactness of successive tensoring.
Scalar extension of a flat sheaf is flat: restriction identifies tensoring with its extension
with ordinary tensoring by that sheaf. Restriction preserves and reflects exactness. This
uses the sheaf tensor balancing relations and the exact restriction in
`lem-pur-sheaf-ring-derived-coefficient-adjunction`; no flatness of the ring map is needed.
2. For each source sheaf and their tensor, use its flat single as a K-flat representative
(`lem-sf-etale-single-flat-tensor`). The normalized coefficient adjunction identifies its
insertion with the canonical scalar representative followed by the single of the ordinary
adjunct, sending x tensor b to b times eta(x). The inverse exact-single comparison in
`def-sp-exact-degree-zero-adjoint-interface` is precisely the one in this calculation.
3. The representative square of `def-pur-exceptional-coefficient-normalizations` identifies
the published tensorIso with balancing (x tensor y) tensor b mapped to
(x tensor 1) tensor (y tensor b). Apply
`lem-pur-etale-single-tensorator-naturality` to the two ordinary adjuncts and cancel the
canonical representative isomorphisms. The desired equation reduces to equality of the
ordinary balanced tensor maps. All complexes are in degree zero, so no shift sign occurs.
4. The left ordinary composite sends (x tensor y) tensor b to
eta1(x) tensor b eta2(y), equal to b times (eta1(x) tensor eta2(y)), the right composite.
The formulas are balanced and commute with restriction. The presheaf tensor universal
property and then sheafification prove equality of sheaf maps. This uses
`def-pur-sheaf-tensor-product`, without any assertion about generation of global sections.
Apply the single functor and the representative square to obtain the displayed equality. -/
theorem tateTensor_scalarAdjointInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L₁ L₂ : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (P₁ P₂ : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hL₁ : ObjectProperty.flat L₁) (_hL₂ : ObjectProperty.flat L₂)
    (hP₁ : ObjectProperty.flat P₁) (_hP₂ : ObjectProperty.flat P₂)
    (η₁ : L₁ ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P₁)
    (η₂ : L₂ ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj P₂) :
    (ExceptionalCoefficients.tensorIso φ T).hom.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₁,
          (_root_.DerivedCategory.singleFunctor _ 0).obj L₂) ≫
      (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η₁ ⊗ₘ
        SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η₂) ≫
      (singleFunctorObjTensorIso P₁ P₂ hP₁).hom =
    (scalarExtension φ T).map (singleFunctorObjTensorIso L₁ L₂ hL₁).hom ≫
      SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ
        ((η₁ ⊗ₘ η₂) ≫
          Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ) P₁ P₂) := by
  have := etaleSheafExtendScalarsAdjunction_isMonoidal φ T
  -- The normalization hypothesis is left as a goal, so that `fo_apply` does not seal the whole
  -- proof as an auxiliary theorem, which would make the kernel check the statement twice.
  fo_apply siteNormalizedTensor_adjointInsertion using
    (ProEtale.etaleSheafExtendScalars φ T), (Sheaf.restrictScalars T.smallEtaleTopology φ),
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T), (scalarExtension φ T),
    (Adjunction.ofIsRightAdjoint
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory),
    (scalarExtensionRepresentative φ T), (scalarExtensionRepresentative_eq_homEquiv_symm φ T),
    (ExceptionalCoefficients.tensorIso φ T), _, hL₁, hP₁,
    η₁, η₂,
    (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η₁),
    (scalarAdjointInsertion_eq_adjointInsertion φ T η₁),
    (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η₂),
    (scalarAdjointInsertion_eq_adjointInsertion φ T η₂),
    (SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ
      ((η₁ ⊗ₘ η₂) ≫
        Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ) P₁ P₂)),
    (scalarAdjointInsertion_eq_adjointInsertion φ T _)
  transport_exact tensorIso_tensorNormalization φ T

end AlgebraicGeometry.Etale
