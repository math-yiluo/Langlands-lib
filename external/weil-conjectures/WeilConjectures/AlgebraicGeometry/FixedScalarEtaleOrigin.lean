/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import WeilConjectures.AlgebraicGeometry.FixedScalarComplexModel
import WeilConjectures.AlgebraicGeometry.AdicResidueFieldTensor
import WeilConjectures.AlgebraicGeometry.CoefficientFieldTorBounds
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.AlgebraicGeometry.FixedScalarEtaleConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.FixedScalarOrdinaryComparison

/-! # Etale origin under fixed-scalar and small-site equivalences

Source: Stacks Tags 03CY, 09A5 and 09AL; Bhatt--Scholze, Remark 6.3.2.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem coefficientConstructible_of_iso (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    {F G : ConstantCompletion.Mod
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, u} X) k)}
    (e : F ≅ G) (hF : IsCoefficientConstructibleEtaleModule.{u, u} X k F) :
    IsCoefficientConstructibleEtaleModule.{u, u} X k G := by
  intro U hU
  obtain ⟨S, hc, hs⟩ := hF U hU
  refine ⟨S, hc, fun i V ↦ ?_⟩
  obtain ⟨R, hR, hM⟩ := hs i V
  refine ⟨R, hR, fun W f hf ↦ ?_⟩
  obtain ⟨M, hm, ⟨j⟩⟩ := hM W f hf
  let j' := (coefficientEtaleFixedPullback.{u, u} (S.immersion i ≫ U.ι) k).mapIso
    ((coefficientModelFixedScalars _ k).mapIso e)
  exact ⟨M, hm, ⟨((smallModelComparisonEtaleTopology.{u, u} (S.domain i)).overPullback
    (ModuleCat.{u + 1} k) W).mapIso j'.symm ≪≫ j⟩⟩

private theorem boundedPresentation (X : Scheme.{u}) [IsNoetherian X]
    (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, u} X) k))
    (e : (ConstantCompletion.Q _).obj ((fixedScalarEtaleComplexToModel X k).obj C) ≅ K) :
    IsCoefficientBoundedConstructibleEtale.{u, u} X k K ↔
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (C.homology q)) ∧
      ∀ q : ℤ, IsConstructibleSheaf (C.homology q) := by
  let F := (fixedScalarEtaleSheafEquivalence X k).functor
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, u} X) k))
  let i (q : ℤ) : (coefficientModelCohomology _ q).obj K ≅ F.obj (C.homology q) :=
    (coefficientModelCohomology _ q).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
        (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app C
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨a, b, hab, fun q hq ↦ ?_⟩, fun q ↦ ?_⟩
    · exact IsZero.of_full_of_faithful_of_isZero F _ ((hz q hq).of_iso (i q).symm)
    · exact (fixedScalarEtale_constructible_sheaf X k _).mp
        (coefficientConstructible_of_iso X k (i q) (hc q))
  · rintro ⟨⟨a, b, hab, hz⟩, hc⟩
    refine ⟨fun q ↦ ?_, a, b, hab, fun q hq ↦ ?_⟩
    · exact coefficientConstructible_of_iso X k (i q).symm
        ((fixedScalarEtale_constructible_sheaf X k _).mpr (hc q))
    · exact (F.map_isZero (hz q hq)).of_iso (i q)

private theorem comparisonPresentation (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ) :
    Nonempty ((ConstantCompletion.Q _).obj
      ((ProEtale.constructibleComparisonComplexPullback.{u, u} X k).obj
        ((fixedScalarEtaleComplexToModel X k).obj C)) ≅
      fixedScalarDerivedModel X k
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapHomologicalComplex
          (.up ℤ)).obj C)) := by
  have : (ProEtale.constructibleComparisonPullback.{u, u} X k).IsLeftAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction
      (F := smallModelComparisonInclusion.{u, u} X)
      (ProEtale.constructibleComparisonRingMap X k)).isLeftAdjoint
  have : (ProEtale.constructibleComparisonPullback.{u, u} X k).Additive :=
    let := (ProEtale.constructibleComparisonPullback_exact_faithful X k).1
    Functor.additive_of_preserves_binary_products _
  obtain ⟨o⟩ := fixedScalar_ordinary_comparison X k
  unfold fixedScalarDerivedModel
  rw [fixedScalarComplexToModel_eq]
  exact ⟨(ConstantCompletion.Q _).mapIso
    ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).app C)⟩

/-- Changing between constant-ring modules on the small models and fixed-scalar
sheaves on the original sites preserves the etale-origin witness. This concerns an
arbitrary residue-field complex, without integral coefficients or completeness.
Source: Stacks Tags 03CY, 09A5 and 09AL; Bhatt--Scholze, Remark 6.3.2
(auxiliary; not a blueprint node).

Proof: On the etale site, precomposition by AsSmall.down is an exact equivalence.
Compose it with the inverse constant-scalar restriction equivalence, just as in
fixedScalarComplexToModel on the pro-etale site. The inverse equivalences send a
cochain representative P of C to an etale fixed-scalar complex D. The unit and counit
of these equivalences, and the canonical localization factorizations, identify Q(P)
with C and Q of its comparison pullback with the model of the pullback of D.
The ordinary comparison commutes with scalar restriction: both right adjoints are
precomposition along the same inclusion with the same constant scalar action, so
uniqueness of the left adjoint gives the comparison, normalized on constant sections.
Homology commutes with these exact equivalences. Apply Noetherian global
constructibility to each homology sheaf and retain the same immersed strata and
trivializing covering sieves; fixed-scalar restriction identifies the finite module
models. Thus bounds and constructibility transport in both directions.
Over the field k, tensoring with any degree-zero module sheaf is exact, on either
site and in either scalar presentation. Tensor homology is therefore homology
tensored with that module. The transported cohomological bounds give the Tor
interval by sfbFieldTensor_bounds on the original etale site, and by the same
K-flat tensor calculation on the small etale site. Conversely the explicit bounded
constructible clause already supplies the bounds. Compose the two localization
comparison isomorphisms with the given origin isomorphism, using its inverse when
necessary. This constructs both existential witnesses without any hypothesis on T.
Empty schemes, zero complexes and arbitrary unbounded representatives are included. -/
theorem fixedScalar_etaleOrigin (X : Scheme.{u}) [IsNoetherian X]
    (k : Type (u + 1)) [Field k]
    (T : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)) ℤ) :
    (∃ C : ConstantCompletion.D (ConstantCompletion.constant
        (smallModelComparisonEtaleTopology.{u, u} X) k),
      IsCoefficientBoundedConstructibleEtale.{u, u} X k C ∧
        (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ C a b) ∧
        ∃ P : ConstantCompletion.Cx (ConstantCompletion.constant
            (smallModelComparisonEtaleTopology.{u, u} X) k),
          Nonempty ((ConstantCompletion.Q _).obj P ≅ C) ∧
            Nonempty ((ConstantCompletion.Q _).obj
              ((ProEtale.constructibleComparisonComplexPullback.{u, u} X k).obj P) ≅
                fixedScalarDerivedModel X k T)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ,
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) ∧
        (∀ q : ℤ, IsConstructibleSheaf (C.homology q)) ∧
        Nonempty (DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj
          (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapHomologicalComplex
             (.up ℤ)).obj C)) ∧
        ∃ a b : ℤ, a ≤ b ∧
          ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) (q : ℤ),
            (q < a ∨ b < q) →
              IsZero ((sfbEtaleTensorDegreeZero X k C N).homology q) := by
  let E := fixedScalarEtaleComplexToModel X k
  let Q := ConstantCompletion.Q
    (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, u} X) k)
  let L := ProEtale.constructibleComparisonComplexPullback.{u, u} X k
  let G := fixedScalarProEtaleDerivedFunctor X k
  constructor
  · rintro ⟨K, hc, _, P, ⟨e⟩, ⟨j⟩⟩
    let C := E.objPreimage P
    let c : E.obj C ≅ P := E.objObjPreimageIso P
    have hC := (boundedPresentation X k C K (Q.mapIso c ≪≫ e)).mp hc
    obtain ⟨a, b, hab, hz⟩ := hC.1
    obtain ⟨s⟩ := comparisonPresentation X k C
    let D := ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapHomologicalComplex
      (.up ℤ)).obj C
    let g : G.obj (DerivedCategory.Q.obj T) ≅ G.obj (DerivedCategory.Q.obj D) :=
      fixedScalarProEtaleDerivedFactors X k T ≪≫ j.symm ≪≫
        (ConstantCompletion.Q _).mapIso (L.mapIso c.symm) ≪≫ s ≪≫
          (fixedScalarProEtaleDerivedFactors X k D).symm
    refine ⟨C, hC.1, hC.2, ⟨G.preimageIso g⟩, a, b, hab, ?_⟩
    exact sfbFieldTensor_bounds X k C a b hz
  · rintro ⟨C, hb, hc, ⟨j⟩, _⟩
    let P := E.obj C
    let K := Q.obj P
    have hK := (boundedPresentation X k C K (Iso.refl _)).mpr ⟨hb, hc⟩
    obtain ⟨a, b, hab, hz⟩ := hK.2
    have ht := coefficientFieldTorBounds _ k K a b hab hz
    obtain ⟨s⟩ := comparisonPresentation X k C
    let D := ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapHomologicalComplex
      (.up ℤ)).obj C
    exact ⟨K, hK, ⟨a, b, ht⟩, P, ⟨Iso.refl _⟩,
      ⟨s ≪≫ (fixedScalarProEtaleDerivedFactors X k D).symm ≪≫ G.mapIso j.symm ≪≫
        fixedScalarProEtaleDerivedFactors X k T⟩⟩

end AlgebraicGeometry.Scheme
