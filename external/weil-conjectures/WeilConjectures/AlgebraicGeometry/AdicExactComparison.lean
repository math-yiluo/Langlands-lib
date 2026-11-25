/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.CategoryTheory.ConstantInverseImageScalarNormalization
import all WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Identifying the adic pullback with exact comparison

Source: Stacks Project, Tags 03D2, 099R and 09AL.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard adicFiniteComparisonData
  adicFinitePullbackData

private theorem ordinaryComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Nonempty (adicFiniteOrdinaryPullback.{u, v} X A ≅
      AlgebraicGeometry.ProEtale.constructibleComparisonPullback X A) := by
  let J := smallModelComparisonEtaleTopology.{u, v} X
  let K := coefficientProEtaleModelTopology.{u, v} X
  let G := smallModelComparisonInclusion.{u, v} X
  let L := smallModelComparisonPullback.{u, v} X
  let adj := smallModelProEtaleComparison.{u, v} X
  let F := adicFiniteComparisonData.{u, v} X
  let R := constant J A
  let S := constant K A
  let c := constantMap F A
  let φ : R ⟶ (G.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S :=
    ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
      ((Functor.const (smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ).obj (CommRingCat.of A))
      ((G.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj S)).symm
      (Functor.whiskerLeft G.op
        (toSheafify K ((Functor.const _).obj (CommRingCat.of A))))
  let f := CategoryTheory.siteContinuousRingedTopos G L adj S R φ
  have hn := constantInverseImageScalarNormalization J K G L adj F A
  have hc : (sheafCompose K (CategoryTheory.forget CommRingCat)).map c =
      (F.algebra R).ringUnderlying.inv ≫ f.ringMap := by
    change _ = (F.algebra R).ringUnderlying.inv ≫ (adj.homEquiv _ _).symm _
    rw [← hn]
    exact ((F.algebra R).ringUnderlying.inv_hom_id_assoc _).symm
  obtain ⟨am, _⟩ := supplied_module_adjunction f (F.rings.obj R) (F.algebra R) c hc
  have a : adicFiniteOrdinaryPullback.{u, v} X A ⊣
      SheafOfModules.pushforward
        (AlgebraicGeometry.ProEtale.constructibleComparisonRingMap X A) := am
  exact ⟨a.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction.{max v (u + 1)}
      (F := smallModelComparisonInclusion.{u, v} X)
      (AlgebraicGeometry.ProEtale.constructibleComparisonRingMap X A))⟩

/-- The normalized adic inverse image is the localization of exact module comparison.
Source: Stacks Project, Tags 03D2, 099R and 09AL; identification of the two
presentations of inverse image in the parent proof step 3.
(auxiliary; not a blueprint node).

Proof: the algebraic lift of the set-sheaf inverse image, followed by scalar
extension along its constant-ring identification, is left adjoint to module
direct image with its constant-section ring map. The Kan-extension construction
constructibleComparisonPullback is left adjoint to that same direct image.
The units identify their coefficient maps: both are adjoint to constant
sections. Uniqueness of left adjoints gives an isomorphism of the ordinary
module functors. The latter functor is exact, so its action on complexes
preserves all quasi-isomorphisms. Its localization is therefore also its left
derived functor. Transport the ordinary isomorphism to complexes and use the
universal property of adicFinitePullbackData to identify its derived functor
with this exact localization. Whisker this isomorphism by Q and compose with
the localization factorization. No bounds or constructibility are used. -/
theorem adicExactComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Nonempty (Q (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⋙
        adicFinitePullback.{u, v} X A ≅
      AlgebraicGeometry.ProEtale.constructibleComparisonComplexPullback X A ⋙
        Q (constant (coefficientProEtaleModelTopology.{u, v} X) A)) := by
  let R := constant (smallModelComparisonEtaleTopology.{u, v} X) A
  let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
  let P := adicFiniteOrdinaryPullback.{u, v} X A
  let T := AlgebraicGeometry.ProEtale.constructibleComparisonPullback X A
  obtain ⟨e⟩ := ordinaryComparison X A
  have : PreservesFiniteLimits T :=
    (AlgebraicGeometry.ProEtale.constructibleComparisonPullback_exact_faithful X A).1
  have : T.IsLeftAdjoint := (SheafOfModules.pullbackPushforwardAdjunction.{max v (u + 1)}
      (F := smallModelComparisonInclusion.{u, v} X)
    (AlgebraicGeometry.ProEtale.constructibleComparisonRingMap X A)).isLeftAdjoint
  have : PreservesFiniteLimits P := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits P := preservesFiniteColimits_of_natIso e.symm
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let d := adicFinitePullbackData.{u, v} X A
  have := d.universal
  have hi : IsIso d.comparison :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts d.functor d.comparison
      (P.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso (ComplexShape.up ℤ))
  exact ⟨asIso d.comparison ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) (Q S)⟩

end AlgebraicGeometry.Scheme
