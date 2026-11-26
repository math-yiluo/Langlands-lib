import Langlands.BruhatTits.IntegralModels.GeneralClausesReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement
import Langlands.BruhatTits.IntegralModels.ModelFamily
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelDescent
import Langlands.BruhatTits.IntegralModels.ApartmentFacetBounds

/-! # The general morphism clauses of KP Axiom 4.1.22 from the unramified kernel statement

The general clauses of KP Axiom 4.1.22 ask that every required model morphism
have a smooth, connected and unipotent special-fibre kernel. This module
derives them from `UnramifiedModelKernelStatement` (KP Proposition 8.4.15 over
the maximal unramified integers). The family must satisfy a K-level description
of its neutral models: the base change of each neutral model to
`fixedFieldIntegers F` has integral points `E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance generalMorphismAxiomsAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance generalMorphismAxiomsScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance generalMorphismAxiomsLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  haveI : IsLocalHom (algebraMap F (inertiaFixedField F)) :=
    isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

namespace RelativeComponentModelHom

-- Matching the instance arguments of the base-changed models against those
-- of `UnramifiedModelKernelStatement` needs more than the default budget.
set_option maxHeartbeats 1000000 in
/-- **One ordered pair.** Suppose the base changes of the target and source
neutral models to the maximal unramified integers have the integral points of
`Ωa` and `Ωa'`, read in one translated apartment chart of `C`. Suppose also
that `Ωa` is nonempty, `Ωa'` is bounded and `Ωa ⊆ closure Ωa'`. Then the
special-fibre kernel of the neutral model morphism is smooth, connected and
unipotent. -/
theorem hasSmoothConnectedUnipotentKernel_of_unramified
    (hker : UnramifiedModelKernelStatement.{u})
    {source target : RelativeComponentModelData ↥𝒪[F] F G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (Ωa Ωa' : Set C.Apartment) (hne : Ωa.Nonempty)
    (hbdd : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa'))
    (hcl : Ωa ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ωa')
    (hN : target.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa))
    (hN' : source.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa')) :
    φ.HasSmoothConnectedUnipotentKernel := by
  have hs : target.neutral.baseChangeUnramified.IsSmooth :=
    target.neutral.isSmooth_baseChange _ _ target.neutral_smooth
  have hs' : source.neutral.baseChangeUnramified.IsSmooth :=
    source.neutral.isSmooth_baseChange _ _ source.neutral_smooth
  have key : IsSmoothConnectedUnipotent (kernel φ.neutral.specialFibreMap) :=
    φ.neutral.isSmoothConnectedUnipotent_kernel_of_baseChangeUnramified fun ψ' =>
      hker F G C E g Ωa Ωa' hne hbdd hcl target.neutral.baseChangeUnramified
        source.neutral.baseChangeUnramified hs hs' hN hN' ψ'
  exact key

end RelativeComponentModelHom

section Transfer

variable {B : ValuationBuildingData G}
  {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}

/-- A real affine map of apartments is continuous for the affine topologies. -/
theorem continuous_affineApartmentMap (a : B.Apartment →ᵃ[ℝ] C.Apartment) :
    @Continuous _ _ (affineApartmentTopology B)
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) a := by
  let := affineApartmentTopology B
  refine continuous_iInf_rng.2 fun f => continuous_induced_rng.2 ?_
  exact continuous_affineApartmentFunctional B (f.comp a)

/-- A real affine map of apartments carries the closure order to the closure order. -/
theorem image_subset_closure_image (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    {Ωa Ωa' : Set B.Apartment} (h : Ωa ⊆ apartmentClosure B Ωa') :
    a '' Ωa ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) (a '' Ωa') := by
  let := affineApartmentTopology B
  let : TopologicalSpace C.Apartment :=
    ⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance
  exact (Set.image_mono h).trans
    (image_closure_subset_closure_image (continuous_affineApartmentMap a))

/-- A real affine map of apartments carries bounded subsets to bounded subsets. -/
theorem bddAbove_image_image (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    {Ωa : Set B.Apartment} (h : B.IsBoundedSubset Ωa) (f : C.Apartment →ᵃ[ℝ] ℝ) :
    BddAbove (f '' (a '' Ωa)) := by
  rw [Set.image_image]
  exact h (f.comp a)

/-- An equivariant map of buildings compatible with the apartment maps sends a
translated chart image to the corresponding translated chart image. -/
theorem image_translatedApartmentMap (e : B.ReducedBuilding → C.ReducedBuilding)
    (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he_smul : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (he_apt : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (g : rationalPoints G) (Ωa : Set B.Apartment) :
    e '' (B.translatedApartmentMap g '' Ωa) =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) '' (a '' Ωa) := by
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr fun w _ => ?_
  change e (g • B.apartmentMap w) = _
  rw [he_smul, he_apt]

end Transfer

namespace BuildingModelFamily

variable {B : ValuationBuildingData G}

/-- Every required morphism pair has presentations `Ωa`, `Ωa'` in one
translated chart with `Ωa ⊆ closure Ωa'`, provided faces lie in the closure of
the facets containing them. -/
theorem exists_chart_of_modelMorphismRequired
    (hface : ∀ Fa Fa' : Set B.Apartment,
      AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' → Fa ⊆ apartmentClosure B Fa')
    {Ω Ω' : BuildingModelIndex B} (h : ModelMorphismRequired B Ω Ω') :
    ApartmentSubsetPrecedes B Ω Ω' := by
  rcases h with h | ⟨Fb, Fb', hΩ, hΩ', g, Fa, Fa', hfa, hF, hF'⟩
  · exact h
  · exact ⟨g, Fa, Fa', hΩ.trans hF, hΩ'.trans hF', hface Fa Fa' hfa⟩

-- The two integral-point rewrites below need more than the default budget.
set_option maxHeartbeats 1000000 in
/-- **The general morphism clauses of KP Axiom 4.1.22.** Take a model family
over `𝒪[F]` and a K-level datum `(C, E, e, a)`, where `e` is a
`G(F)`-equivariant map of buildings compatible with the affine apartment map
`a`. Suppose the base change of every neutral model to the maximal unramified
integers has integral points `E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)`. Assume
also that every apartment presentation of an index is bounded and that faces
lie in the closure of the facets containing them. Then
`UnramifiedModelKernelStatement` gives `M.SatisfiesGeneralMorphismAxioms`. -/
theorem satisfiesGeneralMorphismAxioms_of_unramified
    (hker : UnramifiedModelKernelStatement.{u})
    (M : BuildingModelFamily B ↥𝒪[F])
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he_smul : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (he_apt : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (hpoints : ∀ Ω : BuildingModelIndex B,
      (M.model Ω).neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω.val))
    (hbdd : ∀ (Ω : BuildingModelIndex B) (g : rationalPoints G) (Ωa : Set B.Apartment),
      Ω.val = B.translatedApartmentMap g '' Ωa → B.IsBoundedSubset Ωa)
    (hface : ∀ Fa Fa' : Set B.Apartment,
      AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' → Fa ⊆ apartmentClosure B Fa') :
    M.SatisfiesGeneralMorphismAxioms := by
  intro Ω Ω' h
  rw [RelativeComponentModelHom.satisfiesGeneralSpecialFibreClauses_iff]
  obtain ⟨g, Ωa, Ωa', hΩ, hΩ', hcl⟩ := exists_chart_of_modelMorphismRequired hface h
  have hne : (a '' Ωa).Nonempty := by
    obtain ⟨y, hy⟩ := Ω.nonempty
    rw [hΩ] at hy
    obtain ⟨w, hw, -⟩ := hy
    exact ⟨a w, w, hw, rfl⟩
  refine (M.morphism Ω Ω' h).hasSmoothConnectedUnipotentKernel_of_unramified hker C E
    (rationalExtend F (inertiaFixedField F) G g) (a '' Ωa) (a '' Ωa') hne
    (bddAbove_image_image a (hbdd Ω' g Ωa' hΩ'))
    (image_subset_closure_image a hcl) ?_ ?_
  · rw [hpoints Ω, hΩ, image_translatedApartmentMap e a he_smul he_apt]
  · rw [hpoints Ω', hΩ', image_translatedApartmentMap e a he_smul he_apt]

end BuildingModelFamily

section Axioms

variable (P : ParahoricBuildingData G) (R : P.toValuationBuildingData.PolysimplicialRealization)
  (T : P.toValuationBuildingData.ApartmentSplitting)
  (h1 : P.SatisfiesBuildingAxiom R) (h2 : P.HasBoundedOpenStabilizers)
  (h3 : P.SatisfiesAffineApartmentAxiom T) (h4 : P.HasRootReflections)
  (h5 : P.SatisfiesApartmentAxioms) (h6 : P.HasCompatibleApartmentFacets)
  (h7 : P.HasTitsSystem)

include h1 h2 h3 h4 h5 h6 h7 in
/-- **Every apartment presentation of an index is bounded.** Under the seven
predicates of the corrected opening of KP Section 4.2, if an index `Ω` of a
model family equals `g • A(Ωa)`, then `Ωa` is bounded. The index has some
bounded presentation: it is either a nonempty bounded subset of a translated
apartment or a translated facet, and facets are bounded. Boundedness then
transfers between charts. -/
theorem isBoundedSubset_of_buildingModelIndex
    (Ω : BuildingModelIndex P.toValuationBuildingData) {g : rationalPoints G}
    {Ωa : Set P.toValuationBuildingData.Apartment}
    (hΩ : Ω.val = P.toValuationBuildingData.translatedApartmentMap g '' Ωa) :
    P.toValuationBuildingData.IsBoundedSubset Ωa := by
  rcases Ω.property with ⟨g₀, Ωa₀, -, hb, h₀⟩ | ⟨g₀, Fa, hFa, h₀⟩
  · exact isBoundedSubset_of_image_translatedApartmentMap_eq_of_axioms P R T
      h1 h2 h3 h4 h5 h6 h7 (hΩ.symm.trans h₀) hb
  · exact isBoundedSubset_of_image_translatedApartmentMap_eq_of_axioms P R T
      h1 h2 h3 h4 h5 h6 h7 (hΩ.symm.trans h₀)
      (isBoundedSubset_of_isFacet_of_satisfiesApartmentAxioms _ h5 hFa)

include h1 h2 h3 h4 h5 h6 h7 in
/-- **The general morphism clauses of KP Axiom 4.1.22 on the target data.**
For parahoric building data satisfying the seven predicates of the target
statement, the hypotheses `hbdd` and `hface` of
`satisfiesGeneralMorphismAxioms_of_unramified` hold. So a model family over
`𝒪[F]` whose neutral models have the K-level integral points
`E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)` after base change to the maximal
unramified integers satisfies `M.SatisfiesGeneralMorphismAxioms`, given
`UnramifiedModelKernelStatement`. -/
theorem satisfiesGeneralMorphismAxioms_of_unramified_of_axioms
    (hker : UnramifiedModelKernelStatement.{u})
    (M : BuildingModelFamily P.toValuationBuildingData ↥𝒪[F])
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (e : P.toValuationBuildingData.ReducedBuilding → C.ReducedBuilding)
    (a : P.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment)
    (he_smul : ∀ (g : rationalPoints G) (z : P.toValuationBuildingData.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (he_apt : ∀ w : P.toValuationBuildingData.Apartment,
      e (P.toValuationBuildingData.apartmentMap w) = C.apartmentMap (a w))
    (hpoints : ∀ Ω : BuildingModelIndex P.toValuationBuildingData,
      (M.model Ω).neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω.val)) :
    M.SatisfiesGeneralMorphismAxioms :=
  BuildingModelFamily.satisfiesGeneralMorphismAxioms_of_unramified hker M C E e a
    he_smul he_apt hpoints
    (fun Ω _ _ hΩ => isBoundedSubset_of_buildingModelIndex P R T h1 h2 h3 h4 h5 h6 h7 Ω hΩ)
    (fun _ _ h => subset_apartmentClosure_of_isFaceOf _ h)

end Axioms

end Langlands.BruhatTits.IntegralModels
