import Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientStatement
import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientStatement
import Langlands.Geometry.Building.ChamberClosureOrbit
import Langlands.Geometry.Building.GaloisFacetAction
import Langlands.Galois.Local.SeparableUnramifiedFrobenius

/-! # From the residue quotient for a Frobenius lift to the chamber quotient input -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The residue quotient for every Frobenius lift suffices for the chamber
quotient input at a twisted-fixed point. -/
def UnramifiedTwistedChamberQuotientResidueReductionStatement : Prop :=
  UnramifiedTwistedResidueQuotientStatement.{u} →
    UnramifiedTwistedChamberQuotientStatement.{u}

private instance unramifiedTwistedResidueReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

namespace KPApartmentData

section GaloisRoots

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

private instance unramifiedTwistedResidueReductionExtendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- Precomposing an affine root with the coefficient action of `σ` on the
apartment gives an affine root again. -/
theorem exists_affineRoot_comp_galoisAction (σ : K ≃ₐ[k] K)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (hψ : ψ ∈ D.affineRoots) :
    ∃ ψ' ∈ D.affineRoots, ∀ z, ψ (galoisAction k K i D hD σ z) = ψ' z := by
  obtain ⟨ψ', rfl⟩ := (galoisAffineFunctional k K i D hD σ).surjective ψ
  exact ⟨ψ', (galoisAffineFunctional_mem_affineRoots_iff k K i D hD σ ψ').mp hψ,
    fun z => galoisAffineFunctional_apply_map k K i D hD σ ψ' z⟩

end GaloisRoots

end KPApartmentData

/-- A chamber presentation through `y` is carried to a chamber presentation
through `c • σ y` by the semilinear action of `σ` followed by translation by
`c`, provided the apartment action of `σ` permutes the affine roots and carries
facets and facet closures to facets and facet closures. -/
theorem hasChamberClosurePresentation_semilinear {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
    (A : MaximalUnramified.SemilinearApartmentData B)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (c : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hroots : ∀ ψ ∈ B.affineRoots, ∃ ψ' ∈ B.affineRoots, ∀ z, ψ (A.apartment σ z) = ψ' z)
    (hfacet : ∀ x, A.apartment σ '' AffineRootSystem.facet B.affineRoots x =
      AffineRootSystem.facet B.affineRoots (A.apartment σ x))
    (hclosure : ∀ x, A.apartment σ '' AffineRootSystem.facetClosure B.affineRoots x =
      AffineRootSystem.facetClosure B.affineRoots (A.apartment σ x))
    {Y : Set B.ReducedBuilding} {y y' : B.ReducedBuilding}
    (hY : B.HasChamberClosurePresentation Y y) (hy : c • A.action σ y = y') :
    B.HasChamberClosurePresentation ((fun z => c • A.action σ z) '' Y) y' := by
  obtain ⟨g, x₀, x, hgen, rfl, hx, rfl⟩ := hY
  have hA : ∀ w : B.Apartment, c • A.action σ (g • B.apartmentMap w) =
      (c * rationalConjugate F (inertiaFixedField F) G σ g) •
        B.apartmentMap (A.apartment σ w) := by
    intro w
    rw [A.action_smul, A.action_apartmentMap, mul_smul]
  refine ⟨c * rationalConjugate F (inertiaFixedField F) G σ g, A.apartment σ x₀,
    A.apartment σ x, ?_, ?_, ?_, (hA x).symm.trans hy⟩
  · intro ψ hψ
    obtain ⟨ψ', hψ', h⟩ := hroots ψ hψ
    rw [h]
    exact hgen ψ' hψ'
  · rw [Set.image_image, ← hfacet x₀, Set.image_image]
    exact Set.image_congr fun w _ => hA w
  · rw [← hclosure x₀]
    exact Set.mem_image_of_mem _ hx

/-- Residue quotient data through a point fixed by `z ↦ c • σ z`, with kernel
fixation for every presented chamber and transitivity on presented chambers,
give the finite-field chamber quotient for the twist `g ↦ c σ(g) c⁻¹`, provided
the apartment action of `σ` permutes the affine roots and carries facets and
facet closures to facets and facet closures. -/
theorem hasFiniteFieldChamberQuotient_semilinear {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
    (A : MaximalUnramified.SemilinearApartmentData B)
    (κ Ω : Type u) [Field κ] [Fintype κ] [Field Ω] [Algebra κ Ω] [Algebra.IsAlgebraic κ Ω]
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (c : rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hroots : ∀ ψ ∈ B.affineRoots, ∃ ψ' ∈ B.affineRoots, ∀ z, ψ (A.apartment σ z) = ψ' z)
    (hfacet : ∀ x, A.apartment σ '' AffineRootSystem.facet B.affineRoots x =
      AffineRootSystem.facet B.affineRoots (A.apartment σ x))
    (hclosure : ∀ x, A.apartment σ '' AffineRootSystem.facetClosure B.affineRoots x =
      AffineRootSystem.facetClosure B.affineRoots (A.apartment σ x))
    {y : B.ReducedBuilding} (hy : c • A.action σ y = y)
    (hres : ∃ R : GroupScheme (Spec (CommRingCat.of κ)), IsConnectedReductive R ∧
      ∃ (P : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
        (q : P →* (Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶
          ((GroupScheme.baseChange (algebraBaseMap κ Ω)).obj R).X))
        (θP : P → P),
        P ≤ B.fixer y ∧ Function.Surjective q ∧
        (∀ g : P, (θP g : rationalPoints (baseChanged F (inertiaFixedField F) G)) =
          c * rationalConjugate F (inertiaFixedField F) G σ g * c⁻¹) ∧
        (∀ g : P, q (θP g) =
          descentBasePoint (algebraBaseMap κ Ω)
            (galoisBaseMap κ Ω (FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω))
            (galoisBaseMap_over κ Ω (FiniteField.frobeniusAlgEquivOfAlgebraic κ Ω))
            R (q g)) ∧
        (∀ Y : Set B.ReducedBuilding, B.HasChamberClosurePresentation Y y →
          ∀ g : P, q g = 1 →
            ((g : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y = Y) ∧
        (∀ Y Y' : Set B.ReducedBuilding, B.HasChamberClosurePresentation Y y →
          B.HasChamberClosurePresentation Y' y →
          ∃ h : P, Y' = ((h : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y)) :
    B.HasFiniteFieldChamberQuotient κ Ω
      (fun g => c * rationalConjugate F (inertiaFixedField F) G σ g * c⁻¹)
      (fun z => c • A.action σ z) y := by
  obtain ⟨R, hR, P, q, θP, hP, hq, hθ, hcompat, hker, htrans⟩ := hres
  obtain ⟨Y₀, hY₀⟩ := B.exists_chamberClosurePresentation y
  obtain ⟨h, hh⟩ := htrans Y₀ _ hY₀
    (hasChamberClosurePresentation_semilinear A σ c hroots hfacet hclosure hY₀ hy)
  exact ⟨R, hR, P, q, θP, Y₀, h, hP, hq, hθ, hcompat, hY₀, hker Y₀ hY₀, hh⟩

section SemilinearPresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)

set_option maxHeartbeats 1600000 in
/-- On the building datum of a Galois-stable class, precomposing an affine root
with the coefficient action of `σ` gives an affine root again. -/
theorem semilinearData_affineRoot_comp (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    ∀ ψ ∈ (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).affineRoots,
      ∃ ψ' ∈ (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).affineRoots,
        ∀ z, ψ ((UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).apartment σ z) =
          ψ' z :=
  KPApartmentData.exists_affineRoot_comp_galoisAction F (inertiaFixedField F) iT D hD σ

set_option maxHeartbeats 1600000 in
/-- On the building datum of a Galois-stable class, the coefficient action of
`σ` carries the facet through `x` onto the facet through its image. -/
theorem semilinearData_image_facet (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).Apartment) :
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).apartment σ ''
        AffineRootSystem.facet
          (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).affineRoots x =
      AffineRootSystem.facet
        (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).affineRoots
        ((UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).apartment σ x) :=
  KPApartmentData.image_facet_galois F (inertiaFixedField F) iT D hD σ x

set_option maxHeartbeats 1600000 in
/-- On the building datum of a Galois-stable class, the coefficient action of
`σ` carries the facet closure through `x` onto the facet closure through its
image. -/
theorem semilinearData_image_facetClosure
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).Apartment) :
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).apartment σ ''
        AffineRootSystem.facetClosure
          (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).affineRoots x =
      AffineRootSystem.facetClosure
        (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6).affineRoots
        ((UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).apartment σ x) :=
  KPApartmentData.image_facetClosure_galois F (inertiaFixedField F) iT D hD σ x

end SemilinearPresentation

set_option maxHeartbeats 1600000 in
/-- The residue quotient for the Frobenius lift built from the actual residue
Galois map, together with transitivity on incident chambers, supplies the
chamber quotient input. -/
theorem unramifiedTwistedChamberQuotient_of_residueQuotient
    (hres : UnramifiedTwistedResidueQuotientStatement.{u}) :
    UnramifiedTwistedChamberQuotientStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let := mono_of_isMaximalSplitTorus hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hfin y hy
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  obtain ⟨φ, hdense, hφ⟩ := exists_fixedField_arithmeticFrobenius F
  have hGK := connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  exact ⟨φ, hdense, hasFiniteFieldChamberQuotient_semilinear
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD) _ _ φ (c φ)
    (semilinearData_affineRoot_comp iT hGK hiT C h6 hD φ)
    (semilinearData_image_facet iT hGK hiT C h6 hD φ)
    (semilinearData_image_facetClosure iT hGK hiT C h6 hD φ) (hy φ)
    (hres F G hG T iT hiT D C h6 hD c hc hfin y hy φ hφ)⟩

/-- The conditional reduction is proved at every universe. -/
theorem unramifiedTwistedChamberQuotientResidueReduction :
    UnramifiedTwistedChamberQuotientResidueReductionStatement.{u} :=
  unramifiedTwistedChamberQuotient_of_residueQuotient

end Langlands.Geometry.Building
