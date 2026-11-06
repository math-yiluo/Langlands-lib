import Langlands.Geometry.Building.AnisotropicBuildingTits
import Langlands.Geometry.Building.FullValidity.Realization

/-! # The one-group building axiom on actual anisotropic quotient data -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.AbstractBuilding

namespace PolysimplicialComplex

/-- A complex with no factors, whose product vertex set has one element. -/
def emptyFactorComplex : PolysimplicialComplex PEmpty.{u + 1} (fun _ => PUnit.{u + 1}) where
  factor i := PEmpty.elim i

/-- The complex with no factors has exactly one facet. -/
theorem subsingleton_facets_emptyFactorComplex :
    Subsingleton emptyFactorComplex.{u}.facets := by
  refine ⟨fun A B => emptyFactorComplex.facetsOrderIso.injective ?_⟩
  exact Subsingleton.elim _ _

/-- A polysimplicial complex with a unique facet is a building with its full complex
as its sole apartment. -/
theorem isBuilding_of_subsingleton_facets
    {J : Type v} [Finite J] {V : J → Type u} (K : PolysimplicialComplex J V)
    (hK : Subsingleton K.facets) : IsBuilding K {K.facets} := by
  have heq : ∀ A ∈ K.facets, ∀ C ∈ K.facets, A = C := by
    intro A hA C hC
    exact congrArg Subtype.val (hK.elim (⟨A, hA⟩ : K.facets) ⟨C, hC⟩)
  have hch : ∀ A ∈ K.facets, IsChamber K.facets A := by
    intro A hA
    exact ⟨hA, fun C hC _ => (heq C hC A hA).subset⟩
  have hcc : IsChamberComplex K.facets := by
    refine ⟨K.isPolysimplicial_facets, fun A hA => ⟨A, hch A hA, subset_rfl⟩, ?_⟩
    intro C D hC hD
    rw [heq C hC.mem D hD.mem]
  have hno : ∀ F, ¬ IsCodimOneFacet K.facets F := by
    rintro F ⟨C, hC, hFC⟩
    exact hFC.ssubset.ne (heq F hFC.1 C hC.mem)
  refine ⟨⟨hcc, fun F hF => (hno F hF).elim⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ rfl
    exact isSubcomplex_refl _
  · rintro _ rfl
    exact ⟨hcc, fun F hF => (hno F hF).elim⟩
  · intro C D hC hD
    exact ⟨K.facets, Set.mem_singleton _, hC.mem, hD.mem⟩
  · rintro _ rfl _ rfl F₁ _ F₂ _
    exact ⟨OrderIso.refl _, fun _ _ _ => rfl⟩

end PolysimplicialComplex

end Langlands.Geometry.Building.AbstractBuilding

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels AbstractBuilding

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Realize the facets of an actual one-point quotient by the complex with no factors. -/
def emptyFactorRealizationOfSubsingleton (hB : Subsingleton B.ReducedBuilding) :
    B.PolysimplicialRealization where
  index := PEmpty.{u + 1}
  V _ := PUnit.{u + 1}
  complex := PolysimplicialComplex.emptyFactorComplex
  realize :=
    { toFun := fun _ => Classical.choice B.nonempty_buildingFacet
      invFun := fun _ => ⟨{fun i => PEmpty.elim i},
        PolysimplicialComplex.emptyFactorComplex.singleton_mem_facets _⟩
      left_inv := fun _ => PolysimplicialComplex.subsingleton_facets_emptyFactorComplex.elim _ _
      right_inv := fun _ => (B.subsingleton_buildingFacet hB).elim _ _ }

/-- Every apartment complex of a one-point quotient is the whole realized complex. -/
theorem PolysimplicialRealization.apartments_eq_singleton_of_subsingleton
    (R : B.PolysimplicialRealization) (hB : Subsingleton B.ReducedBuilding) :
    R.apartments = {R.complex.facets} := by
  have hA := B.apartmentImage_eq_univ_of_subsingleton hB
  have hY : ∀ Y, B.IsApartment Y → Y = Set.univ := by
    rintro Y ⟨g, rfl⟩
    rw [hA, Set.smul_set_univ]
  have hC : R.apartmentComplex Set.univ = R.complex.facets := by
    ext Fc
    simp [apartmentComplex]
  ext A
  constructor
  · rintro ⟨Y, hY', rfl⟩
    rw [hY Y hY', hC]
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨B.apartmentImage, B.isApartment_apartmentImage, by rw [hA, hC]⟩

/-- The empty-factor realization satisfies the polysimplicial, face and action clauses;
the actual torus correspondence and normalizer stabilizer remain explicit inputs. -/
theorem satisfiesBuildingAxiom_emptyFactorRealizationOfSubsingleton
    (hB : Subsingleton B.ReducedBuilding)
    (hT : B.HasTorusApartmentCorrespondence) (hN : B.HasNormalizerApartmentStabilizer) :
    B.SatisfiesBuildingAxiom (B.emptyFactorRealizationOfSubsingleton hB) := by
  let R := B.emptyFactorRealizationOfSubsingleton hB
  have hK : Subsingleton R.complex.facets :=
    PolysimplicialComplex.subsingleton_facets_emptyFactorComplex
  have hFc := B.subsingleton_buildingFacet hB
  have : Subsingleton (∀ i, R.V i) := by
    dsimp [R, emptyFactorRealizationOfSubsingleton]
    infer_instance
  refine ⟨?_, ?_, ?_, hT, hN⟩
  · intro Fc Fc'
    rw [hK.elim Fc Fc']
    exact iff_of_true (le_refl _) (facetPrecedes_refl _ _)
  · rw [R.apartments_eq_singleton_of_subsingleton B hB]
    exact R.complex.isBuilding_of_subsingleton_facets hK
  · intro g
    let φ : PolysimplicialIso R.complex R.complex :=
      { perm := Equiv.refl _
        factorIso := fun i => PEmpty.elim i }
    refine ⟨φ.vertexEquiv, ⟨φ, rfl⟩, ?_⟩
    intro Fc Fc'
    have he : φ.vertexEquiv = Equiv.refl _ := Subsingleton.elim _ _
    have hg : (fun y : B.ReducedBuilding => g • y) = id :=
      funext fun _ => hB.elim _ _
    constructor
    · intro _
      simpa only [hg, Set.image_id] using
        congrArg Subtype.val (hFc.elim (R.realize Fc') (R.realize Fc))
    · intro _
      rw [he]
      change (Fc' : Set (∀ i, R.V i)) = id '' (Fc : Set (∀ i, R.V i))
      simpa only [Set.image_id] using
        congrArg Subtype.val (hK.elim Fc' Fc)

/-- An actual anisotropic group has the torus/apartment correspondence on supplied data. -/
theorem hasTorusApartmentCorrespondence_of_isAnisotropic (hG : IsAnisotropic G) :
    B.HasTorusApartmentCorrespondence := by
  have hB := B.apartment.subsingleton_reducedBuilding_of_isAnisotropic hG
    B.isMaximalSplitTorus.isSplitSubtorus
  have hA := B.apartmentImage_eq_univ_of_subsingleton hB
  have hHom : ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (j : T.toGrp ⟶ G),
      IsSplitSubtorus j → ∀ H : CommGroupScheme (Spec (CommRingCat.of F)),
      Subsingleton (T ⟶ H) := by
    intro T j hj H
    have := hG.subsingleton_hom_of_isSplitSubtorus hj H.toGrp
    exact ⟨fun f g => congrArg Additive.ofMul (Subsingleton.elim f.toMul g.toMul)⟩
  refine ⟨?_, ?_⟩
  · intro T₂ i₂ hi₂
    let σ : B.S ≅ T₂ :=
      { hom := 0
        inv := 0
        hom_inv_id := (hHom B.S B.i B.isMaximalSplitTorus.isSplitSubtorus B.S).elim _ _
        inv_hom_id := (hHom T₂ i₂ hi₂.isSplitSubtorus T₂).elim _ _ }
    exact ⟨1, σ,
      (hG.subsingleton_hom_of_isSplitSubtorus B.isMaximalSplitTorus.isSplitSubtorus G).elim _ _⟩
  · intro g h
    have ht : B.conjTorus g = B.conjTorus h :=
      congrArg SubgroupFunctor.range
        ((hG.subsingleton_hom_of_isSplitSubtorus B.isMaximalSplitTorus.isSplitSubtorus G).elim
          (B.i ≫ (G.innerIso g).hom) (B.i ≫ (G.innerIso h).hom))
    have ha : g • B.apartmentImage = h • B.apartmentImage := by
      rw [hA, Set.smul_set_univ, Set.smul_set_univ]
    exact iff_of_true ht ha

/-- The polysimplicial realization of supplied actual anisotropic valuation-building data. -/
def anisotropicRealization (hG : IsAnisotropic G) : B.PolysimplicialRealization :=
  B.emptyFactorRealizationOfSubsingleton
    (B.apartment.subsingleton_reducedBuilding_of_isAnisotropic hG
      B.isMaximalSplitTorus.isSplitSubtorus)

/-- All clauses of the existing one-group KP Axiom 4.1.1 hold on the actual anisotropic quotient. -/
theorem satisfiesBuildingAxiom_anisotropicRealization (hG : IsAnisotropic G) :
    B.SatisfiesBuildingAxiom (B.anisotropicRealization hG) :=
  B.satisfiesBuildingAxiom_emptyFactorRealizationOfSubsingleton _
    (B.hasTorusApartmentCorrespondence_of_isAnisotropic hG)
    (B.hasNormalizerApartmentStabilizer_of_relativeRoots_eq_empty
      (hG.relativeRoots_eq_empty B.isMaximalSplitTorus.isSplitSubtorus))

end ValuationBuildingData

end Langlands.Geometry.Building
