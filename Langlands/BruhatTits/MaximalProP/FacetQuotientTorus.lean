import Langlands.BruhatTits.MaximalProP.FacetReductiveComparisonStatement
import Langlands.Geometry.Building.BuildingChamberIncidence
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.TorusModelPowerIntegrality
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof

/-! # Chamber quotients are tori on supplied KP data -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme

/-- A quasi-split group with no roots for one maximal split torus is a torus. -/
theorem IsQuasiSplit.isTorus_of_maximalSplitTorus_roots_eq_empty
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsQuasiSplit G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (ha : IsMaximalSplitTorus a)
    (hroot : (haveI := hG.isConnectedReductive.isAffineHom; roots a = ∅)) :
    IsTorus G := by
  let := hG.isConnectedReductive.isAffineHom
  let := hG.isConnectedReductive.smooth
  let := hG.isConnectedReductive.connectedSpace
  have hcentral := isCentral_of_roots_eq_empty ha.1.1 a hroot
  obtain ⟨A₀, a₀, C, c, ha₀, hc, _, hC⟩ :=
    quasiSplitTorusCentralizerExistence k G hG
  obtain ⟨g, e, he⟩ :=
    (maximalSplitTorusConjugacy k G hG.isConnectedReductive).1 A₀ A a₀ a ha₀ ha
  have hc' := hc.torusCentralizer_of_iso_square e (G.innerIso g) he
  rw [(isCentral_iff_torusCentralizer_eq_top a).mp hcentral] at hc'
  exact IsTorus.of_iso hc'.topIso.symm hC

end Langlands.GroupScheme

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

/-- A facet has no derivative roots precisely when it is a chamber. -/
theorem facetDerivativeRoots_eq_empty_iff_isChamber
    (hD : D.SatisfiesGroupAxioms) {Fa : Set D.base.Apartment}
    (hFa : AffineRootSystem.IsFacet D.base.affineRoots Fa) :
    facetDerivativeRoots D.base.toValuationBuildingData Fa = ∅ ↔
      AffineRootSystem.IsChamber D.base.affineRoots Fa := by
  constructor
  · intro hempty
    obtain ⟨x, rfl⟩ := hFa
    refine ⟨x, ?_, rfl⟩
    intro ψ hψ hzero
    have hlin : ψ.linear ∈ AffineRootSystem.derivativeRoots D.base.affineRoots :=
      ⟨ψ, hψ, rfl⟩
    rw [hD.affineRootSystem.apartmentAxioms.derivativeRoots_affineRoots] at hlin
    obtain ⟨a, ha⟩ := hlin
    have hmem : a.val ∈
        facetDerivativeRoots D.base.toValuationBuildingData
          (AffineRootSystem.facet D.base.affineRoots x) := by
      refine ⟨a.property, ψ, hψ, ha.symm, ?_⟩
      intro y hy
      exact sign_eq_zero_iff.mp ((hy ψ hψ).symm.trans (sign_eq_zero_iff.mpr hzero))
    rw [hempty] at hmem
    exact hmem
  · rintro ⟨x, hx, rfl⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro a ⟨_, ψ, hψ, _, hzero⟩
    exact hx ψ hψ (hzero x (AffineRootSystem.mem_facet_self _ _))

/-- The actual reductive quotient of a facet is a torus precisely for chambers. -/
theorem facetQuotient_isTorus_iff_isChamber
    (hD : D.SatisfiesGroupAxioms)
    (Fc : BuildingFacet D.base.toValuationBuildingData) :
    IsTorus (D.quotients.quotient Fc).quotient ↔ D.base.IsChamber Fc.val := by
  obtain ⟨g, Fa, hFa, hFc⟩ := Fc.property
  change Fc.val = D.base.translatedApartmentMap g '' Fa at hFc
  have hface : AffineRootSystem.IsFaceOf D.base.affineRoots Fa Fa := by
    obtain ⟨x, rfl⟩ := hFa
    exact ⟨⟨x, rfl⟩, x, rfl, AffineRootSystem.facet_subset_facetClosure _ _⟩
  let Q := D.quotients.quotient Fc
  let T : IntegralTorusData (D.models.facetModels.model Fc) D.base.S
      (D.base.i ≫ (G.innerIso g).hom) :=
    D.models.torus (BuildingModelIndex.ofFacet Fc) g Fa hFc
  let φ := D.models.facetModels.morphism Fc Fc (facetPrecedes_refl _ Fc)
  have hT := hD.reductiveQuotients.facets.common_tori Fc Fc
    (facetPrecedes_refl _ Fc) g Fa Fa hface hFc hFc
  have hmap : φ.neutralSpecialFibreMap = 𝟙 _ := by
    let e : (D.models.facetModels.model Fc).neutral.Hom
        (D.models.facetModels.model Fc).neutral (𝟙 G) :=
      { hom := 𝟙 _
        generic_comm := by simp }
    have he := φ.neutral.hom_eq e
    change (baseChange (IntegralModel.residueBaseMap ↥𝒪[F])).map φ.neutral.hom = _
    rw [he]
    exact CategoryTheory.Functor.map_id _ _
  have hmax : IsMaximalSplitTorus (T.specialFibreInclusion ≫ Q.projection) := by
    have hm := hT.2.2.2
    change IsMaximalSplitTorus
      ((T.specialFibreInclusion ≫ φ.neutralSpecialFibreMap) ≫ Q.projection) at hm
    simpa only [hmap, Category.comp_id] using hm
  obtain ⟨J, hJ, P, hP, hgraph⟩ :=
    hD.reductiveQuotients.facets.derivative_root_data Fc g Fa hFa hFc hT.1.1
  change IsRootDatumOf (T.specialFibreInclusion ≫ Q.projection) P at hP
  have hroots :
      roots (T.specialFibreInclusion ≫ Q.projection) = ∅ ↔
        facetDerivativeRoots D.base.toValuationBuildingData Fa = ∅ := by
    constructor
    · intro hempty
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hpair :
          (T.characterSpecialization hT.1.1 a,
            T.cocharacterSpecialization hT.1.1 (D.rootDatum.coroot ⟨a, ha.1⟩)) ∈
              Set.range (fun j => (P.root j, P.coroot j)) := by
        rw [hgraph]
        exact ⟨⟨a, ha.1⟩, ha, rfl⟩
      obtain ⟨j, _⟩ := hpair
      have hj : P.root j ∈ roots (T.specialFibreInclusion ≫ Q.projection) := by
        rw [← hP.2.1]
        exact Set.mem_range_self j
      rw [hempty] at hj
      exact hj
    · intro hempty
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro χ hχ
      rw [← hP.2.1] at hχ
      obtain ⟨j, rfl⟩ := hχ
      have hpair : (P.root j, P.coroot j) ∈
          apartmentDerivativeRootCorootGraph D.base.toValuationBuildingData
            T D.rootDatum hT.1.1 Fa := by
        rw [← hgraph]
        exact Set.mem_range_self j
      obtain ⟨a, ha, _⟩ := hpair
      rw [hempty] at ha
      exact ha
  have hQ := (hD.reductiveQuotients.facets.reductive_quotients Fc).2.2
  have hquasi := finiteFieldQuasiSplit 𝓀[F] Q.quotient hQ
  rw [hFc, D.base.isChamber_translatedApartmentMap_image_iff
    hD.affineRootSystem.apartmentAxioms g hFa,
    ← facetDerivativeRoots_eq_empty_iff_isChamber hD hFa, ← hroots]
  constructor
  · intro htorus
    let := htorus.isCommMonObj
    let := hQ.smooth
    exact roots_eq_empty_of_isCommMonObj hmax.1.1 _
  · exact hquasi.isTorus_of_maximalSplitTorus_roots_eq_empty hmax

/-- The quotient of a chamber, with the commutative group structure implied by
the supplied KP axioms. Its underlying group scheme is the supplied quotient. -/
def chamberQuotientCommGroupScheme
    (hD : D.SatisfiesGroupAxioms)
    (Fc : BuildingFacet D.base.toValuationBuildingData)
    (hFc : D.base.IsChamber Fc.val) :
    CommGroupScheme (Spec (CommRingCat.of 𝓀[F])) :=
  { toGrp := (D.quotients.quotient Fc).quotient
    comm := ((facetQuotient_isTorus_iff_isChamber hD Fc).mpr hFc).isCommMonObj }

end Langlands.BruhatTits.MaximalProP
