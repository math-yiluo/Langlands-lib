import Langlands.Group.TitsApartmentGalleries
import Langlands.Geometry.Building.TitsRealizationApartmentPanels
import Langlands.Geometry.Building.TitsCommonFacetApartment

/-! # Realized gallery steps and apartment chamber connectivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem Langlands.Group.RelativeWeyl
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

namespace IsBuildingTitsSystem

variable (hT : P.IsBuildingTitsSystem Ca π Sgen)
  (R : P.toValuationBuildingData.PolysimplicialRealization)

/-- The realized facet corresponding to an admissible subgroup. -/
def realizationAdmissibleFacet (Q : Subgroup P.zeroSubgroup)
    (hQ : IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q) :
    R.complex.facets :=
  R.realize.symm (hT.exists_facetZeroStabilizer_eq hQ).choose

@[simp] theorem realizationAdmissibleFacet_stabilizer (Q : Subgroup P.zeroSubgroup)
    (hQ : IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q) :
    P.facetZeroStabilizer (R.realize (hT.realizationAdmissibleFacet R Q hQ)) = Q := by
  simpa only [realizationAdmissibleFacet, Equiv.apply_symm_apply] using
    (hT.exists_facetZeroStabilizer_eq hQ).choose_spec

theorem realizationAdmissibleFacet_eq (Q : Subgroup P.zeroSubgroup)
    (hQ : IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q)
    (Fc : R.complex.facets) (hFc : P.facetZeroStabilizer (R.realize Fc) = Q) :
    hT.realizationAdmissibleFacet R Q hQ = Fc := by
  apply R.realize.injective
  apply hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
  exact (hT.realizationAdmissibleFacet_stabilizer R Q hQ).trans hFc.symm

/-- The actual realized facet whose stabilizer is a given conjugate Borel. -/
def realizationBorelFacet (g : P.zeroSubgroup) : R.complex.facets :=
  hT.realizationAdmissibleFacet R
    (conjugateSubgroup g (P.chamberZeroStabilizerIn Ca))
    (hT.isTitsSystem.isAdmissibleParabolic_conjugate_borel g)

@[simp] theorem realizationBorelFacet_stabilizer (g : P.zeroSubgroup) :
    P.facetZeroStabilizer (R.realize (hT.realizationBorelFacet R g)) =
      conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) :=
  hT.realizationAdmissibleFacet_stabilizer R _ _

theorem realizationBorelFacet_eq_of_conjugate_eq (g k : P.zeroSubgroup)
    (h : conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) =
      conjugateSubgroup k (P.chamberZeroStabilizerIn Ca)) :
    hT.realizationBorelFacet R g = hT.realizationBorelFacet R k := by
  apply R.realize.injective
  apply hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
  simpa only [realizationBorelFacet_stabilizer] using h

variable (hR : R.IsFaceCompatible)
include hT hR

/-- A cover in the reversed stabilizer order gives a codimension-one face. -/
theorem realization_isCodimOneFace_of_admissible_cover
    {Fa Fc : R.complex.facets}
    (hcov : IsAdmissibleParabolicCover (P.chamberZeroStabilizerIn Ca) π Sgen
      (P.facetZeroStabilizer (R.realize Fc))
      (P.facetZeroStabilizer (R.realize Fa))) :
    AbstractBuilding.IsCodimOneFace R.complex.facets Fa.val Fc.val := by
  have hsub : Fa.val ⊆ Fc.val :=
    (hR Fa Fc).mpr ((hT.facetPrecedes_iff _ _).mpr hcov.2.1.le)
  refine ⟨Fa.property, Fc.property, ⟨hsub, ?_⟩, ?_⟩
  · intro hback
    exact hcov.2.1.not_ge ((hT.facetPrecedes_iff _ _).mp ((hR Fc Fa).mp hback))
  · intro D hD hAD hDC
    let Fd : R.complex.facets := ⟨D, hD⟩
    have hCD : P.facetZeroStabilizer (R.realize Fc) <
        P.facetZeroStabilizer (R.realize Fd) := by
      refine ⟨(hT.facetPrecedes_iff _ _).mp ((hR Fd Fc).mp hDC.subset), ?_⟩
      intro hle
      exact hDC.not_superset ((hR Fc Fd).mpr ((hT.facetPrecedes_iff _ _).mpr hle))
    have hDA : P.facetZeroStabilizer (R.realize Fd) ≤
        P.facetZeroStabilizer (R.realize Fa) :=
      (hT.facetPrecedes_iff _ _).mp ((hR Fa Fd).mp hAD.subset)
    have heq := hcov.2.2
      (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ (R.realize Fd))) hCD hDA
    have hsame : Fd = Fa := R.realize.injective
      (hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _) heq)
    exact hAD.not_superset (congrArg Subtype.val hsame).subset

/-- Algebraic apartment incidence gives the actual meet and panel conditions. -/
theorem realization_isGalleryStep_of_borelStep
    {a : P.zeroSubgroup} {Fc Fd : R.complex.facets}
    (hstep : IsApartmentBorelStep (P.chamberZeroStabilizerIn Ca) π Sgen a
      (P.facetZeroStabilizer (R.realize Fc))
      (P.facetZeroStabilizer (R.realize Fd))) :
    AbstractBuilding.IsGalleryStep R.complex.facets Fc.val Fd.val := by
  obtain ⟨Q, _, hcovC, hcovD, hleast⟩ := hstep
  let Fa := hT.realizationAdmissibleFacet R Q hcovC.1
  have hFa : P.facetZeroStabilizer (R.realize Fa) = Q :=
    hT.realizationAdmissibleFacet_stabilizer R Q hcovC.1
  have hAC : AbstractBuilding.IsCodimOneFace R.complex.facets Fa.val Fc.val := by
    apply hT.realization_isCodimOneFace_of_admissible_cover R hR
    rwa [hFa]
  have hAD : AbstractBuilding.IsCodimOneFace R.complex.facets Fa.val Fd.val := by
    apply hT.realization_isCodimOneFace_of_admissible_cover R hR
    rwa [hFa]
  refine ⟨Fa.val, ⟨⟨Fa.property, hAC.ssubset.subset, hAD.ssubset.subset⟩, ?_⟩,
    hAC, hAD⟩
  rintro E ⟨hE, hEC, hED⟩
  let Fe : R.complex.facets := ⟨E, hE⟩
  apply (hR Fe Fa).mpr
  apply (hT.facetPrecedes_iff _ _).mpr
  rw [hFa]
  exact hleast (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ (R.realize Fe)))
    ((hT.facetPrecedes_iff _ _).mp ((hR Fe Fc).mp hEC))
    ((hT.facetPrecedes_iff _ _).mp ((hR Fe Fd).mp hED))

/-- The same algebraic panel gives a gallery step inside the specified actual apartment. -/
theorem realization_isGalleryStep_apartment_of_borelStep
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    {a : P.zeroSubgroup}
    {Fc Fd : R.complex.facets}
    (hFcY : Fc.val ∈ R.apartmentComplex Y) (hFdY : Fd.val ∈ R.apartmentComplex Y)
    (hstep : IsApartmentBorelStep (P.chamberZeroStabilizerIn Ca) π Sgen a
      (P.facetZeroStabilizer (R.realize Fc))
      (P.facetZeroStabilizer (R.realize Fd))) :
    AbstractBuilding.IsGalleryStep (R.apartmentComplex Y) Fc.val Fd.val := by
  obtain ⟨A, hgreat, hAC, hAD⟩ :=
    hT.realization_isGalleryStep_of_borelStep R hR hstep
  have hsub := hT.realization_isSubcomplex_apartmentComplex R hR hY
  have hAY : A ∈ R.apartmentComplex Y := hsub.2 Fc.val hFcY A hAC.1 hAC.ssubset.subset
  refine ⟨A, ⟨⟨hAY, hgreat.1.2⟩, ?_⟩,
    ⟨hAY, hFcY, hAC.ssubset, ?_⟩, ⟨hAY, hFdY, hAD.ssubset, ?_⟩⟩
  · rintro E ⟨hE, hEC, hED⟩
    exact hgreat.2 ⟨hsub.1 hE, hEC, hED⟩
  · intro D hD
    exact hAC.2.2.2 D (hsub.1 hD)
  · intro D hD
    exact hAD.2.2.2 D (hsub.1 hD)

omit hR in
/-- The chosen normalizer Borel chamber belongs to its actual apartment. -/
theorem realizationBorelFacet_mem_apartmentComplex
    {Y : Set P.ReducedBuilding} (a : P.zeroSubgroup)
    (ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
      P.facetStabilizersIn Y) (m : P.normalizerInZero) :
    (hT.realizationBorelFacet R (a * m)).val ∈ R.apartmentComplex Y := by
  have hmem : conjugateSubgroup (a * m) (P.chamberZeroStabilizerIn Ca) ∈
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a :=
    (hT.isTitsSystem.mem_restrictedApartment_iff_conjugate).mpr
      ⟨m, ∅, isAdmissibleType_empty Sgen, by
        rw [show hT.isTitsSystem.standardParabolicSubgroup (Set.empty_subset Sgen) =
          P.chamberZeroStabilizerIn Ca from
            SetLike.coe_injective hT.isTitsSystem.standardParabolic_empty]⟩
  rw [ha] at hmem
  obtain ⟨Fc, hFcY, hFc⟩ := hmem
  have hsame : R.realize (hT.realizationBorelFacet R (a * m)) = Fc :=
    hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
      ((hT.realizationBorelFacet_stabilizer R (a * m)).trans hFc.symm)
  refine ⟨(hT.realizationBorelFacet R (a * m)).property, ?_⟩
  change (R.realize (hT.realizationBorelFacet R (a * m))).val ⊆ Y
  rwa [hsame]

/-- Simple normalizer lifts give adjacent realized chambers in the same apartment. -/
theorem realization_isGalleryStep_simple
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (a : P.zeroSubgroup)
    (ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
      P.facetStabilizersIn Y)
    {s : W} (hs : s ∈ Sgen) (hadm : IsAdmissibleType Sgen {s})
    (m n : P.normalizerInZero) (hn : π n = s) :
    AbstractBuilding.IsGalleryStep (R.apartmentComplex Y)
      (hT.realizationBorelFacet R (a * m)).val
      (hT.realizationBorelFacet R (a * (m * n))).val := by
  apply hT.realization_isGalleryStep_apartment_of_borelStep R hR hY
    (hT.realizationBorelFacet_mem_apartmentComplex R a ha m)
    (hT.realizationBorelFacet_mem_apartmentComplex R a ha (m * n))
  simpa only [realizationBorelFacet_stabilizer, Subgroup.coe_mul] using
    hT.isTitsSystem.isApartmentBorelStep_simple hs hadm a m n hn

/-- Simple-word induction gives a gallery between chosen normalizer Borel facets. -/
theorem realization_reflTransGen_borelFacets
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s})
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (a : P.zeroSubgroup)
    (ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
      P.facetStabilizersIn Y) (m n : P.normalizerInZero) :
    Relation.ReflTransGen (AbstractBuilding.IsGalleryStep (R.apartmentComplex Y))
      (hT.realizationBorelFacet R (a * m)).val
      (hT.realizationBorelFacet R (a * n)).val := by
  have hword : ∀ (l : List W), (∀ s ∈ l, s ∈ Sgen) →
      ∀ (m n : P.normalizerInZero), π n = l.prod →
        Relation.ReflTransGen (AbstractBuilding.IsGalleryStep (R.apartmentComplex Y))
          (hT.realizationBorelFacet R (a * m)).val
          (hT.realizationBorelFacet R (a * (m * n))).val := by
    intro l hl
    induction l with
    | nil =>
      intro m n hn
      have hnB : (n : P.zeroSubgroup) ∈ P.chamberZeroStabilizerIn Ca :=
        (hT.isTitsSystem.mem_iff n).mpr (by simpa using hn)
      have heq : hT.realizationBorelFacet R (a * (m * n)) =
          hT.realizationBorelFacet R (a * m) := by
        apply hT.realizationBorelFacet_eq_of_conjugate_eq R
        rw [← mul_assoc, conjugateSubgroup_mul, conjugateSubgroup_eq_self hnB]
      rw [heq]
    | cons s l ih =>
      intro m n hn
      have hs : s ∈ Sgen := hl s (by simp)
      obtain ⟨ns, hns⟩ := hT.isTitsSystem.surjective s
      have hn' : π (ns⁻¹ * n) = l.prod := by
        simp only [List.prod_cons] at hn
        simp [map_mul, map_inv, hns, hn]
      have htail := ih (fun t ht => hl t (by simp [ht])) (m * ns) (ns⁻¹ * n) hn'
      have hstep := hT.realization_isGalleryStep_simple R hR hY a ha
        hs (hadm s hs) m ns hns
      have H := Relation.ReflTransGen.head hstep htail
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using H
  obtain ⟨l, hl, heq⟩ := exists_word_of_mem_closure hT.isTitsSystem.mul_self
    (hT.isTitsSystem.closure_eq ▸ Subgroup.mem_top (π (m⁻¹ * n)))
  have H := hword l hl m (m⁻¹ * n) heq.symm
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using H

/-- Every chamber of an actual apartment is one of its normalizer Borel facets. -/
theorem exists_realizationBorelFacet_eq_of_apartment_chamber
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (a : P.zeroSubgroup)
    (ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
      P.facetStabilizersIn Y) (Fc : R.complex.facets)
    (hFc : AbstractBuilding.IsChamber (R.apartmentComplex Y) Fc.val) :
    ∃ n : P.normalizerInZero, hT.realizationBorelFacet R (a * n) = Fc := by
  have hFc' := (hT.realization_isChamber_apartmentComplex_iff R hR hY Fc.val).mp hFc
  have hmem : P.facetZeroStabilizer (R.realize Fc) ∈
      apartmentBorelsBelow (P.chamberZeroStabilizerIn Ca) P.normalizerInZero a
        (P.facetZeroStabilizer (R.realize Fc)) := by
    rw [hT.isTitsSystem.apartmentBorelsBelow_eq_inter]
    refine ⟨⟨(hT.realization_isChamber_iff_stabilizer R hR Fc).mp hFc'.1,
      le_rfl⟩, ?_⟩
    rw [ha]
    exact ⟨R.realize Fc, hFc'.2.choose_spec, rfl⟩
  obtain ⟨⟨n, hn⟩, _⟩ := hmem
  exact ⟨n, hT.realizationAdmissibleFacet_eq R _ _ Fc hn⟩

/-- The gallery-connectivity clause of a chamber complex in every actual apartment. -/
theorem realization_reflTransGen_apartment
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s})
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) :
    ∀ C D, AbstractBuilding.IsChamber (R.apartmentComplex Y) C →
      AbstractBuilding.IsChamber (R.apartmentComplex Y) D →
        Relation.ReflTransGen (AbstractBuilding.IsGalleryStep (R.apartmentComplex Y)) C D := by
  intro C D hC hD
  let Fc : R.complex.facets := ⟨C, hC.1.choose⟩
  let Fd : R.complex.facets := ⟨D, hD.1.choose⟩
  obtain ⟨a, ha⟩ := hT.exists_restrictedApartment_eq hY
  obtain ⟨m, hm⟩ :=
    hT.exists_realizationBorelFacet_eq_of_apartment_chamber R hR hY a ha Fc hC
  obtain ⟨n, hn⟩ :=
    hT.exists_realizationBorelFacet_eq_of_apartment_chamber R hR hY a ha Fd hD
  have H := hT.realization_reflTransGen_borelFacets R hR hadm hY a ha m n
  simpa only [hm, hn] using H

/-- A gallery step inside an apartment is also a step in the full realized complex. -/
theorem realization_isGalleryStep_of_apartment
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    {C D : Set (∀ i, R.V i)}
    (hstep : AbstractBuilding.IsGalleryStep (R.apartmentComplex Y) C D) :
    AbstractBuilding.IsGalleryStep R.complex.facets C D := by
  obtain ⟨A, hgreat, hAC, hAD⟩ := hstep
  have hsub := hT.realization_isSubcomplex_apartmentComplex R hR hY
  refine ⟨A, ⟨⟨hsub.1 hgreat.1.1, hgreat.1.2⟩, ?_⟩,
    hT.realization_isCodimOneFace_of_apartment R hR hY hAC,
    hT.realization_isCodimOneFace_of_apartment R hR hY hAD⟩
  rintro E ⟨hE, hEC, hED⟩
  exact hgreat.2 ⟨hsub.2 C hAC.2.1 E hE hEC, hEC, hED⟩

/-- Gallery connectivity in the full realized complex, via common apartments. -/
theorem realization_reflTransGen
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s}) :
    ∀ C D, AbstractBuilding.IsChamber R.complex.facets C →
      AbstractBuilding.IsChamber R.complex.facets D →
        Relation.ReflTransGen (AbstractBuilding.IsGalleryStep R.complex.facets) C D := by
  intro C D hC hD
  obtain ⟨Y, hY, hCY, hDY⟩ :=
    hT.exists_apartment_contains_facets (R.realize ⟨C, hC.1⟩) (R.realize ⟨D, hD.1⟩)
  have H := hT.realization_reflTransGen_apartment R hR hadm hY C D
    ((hT.realization_isChamber_apartmentComplex_iff R hR hY C).mpr ⟨hC, hC.1, hCY⟩)
    ((hT.realization_isChamber_apartmentComplex_iff R hR hY D).mpr ⟨hD, hD.1, hDY⟩)
  exact Relation.ReflTransGen.mono
    (fun _ _ hstep => hT.realization_isGalleryStep_of_apartment R hR hY hstep) C D H

/-- A face-compatible realization is a chamber complex under singleton admissibility. -/
theorem realization_isChamberComplex
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s}) :
    AbstractBuilding.IsChamberComplex R.complex.facets := by
  refine ⟨⟨R.index, inferInstance, R.V, R.complex, ⟨OrderIso.refl _⟩⟩,
    hT.realization_exists_chamber R hR, hT.realization_reflTransGen R hR hadm⟩

/-- The remaining apartment chamber-complex premise is its polysimplicial structure. -/
theorem realization_isChamberComplex_apartment
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s})
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (hpoly : AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y)) :
    AbstractBuilding.IsChamberComplex (R.apartmentComplex Y) := by
  refine ⟨hpoly, ?_, hT.realization_reflTransGen_apartment R hR hadm hY⟩
  intro A hA
  obtain ⟨C, hC, hCY, hAC⟩ := hT.realization_exists_apartment_chamber R hR hY A hA
  exact ⟨C, (hT.realization_isChamber_apartmentComplex_iff R hR hY C).mpr ⟨hC, hCY⟩,
    hAC⟩

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
