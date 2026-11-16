import Langlands.BruhatTits.IntegralModels.UnramifiedResidueCocharacterAttainment
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusClause
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Downstairs split integral tori and fixed-torus parabolic attainment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme

/-- A rational parabolic containing a prescribed maximal split torus is the
parabolic of a cocharacter of that same torus. -/
theorem IsParabolicSubgroup.exists_cocharacter_of_maximalSplitTorus
    {k : Type u} [Field k]
    {H P : GroupScheme (Spec (CommRingCat.of k))}
    (hH : IsConnectedReductive H)
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (iS : S.toGrp ⟶ H) (hiS : IsMaximalSplitTorus iS)
    (j : P ⟶ H) (hj : IsParabolicSubgroup j)
    (f : S.toGrp ⟶ P) (hf : f ≫ j = iS) :
    ∃ ν : cocharacterLattice S,
      SubgroupFunctor.range j = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ iS) := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : ConnectedSpace H.X.left := hH.connectedSpace
  let : Smooth P.X.hom := hj.smooth
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : ConnectedSpace P.X.left := hj.connectedSpace
  have hmax : IsMaximalSplitTorus f :=
    IsMaximalSplitTorus.of_comp hj.isClosedSubgroup (hf.symm ▸ hiS)
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k H hH P j hj.isClosedSubgroup).mp hj
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, hχ⟩
  let χP := hrep.factorHom χ (Dynamic.range_le_parabolic χ)
  have hχP : χP ≫ j = χ := hrep.factorHom_comp _ _
  obtain ⟨p, ν, hν⟩ := exists_innerIso_comp_eq_cocharacter
    smoothMaximalSplitTorusConjugacy hmax χP
  let g := p ≫ j.hom.hom
  have hg : g ∈ (Dynamic.parabolic χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [← hχ]
    exact ⟨p, rfl⟩
  have hνG : χ ≫ (H.innerIso g).hom = CommGroupScheme.groupHom ν ≫ iS := by
    rw [← hχP, Category.assoc, comp_innerIso_hom_comp,
      ← Category.assoc, hν, Category.assoc, hf]
  have h1 := Dynamic.parabolic_eq_comap_of_iso χ (H.innerIso g)
  rw [hνG] at h1
  have h2 := (SubgroupFunctor.eq_comap_iso_iff (H.innerIso g)).1 h1
  rw [← innerIso_inv_hom,
    SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ (Subgroup.inv_mem _ hg)] at h2
  exact ⟨ν, hχ.trans h2⟩

end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

/-- The actual special-fibre torus remains maximal split in the reductive
quotient over a perfect residue field. -/
theorem isMaximalSplitTorus_quotient
    {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [PerfectField (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (hT : T.HasMaximalSplitSpecialFibre) :
    IsMaximalSplitTorus (T.specialFibreInclusion ≫ Q.projection) := by
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom D.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  let : LocallyOfFiniteType D.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
        (IntegralModel.residueBaseMap R))
    infer_instance
  exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
    Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.isUnipotent
    Q.projection hQ.2.1 T.specialFibreInclusion).mpr hT

end Langlands.BruhatTits.IntegralModels.IntegralTorusData

namespace Langlands.BruhatTits.IntegralModels.FacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ z : B.ReducedBuilding, B.HasCommonApartmentWith z)
  (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)
  (M : FacetModelData B ↥𝒪[F])
  (hmodel : ∀ Fc : BuildingFacet B,
    (M.model Fc).neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))

private instance descendedAttainment_affine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

local instance : Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  unramifiedResidue_isSeparable

include hD hcommon hequiv hap hfac hmodel in
/-- The actual supplied model at an apartment point admits the complete
integral split torus clause from bounded-torus fixedness. -/
theorem exists_integralTorus_at_apartmentPoint
    (hfixed : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) B.S.toGrp),
      ∀ w : B.Apartment,
        rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
          e (B.apartmentMap w) = e (B.apartmentMap w))
    (x : B.Apartment) :
    ∃ T : IntegralTorusData (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S B.i,
      T.SatisfiesTorusClause := by
  have hfix : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) B.S.toGrp),
      ∀ y ∈ ({a x} : Set C.Apartment),
        rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
          C.apartmentMap y = C.apartmentMap y := by
    intro s hs y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    simpa only [hap] using hfixed s hs x
  have hchar := M.unramified_apartmentPointCharacterization
    B C E e a hD hcommon hequiv hap hfac hmodel x
  change (M.model (B.buildingFacetAt (B.apartmentMap x))).neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {a x}) at hchar
  have hchar' : (M.model (B.buildingFacetAt (B.apartmentMap x))).neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        ((fun y => rationalExtend F (inertiaFixedField F) G 1 • C.apartmentMap y) '' {a x}) := by
    simpa only [map_one, one_smul] using hchar
  have htorus := unramifiedTorusClause F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus C E {a x} (Set.singleton_nonempty _)
    (by intro l; simpa only [Set.image_singleton] using
      (show BddAbove ({l (a x)} : Set ℝ) from bddAbove_singleton)) hfix 1
    (M.model (B.buildingFacetAt (B.apartmentMap x))) hchar'
  change ∃ T : IntegralTorusData
      (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S
      (B.i ≫ (G.innerIso 1).hom), T.SatisfiesTorusClause at htorus
  rw [innerIso_one_hom, Category.comp_id] at htorus
  exact htorus

include hD hcommon hequiv hap hfac hmodel in
/-- Every residue parabolic containing the actual apartment torus is attained
by the supplied morphism from an incident downstairs facet. -/
theorem exists_incidentFacet_quotientImage_eq_parabolic_of_torus
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i =
      (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (x : B.Apartment)
    (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x))))
    (hQ : Q.IsReductiveQuotient)
    (T : IntegralTorusData (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S B.i)
    (hT : T.SatisfiesTorusClause)
    (P : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
    (j : P ⟶ Q.quotient) (hj : IsParabolicSubgroup j)
    (t : T.specialFibre.toGrp ⟶ P)
    (ht : t ≫ j = T.specialFibreInclusion ≫ Q.projection) :
    ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
      SubgroupFunctor.range
        ((M.morphism _ Fd.val Fd.property).reductiveImageInclusion Q) =
          SubgroupFunctor.range j := by
  have hmax := T.isMaximalSplitTorus_quotient Q hQ hT.2
  obtain ⟨ν, hν⟩ := hj.exists_cocharacter_of_maximalSplitTorus hQ.2.2
    (T.specialFibreInclusion ≫ Q.projection) hmax j t ht
  let c := (T.cocharacterSpecialization hT.1.1).symm ν
  obtain ⟨ε, hε, Fd, hFd, himage⟩ :=
    M.exists_incidentFacet_quotientImage_eq_residueCocharacter
      B C E e a hD hcommon hequiv hap hfac hmodel f hf x Q hQ T hT.1.1 c
  refine ⟨Fd, himage.trans ?_⟩
  dsimp only [c] at *
  rw [AddEquiv.apply_symm_apply, Category.assoc]
  exact hν.symm

/-- A constructed integral apartment torus supplies actual facet-model
attainment for every residue parabolic containing its quotient inclusion. -/
def HasResidueFixedTorusQuotientAttainment : Prop :=
  ∀ (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp),
    f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i →
    ∀ (x : B.Apartment)
      (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x)))),
      Q.IsReductiveQuotient →
      ∃ T : IntegralTorusData (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S B.i,
        T.SatisfiesTorusClause ∧
        IsMaximalSplitTorus (T.specialFibreInclusion ≫ Q.projection) ∧
        ∀ (P : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
          (j : P ⟶ Q.quotient), IsParabolicSubgroup j →
          ∀ t : T.specialFibre.toGrp ⟶ P,
            t ≫ j = T.specialFibreInclusion ≫ Q.projection →
            ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
              SubgroupFunctor.range
                ((M.morphism _ Fd.val Fd.property).reductiveImageInclusion Q) =
                  SubgroupFunctor.range j

include hD hcommon hequiv hap hfac hmodel in
theorem hasResidueFixedTorusQuotientAttainment
    (hfixed : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) B.S.toGrp),
      ∀ w : B.Apartment,
        rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
          e (B.apartmentMap w) = e (B.apartmentMap w)) :
    HasResidueFixedTorusQuotientAttainment B C M := by
  intro f hf x Q hQ
  obtain ⟨T, hT⟩ := M.exists_integralTorus_at_apartmentPoint
    B C E e a hD hcommon hequiv hap hfac hmodel hfixed x
  refine ⟨T, hT, T.isMaximalSplitTorus_quotient Q hQ hT.2, ?_⟩
  intro P j hj t ht
  exact M.exists_incidentFacet_quotientImage_eq_parabolic_of_torus
    B C E e a hD hcommon hequiv hap hfac hmodel f hf x Q hQ T hT P j hj t ht

end Langlands.BruhatTits.IntegralModels.FacetModelData
