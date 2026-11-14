import Langlands.Geometry.Building.UnramifiedDescendedApartmentTorusStatement
import Langlands.Geometry.Building.UnramifiedCentralizerNormOneBoundednessProof
import Langlands.Geometry.Building.UnramifiedZeroRootFiltrationBoundedProof
import Langlands.Geometry.Building.SplitTorusBoundedCommutation
import Langlands.Geometry.Building.RegularUnitExistence
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.GroupScheme.Rational.BoundedConjugation
import Langlands.GroupScheme.Rational.SplitTorusPowerGridBaseChange
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # The descended apartment's split torus factors through the ambient apartment torus -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private theorem centralizer_torus_point
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    (D : CentralizerDatum i) (s : rationalPoints S.toGrp) :
    rationalPoints.map D.j (rationalPoints.map D.s s) = rationalPoints.map i s := by
  change (s ≫ D.s.hom.hom) ≫ D.j.hom.hom = s ≫ i.hom.hom
  rw [Category.assoc]
  exact congrArg (fun f => s ≫ f.hom.hom) D.comp_eq

private theorem torus_preserves_apartment
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G) (s : rationalPoints B.S.toGrp) (w : B.Apartment) :
    ∃ w' : B.Apartment, rationalPoints.map B.i s • B.apartmentMap w =
      B.apartmentMap w' := by
  let z := rationalPoints.map B.centralizer.s s
  refine ⟨B.centralizer.toNormalizer z • w, ?_⟩
  have hn : (B.centralizer.toNormalizer z : rationalPoints G) =
      rationalPoints.map B.i s := centralizer_torus_point B.centralizer s
  rw [← hn]
  exact B.normalizer_smul_apartmentMap _ w

private instance descendedApartmentAffineBaseChange
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The exact descended-apartment torus containment, at arbitrary universe. -/
theorem unramifiedDescendedApartmentTorus :
    UnramifiedDescendedApartmentTorusStatement.{u} := by
  intro F _ _ _ _ G _ P R T hbuilding hopen haff hroot hapt hfacet htits
  intro C A e a hinj hequiv hap hfixed hsurj hspecial hfacets hkernel
  let K := inertiaFixedField F
  let GK := baseChanged F K G
  let v := MaximalUnramified.valuation F
  letI : IsAffine GK.X.left := isAffine_of_isAffineHom GK.X.hom
  letI : Infinite (IsLocalRing.ResidueField v.valuationSubring) :=
    MaximalUnramified.infinite_residueField F
  obtain ⟨I, hI, ⟨q⟩⟩ := P.isMaximalSplitTorus.1.1
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  let j0 : splitTorus (Spec (CommRingCat.of F)) I ⟶ G := q.inv ≫ P.i
  let jK : splitTorus (Spec (CommRingCat.of K)) I ⟶ GK :=
    splitTorus.baseChangeHomAlong I (baseMap F K) j0
  let qK : baseChanged F K P.S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I :=
    (GroupScheme.baseChange (baseMap F K)).mapIso q ≪≫
      splitTorus.baseChangeIso (baseMap F K) I
  have hπ : WithZero.log (v (MaximalUnramified.baseUniformizerUnit F : K)) ≠ 0 := by
    have h := MaximalUnramified.orderUnits_baseUniformizerUnit F
    rw [IntegerValuation.orderUnits_toAdd] at h
    change -WithZero.log (v (MaximalUnramified.baseUniformizerUnit F : K)) = 1 at h
    omega
  obtain ⟨w0⟩ : Nonempty P.toValuationBuildingData.Apartment := inferInstance
  let y := e (P.toValuationBuildingData.apartmentMap w0)
  have hB : letI := ValuativeRel.ofValuation v
      IsAlgebraicallyBounded K GK.X (C.oneStabilizer y : Set (rationalPoints GK)) := by
    have hB0 := MaximalUnramified.oneStabilizerBounded_of_centralizer_of_zeroRootFiltration
      MaximalUnramified.centralizerNormOneBounded
      MaximalUnramified.zeroRootFiltrationBounded F GK C y
    intro r
    obtain ⟨b, hb, h⟩ := hB0 r
    refine ⟨b, hb, fun p hp => ?_⟩
    exact (MaximalUnramified.valuation_isEquiv F _ _).2 (h p hp)
  have hcomm : KernelPointwiseCommute v jK C.i := by
    intro s t ht
    let x := rationalPoints.map C.i t
    have hxkernel : x ∈ characterValuationKernel v GK :=
      IntegerValuation.map_mem_characterValuationKernel v C.i ht
    have hxfix (w : P.toValuationBuildingData.Apartment) :
        x • e (P.toValuationBuildingData.apartmentMap w) =
          e (P.toValuationBuildingData.apartmentMap w) := by
      have htZ := IntegerValuation.map_mem_characterValuationKernel v C.centralizer.s ht
      have hm := C.map_mem_oneStabilizer htZ (a w)
      rw [centralizer_torus_point] at hm
      have hf := (C.mem_oneStabilizer.mp hm).2
      rw [hap]
      exact hf
    let τ := splitTorus.algebraPointsEquiv (R := CommRingCat.of K) I K
      (rationalCoeffEquiv K _ s)
    have hs : BoundedTorusOrbits.tuplePoint I τ = s := by
      simp [BoundedTorusOrbits.tuplePoint, τ]
    rw [← hs]
    apply BoundedTorusOrbits.commute_of_bounded_conjugation_grid I v
      (MaximalUnramified.baseUniformizerUnit F) hπ jK x
      (C.oneStabilizer y : Set (rationalPoints GK)) hB
    intro n
    let p := BoundedTorusOrbits.tuplePoint I
      (BoundedTorusOrbits.powerTuple I (SplitTorusValuation.uniformizerUnit F) n)
    let sF := rationalPoints.map q.inv p
    let g := rationalPoints.map jK (BoundedTorusOrbits.tuplePoint I
      (BoundedTorusOrbits.powerTuple I (MaximalUnramified.baseUniformizerUnit F) n))
    have hg : g = rationalExtend F K G (rationalPoints.map P.i sF) := by
      have h := BoundedTorusOrbits.baseChangeHomAlong_powerTuple
        (L := K) I j0 (SplitTorusValuation.uniformizerUnit F) n
      exact h
    apply C.mem_oneStabilizer.mpr
    refine ⟨(inferInstance : (characterValuationKernel v GK).Normal).conj_mem x hxkernel g, ?_⟩
    obtain ⟨w', hw'⟩ := torus_preserves_apartment P.toValuationBuildingData sF⁻¹ w0
    have hinv : g⁻¹ • y = e (P.toValuationBuildingData.apartmentMap w') := by
      rw [hg, ← map_inv]
      rw [← hequiv]
      exact congrArg e (by simpa only [map_inv] using hw')
    change (g * x * g⁻¹) • y = y
    rw [mul_smul, mul_smul, hinv, hxfix]
    rw [← hinv, smul_inv_smul]
  have hstd : IsSplitTorus (splitTorus (Spec (CommRingCat.of K)) I) :=
    ⟨I, inferInstance, ⟨Iso.refl _⟩⟩
  obtain ⟨f, hf⟩ := C.isMaximalSplitTorus.exists_factor_of_commute hstd jK
    (commute_of_kernelPointwiseCommute v hstd C.isMaximalSplitTorus.1.1 jK C.i hcomm)
  refine ⟨qK.hom ≫ f, ?_⟩
  rw [Category.assoc, hf]
  dsimp only [qK, jK, j0, splitTorus.baseChangeHomAlong, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Langlands.Geometry.Building
