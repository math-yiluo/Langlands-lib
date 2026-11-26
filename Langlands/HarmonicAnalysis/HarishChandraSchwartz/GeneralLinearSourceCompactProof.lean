import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GeneralLinearSourceCompactStatement
import Langlands.Geometry.Building.IntegerValuationLocalComparison
import Langlands.Geometry.Building.ConjugateApartmentRealization
import Langlands.Geometry.Building.FullValidity.DatumTransport.Bounded
import Langlands.Geometry.Building.FullValidity.DatumTransport.RootSystem
import Langlands.GroupScheme.IntegralModel.BuildingComparisonProof
import Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints
import Langlands.GroupScheme.IntegralModel.MaximalCompact
import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerProof
import Langlands.GroupScheme.Reductive.GeneralLinearIsConnectedReductiveProof
import Langlands.GroupScheme.Reductive.GeneralLinearIsReductiveProof

/-! # The special-vertex realization of the standard general linear compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel Langlands.Plancherel.WaldspurgerSourceNormalization

namespace Langlands.HarishChandraSchwartz

open GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem diagonalBaseChange (N : ℕ) {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R) :
    (GroupScheme.baseChange b).map (diagonalTorus (Fin N) R) ≫
        (baseChangeIso (Fin N) b).hom =
      CommGroupScheme.groupHom (splitTorus.commBaseChangeIso b (ULift (Fin N))).hom ≫
        diagonalTorus (Fin N) R' := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv (Fin N) R' U).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_comp_baseChangeIso_hom,
    baseChangePointsEquiv_comp, pointsEquiv_diagonalTorus,
    Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_diagonalTorus]
  congr 1
  exact (splitTorus.pointsEquiv_baseChangeIso_hom b (ULift (Fin N)) U x).symm

private theorem diagonalFibrewiseMaximal (N : ℕ) (R : CommRingCat.{u}) :
    IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec R) (ULift (Fin N))) (diagonalTorus (Fin N) R) := by
  intro s
  let b := (Spec R).fromSpecResidueField s
  apply (IsMaximalTorus.comp_iso_iff _ (baseChangeIso (Fin N) b)).mp
  rw [diagonalBaseChange]
  exact IsMaximalTorus.precomp_torusIso (splitTorus.commBaseChangeIso b (ULift (Fin N)))
    (isMaximalTorus_diagonalTorus (n := Fin N) _)

private theorem genericDiagonal (N : ℕ) (R F : Type u) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] :
    (standardIntegralModel R F (Fin N)).genericSplitTorusHom
        (diagonalTorus (Fin N) (CommRingCat.of R)) =
      diagonalTorus (Fin N) (CommRingCat.of F) := by
  rw [IntegralModel.genericSplitTorusHom_eq]
  let b := Spec.algebraMap R F
  change (splitTorus.baseChangeIso b (ULift (Fin N))).inv ≫
      (GroupScheme.baseChange b).map (diagonalTorus (Fin N) (CommRingCat.of R)) ≫
      (baseChangeIso (Fin N) b).hom = _
  rw [diagonalBaseChange, ← Category.assoc]
  change ((splitTorus.baseChangeIso b (ULift (Fin N))).inv ≫
      (splitTorus.baseChangeIso b (ULift (Fin N))).hom) ≫ _ = _
  rw [Iso.inv_hom_id, Category.id_comp]

private theorem valuationUnit_iff_order_zero {F : Type u} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) (a : Fˣ) :
    v (a : F) = 1 ↔ IntegerValuation.order v a = 0 := by
  rw [← IntegerValuation.orderUnits_eq_one_iff]
  unfold IntegerValuation.order
  rw [Int.cast_eq_zero]
  rfl

private theorem torusKernel_of_root_orders {F : Type u} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ)))
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) {I : Type u} [Fintype I]
    {i : (SplitIntegralPinning.coordTorus F I).toGrp ⟶ G}
    (hi : IsMaximalSplitTorus (T := SplitIntegralPinning.coordTorus F I) i)
    (t : rationalPoints (SplitIntegralPinning.coordTorus F I).toGrp)
    (ht : ∀ a ∈ relativeRoots (T := SplitIntegralPinning.coordTorus F I) i,
      IntegerValuation.order v (torusCharEval (SplitIntegralPinning.coordTorus F I) a t) = 0)
    (hk : rationalPoints.map i t ∈ characterValuationKernel v G) :
    t ∈ characterValuationKernel v (SplitIntegralPinning.coordTorus F I).toGrp := by
  let e := BruhatTits.Cartan.restrictionEvaluation_id_bijective
    (S := SplitIntegralPinning.coordTorus F I) (isSplitTorus_splitTorus I)
  have hw : (IntegerValuation.centralizerValuation v (𝟙 _) e t).toAdd = 0 := by
    apply eq_zero_of_eval_relativeRoots_of_eval_torusCharacterRestrict hG _ hi
    · intro a ha
      rw [SplitIntegralPinning.eval_centralizerValuation_id]
      exact ht a ha
    · intro χ
      have heval : torusCharEval (SplitIntegralPinning.coordTorus F I)
          (torusCharacterRestrict i χ) t = rationalCharacterEval χ (rationalPoints.map i t) :=
        rationalCharacterEval_characterRestrict i χ t
      rw [SplitIntegralPinning.eval_centralizerValuation_id, heval]
      exact (valuationUnit_iff_order_zero v _).mp ((mem_characterValuationKernel.mp hk) χ)
  rw [← IntegerValuation.centralizerValuation_ker v (𝟙 _) e, MonoidHom.mem_ker,
    ← ofAdd_toAdd (IntegerValuation.centralizerValuation v (𝟙 _) e t), hw, ofAdd_zero]

set_option maxHeartbeats 1000000 in
private theorem exists_integralDiagonalPinning (N : ℕ) (R F : Type u)
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (v : Valuation F (WithZero (Multiplicative ℤ)))
    (hv : ∀ c : F, v c ≤ 1 ↔ c ∈ (algebraMap R F).range) :
    let i := diagonalTorus (Fin N) (CommRingCat.of F)
    ∃ (_ : Mono i.hom.hom.left) (P : SplitIntegralPinning v i),
      P.K ≤ (standardIntegralModel R F (Fin N)).integralPoints := by
  classical
  dsimp only
  rw [← genericDiagonal N R F]
  let M := standardIntegralModel R F (Fin N)
  let G := groupScheme (Fin N) (CommRingCat.of F)
  let T := SplitIntegralPinning.coordTorus F (ULift (Fin N))
  let i := diagonalTorus (Fin N) (CommRingCat.of R)
  let j := M.genericSplitTorusHom i
  have hG : IsConnectedReductive G := isConnectedReductiveStatement F (Fin N)
  have hR : IsReductive M.group := isReductiveStatement (Fin N) (CommRingCat.of R)
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom M.group.X.hom := hR.isAffineHom
  let : Smooth M.group.X.hom := hR.smooth
  have hc : IsClosedSubgroup i := isClosedSubgroup_diagonalTorus (Fin N) (CommRingCat.of R)
  have hmax := diagonalFibrewiseMaximal N (CommRingCat.of R)
  have hsplit : IsMaximalSplitTorus (T := T) j := M.isMaximalSplitTorus_genericSplitTorusHom i hmax
  let hm : Mono j.hom.hom.left := mono_of_isMaximalSplitTorus hsplit
  obtain ⟨J, P, hP⟩ :=
    localSplitFibrewiseRootDatumExistence R M.group hR (ULift (Fin N)) i hc hmax
  let : Fintype J := @Fintype.ofFinite J hP.finite
  let := hP.isReduced
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  obtain ⟨u, hu, hw⟩ := localSplitRootGroup R M.group hR (ULift (Fin N)) i hc hmax J P hP b
  let generators : Set (rationalPoints G) :=
    rationalPoints.map j '' (characterValuationKernel v T.toGrp : Set _) ∪
      ⋃ α, SplitIntegralPinning.fieldRootPoint (M.genericRootHom (u α)) '' {c | v c ≤ 1}
  let H := Subgroup.closure generators
  have hroot (α : J) (c : F) :
      SplitIntegralPinning.fieldRootPoint (M.genericRootHom (u α)) c ∈ M.integralPoints ↔
        v c ≤ 1 :=
    M.fieldRootPoint_genericRootHom_mem_integralPoints_iff v hv _ (hu α).isClosedSubgroup c
  have hH : H ≤ M.integralPoints := by
    apply (Subgroup.closure_le _).2
    rintro _ (⟨t, ht, rfl⟩ | hg)
    · apply M.map_genericSplitTorusHom_mem_integralPoints hv hG i hc hsplit t
      · intro a _
        exact (valuationUnit_iff_order_zero v _).mp
          ((mem_characterValuationKernel.mp ht) ((rationalCharacters.equivCharacterLattice T).symm a))
      · exact IntegerValuation.map_mem_characterValuationKernel v j ht
    · obtain ⟨α, c, hc, rfl⟩ := Set.mem_iUnion.mp hg
      exact (hroot α c).2 hc
  refine ⟨hm, SplitIntegralPinning.ofRootParametrizations v hG
    (M.isMaximalTorus_genericSplitTorusHom i hmax) hP.isReduced
    (M.isRootDatumOf_genericSplitTorusHom i hP) b
    (fun α => M.isRootParametrization_genericRootHom i (hu α))
    (fun α ha => M.isWeylPoint_genericRootHom i (hw α ha)) H ?_ ?_ le_rfl, hH⟩
  · intro α c
    refine ⟨fun h => (hroot α c).1 (hH h), fun hc => Subgroup.subset_closure ?_⟩
    exact Or.inr (Set.mem_iUnion.mpr ⟨α, c, hc, rfl⟩)
  · intro t ht hk
    exact Subgroup.subset_closure (Or.inl ⟨t, torusKernel_of_root_orders v hG hsplit t ht hk, rfl⟩)

private theorem specialPoint_reindexOrder {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω ω' : Fˣ → ℝ} (D : KPApartmentData i ω)
    (h : ω = ω') (x : D.Apartment) :
    AffineRootSystem.IsSpecialPoint (D.reindexOrder h).affineRoots (D.reindexOrderApartment h x) ↔
      AffineRootSystem.IsSpecialPoint D.affineRoots x := by
  cases h
  rfl

private theorem normalizedValuation_le_one {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (c : F) :
    FML.normalizedMultiplicativeValuation F c ≤ 1 ↔ c ∈ (algebraMap ↥𝒪[F] F).range := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  change e (ValuativeRel.valuation F c) ≤ 1 ↔ c ∈ (algebraMap ↥𝒪[F] F).range
  rw [← map_one e, map_le_map_iff e]
  exact ⟨fun h => ⟨⟨c, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩

set_option maxHeartbeats 2000000 in
/-- The standard model compact is realized at a special vertex of the diagonal
apartment, which carries the apartment axioms and bounded open stabilizers. -/
theorem generalLinearSourceCompactGeometry (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (N : ℕ) :
    let S := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
    let i := diagonalTorus (Fin N) (CommRingCat.of F)
    let K := (standardIntegralModel ↥𝒪[F] F (Fin N)).integralPoints
    haveI := isAffineHom_groupScheme (n := Fin N) (R := CommRingCat.of F)
    IsCompactOpenMaximal F K ∧
      ∃ hi : IsMaximalSplitTorus (T := S) i,
        haveI := mono_of_isMaximalSplitTorus hi
        ∃ (C : CentralizerDatum (S := S) i) (D : KPApartmentData (S := S) i (localFieldOrder F))
          (x : D.Apartment),
          D.SatisfiesApartmentAxioms C ∧ D.HasBoundedOpenStabilizers ∧
            D.IsSpecialApartmentVertex x ∧ D.specialCompactSubgroup x = K := by
  classical
  let G := groupScheme (Fin N) (CommRingCat.of F)
  let S := splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin N))
  let i := diagonalTorus (Fin N) (CommRingCat.of F)
  let M := standardIntegralModel ↥𝒪[F] F (Fin N)
  have hG : IsConnectedReductive G := isConnectedReductiveStatement F (Fin N)
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hspecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) :=
    IsConnectedReductive.of_iso (baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] 𝓀[F]))
      (isConnectedReductiveStatement 𝓀[F] (Fin N))
  obtain ⟨hc, hmax⟩ := IntegralModel.maximalCompactStatement F G hG M hspecial
  refine ⟨⟨hc, M.isOpen_integralPoints_localField, hc, fun L hL hKL => (hmax L hL hKL).le⟩, ?_⟩
  obtain ⟨P, R, T, hR, hB, hT, hRR, hA, hC, hTits⟩ := rootValuationBuildingConstruction F G hG
  obtain ⟨y, -, hM⟩ := IntegralModel.specialStabilizerStatement_of_unramified
    IntegralModel.unramifiedSpecialStabilizer
    (unramifiedBuildingDescentStatement_of_apartmentDescent unramifiedApartmentDescent)
    F G hG M hspecial P R T hR hB hT hRR hA hC hTits
  let B := P.toValuationBuildingData
  have hsplit : IsMaximalSplitTorus (T := S) i :=
    isMaximalSplitTorus_diagonalTorus (n := Fin N) F
  have hmaxTorus : IsMaximalTorus (T := S) i :=
    isMaximalTorus_diagonalTorus (n := Fin N) F
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy.{u} F G hG).1
    B.S S B.i i B.isMaximalSplitTorus hsplit
  let σ : B.S ≅ S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have h : B.i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i := he
  let Bd := B.basedTransport σ (G.innerIso g) h
  have hAd : Bd.SatisfiesApartmentAxioms :=
    ValuationBuildingData.SatisfiesApartmentAxioms.basedTransport B σ (G.innerIso g) h hA
  have hBd : Bd.HasBoundedOpenStabilizers :=
    ValuationBuildingData.HasBoundedOpenStabilizers.basedTransport B σ (G.innerIso g) h hB
  let v := FML.normalizedMultiplicativeValuation F
  let C := IntegerValuationBuildingData.ofLocal Bd
  obtain ⟨hmono, Pin, hPin⟩ := exists_integralDiagonalPinning N ↥𝒪[F] F v
    normalizedValuation_le_one
  let Fr : C.SplitIntegralFrame :=
    IntegerValuationBuildingData.SplitIntegralPinning.toFrame (B := C) hmaxTorus Pin
  let π := SplitTorusValuation.uniformizerUnit F
  have hπ : (IntegerValuation.orderUnits v π).toAdd = 1 := by
    rw [IntegerValuation.orderUnits_normalized]
    exact SplitTorusValuation.fieldOrderUnits_uniformizerUnit F
  have hπsq : π ^ 2 ≠ 1 := by
    intro hp
    have hpow := congrArg (fun d : Fˣ => (IntegerValuation.orderUnits v d).toAdd) hp
    rw [map_pow, map_one, toAdd_pow, hπ, toAdd_one] at hpow
    norm_num at hpow
  obtain ⟨xi, hxi, -, hFr⟩ := Fr.exists_isSpecialPoint_K_eq_oneStabilizer ⟨π, hπsq⟩
  have hsp := Fr.isSpecialPoint hxi
  obtain ⟨x, rfl⟩ := (IntegerValuationBuildingData.ofLocalApartmentEquiv Bd).surjective xi
  have hxSpecial : AffineRootSystem.IsSpecialPoint Bd.affineRoots x :=
    (specialPoint_reindexOrder Bd.apartment (IntegerValuation.order_normalized F).symm x).mp hsp
  have hx : Bd.apartment.IsSpecialApartmentVertex x :=
    ⟨hxSpecial, AffineRootSystem.isVertex_of_isSpecialPoint hAd.isAffineRootSystem_affineRoots hxSpecial⟩
  have hK : Pin.K = Bd.apartment.specialCompactSubgroup x := by
    change Fr.K = Bd.compactStabilizer (Bd.apartmentMap x)
    rw [← IntegerValuationBuildingData.ofLocal_oneStabilizer,
      IntegerValuationBuildingData.ofLocalBuildingEquiv_apartmentMap]
    exact hFr
  let z := B.apartment.conjugateApartmentMap σ g h x
  have hzK : B.compactStabilizer z = Pin.K := by
    rw [hK]
    change rationalCommonNormKernel G ⊓
      B.apartment.reducedFixer (B.apartment.conjugateReducedBuildingEquiv σ g h (Bd.apartmentMap x)) =
      rationalCommonNormKernel G ⊓ Bd.apartment.reducedFixer (Bd.apartmentMap x)
    rw [B.apartment.reducedFixer_conjugateReducedBuildingEquiv σ g h]
    rfl
  let A := B.basedApartmentEquiv σ (G.innerIso g) h
  obtain ⟨w, hw⟩ := A.surjective x
  have hzw : g • B.apartmentMap w = z := by
    rw [← B.apartment.conjugateApartmentMap_transport σ g h w]
    exact congrArg (B.apartment.conjugateApartmentMap σ g h) hw
  have hwSpecial : AffineRootSystem.IsSpecialPoint B.affineRoots w := by
    apply (AffineRootSystem.isSpecialPoint_transportedRoots_iff A B.affineRoots w).mp
    rw [show AffineRootSystem.transportedRoots A B.affineRoots = Bd.affineRoots from
      B.transportedRoots_basedApartmentEquiv σ (G.innerIso g) h, hw]
    exact hx.1
  have hyz : y = z := B.eq_of_compactStabilizer_fixed_of_special_buildingPoint hA
    P.hasOppositeFactorPairs hC.injective
    (fun a => R.hasCommonApartmentWith_of_isBuilding hR.isBuilding (B.apartmentMap a))
    ⟨g, w, hzw, hwSpecial⟩
    (fun k hk => (B.mem_compactStabilizer.mp (hM ▸ hPin (hzK ▸ hk))).2)
  refine ⟨hsplit, Bd.centralizer, Bd.apartment, x, hAd, hBd, hx, ?_⟩
  calc
    Bd.apartment.specialCompactSubgroup x = Pin.K := hK.symm
    _ = B.compactStabilizer z := hzK.symm
    _ = M.integralPoints := by simpa only [hyz] using hM.symm

/-- The integral points of the standard general linear model realize the compact chosen in
Waldspurger I.1, using the apartment of the actual diagonal torus. -/
theorem generalLinearSourceCompact : GeneralLinearSourceCompactStatement.{u} := by
  intro F _ _ _ _ N
  obtain ⟨hc, hi, C, D, x, hA, -, hx, heq⟩ := generalLinearSourceCompactGeometry F N
  exact ⟨hc, hi, C, D, x, hA.omegaCompatible, hx, heq⟩

end Langlands.HarishChandraSchwartz
