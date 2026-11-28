import Langlands.Geometry.Building.KPTorusBuildingProof
import Langlands.GroupScheme.IntegralModel.ResidueSplitTorusGenericLift
import Langlands.LocalFactor.FML.Valuation
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.IntegralModel.OrderedCellLemmas
import Langlands.GroupScheme.Rational.ParabolicWhiteheadIsomorphism
import Langlands.GroupScheme.Rational.SplitRankReduction
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.SplitTorusRationalRank

/-!
# Split tori: proof of `KPSplitTorusBuildingStatement`

For a split torus `T` over a nonarchimedean local field `F` and KP building data of `T`
satisfying the one-group axioms, the integral split torus of Axiom 4.1.20(3) at the facet is
isomorphic to the neutral facet model. This gives `T(F)^0 = T(F)^1`, the component group
`T(F)/T(F)^0 ≃ ℤ^N` through the valuation homomorphism, and `(q - 1)^N` residue-field points of
the reductive quotient. The final theorem `kpSplitTorusBuilding` proves
`KPSplitTorusBuildingStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k] {T : GroupScheme (Spec (CommRingCat.of k))}

/-- A maximal split torus of a split torus is an isomorphism onto it. -/
theorem isIso_of_isMaximalSplitTorus_of_isSplitTorus (hT : IsSplitTorus T)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ T}
    (hi : IsMaximalSplitTorus i) : IsIso i := by
  let U : CommGroupScheme (Spec (CommRingCat.of k)) := { T with comm := hT.isCommMonObj }
  exact hi.2 U (𝟙 U.toGrp) ⟨hT, IsClosedSubgroup.of_iso (Iso.refl _)⟩ i (Category.comp_id i)

end Field

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The normalized `ℤᵐ⁰`-valued valuation of `F` has valuation ring `𝒪[F]`. -/
theorem normalizedMultiplicativeValuation_le_one_iff (c : F) :
    FML.normalizedMultiplicativeValuation F c ≤ 1 ↔ c ∈ (algebraMap 𝒪[F] F).range := by
  have h : FML.normalizedMultiplicativeValuation F c ≤ 1 ↔ ValuativeRel.valuation F c ≤ 1 := by
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
      (ValuativeRel.valuation F c) ≤ 1 ↔ _
    rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F), map_le_map_iff]
  rw [h]
  exact ⟨fun hc => ⟨⟨c, hc⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩

section Valuation

variable {T : GroupScheme (Spec (CommRingCat.of F))}

/-- For a split torus the valuation homomorphism `T(F) → Hom(X^*_F(T), ℤ)` is surjective
(KP Lemma 2.5.7). -/
theorem rationalCharacterValuation_surjective_of_isSplitTorus (hT : IsSplitTorus T) :
    Function.Surjective (Plancherel.rationalCharacterValuation T) := by
  let U : CommGroupScheme (Spec (CommRingCat.of F)) := { T with comm := hT.isCommMonObj }
  intro f
  have := CocharacterUniformizer.latticePairing_isPerfPair F U hT
  let f' : characterLattice U →ₗ[ℤ] ℤ :=
    (f.toAdd.comp (rationalCharacters.equivCharacterLattice U).symm.toAddMonoidHom).toIntLinearMap
  obtain ⟨c, hc⟩ := (LinearMap.IsPerfPair.bijective_right (latticePairing U)).surjective f'
  refine ⟨CocharacterUniformizer.latticeSection F U (Multiplicative.ofAdd c), ?_⟩
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro χ
  have h := CocharacterUniformizer.rationalCharacterValuation_latticeSection F U
    (rationalCharacters.equivCharacterLattice U χ) c
  rw [AddEquiv.symm_apply_apply] at h
  rw [h]
  have h2 := LinearMap.congr_fun hc (rationalCharacters.equivCharacterLattice U χ)
  change latticePairing U _ c = _ at h2
  rw [h2]
  change f.toAdd ((rationalCharacters.equivCharacterLattice U).symm
    (rationalCharacters.equivCharacterLattice U χ)) = _
  rw [AddEquiv.symm_apply_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a split torus of split rank `N`, `Hom(X^*_F(T), ℤ)` is isomorphic to `ℤ^N`. -/
theorem nonempty_valuationCoordinates_of_isSplitTorus (hT : IsSplitTorus T) {N : ℕ}
    (hN : splitRank T = N) : Nonempty ((rationalCharacters T →+ ℤ) ≃+ (Fin N → ℤ)) := by
  let U : CommGroupScheme (Spec (CommRingCat.of F)) := { T with comm := hT.isCommMonObj }
  obtain ⟨I, hI, ⟨eT⟩⟩ := hT
  have hcard : Nat.card I = N := by
    have h := splitRank_eq_of_splitIso I eT
    rw [hN] at h
    exact_mod_cast h.symm
  let σ : I ≃ Fin N := (Finite.equivFin I).trans (finCongr hcard)
  let cX : rationalCharacters T ≃ₗ[ℤ] (Fin N → ℤ) :=
    ((rationalCharacters.equivCharacterLattice U).trans
      (splitTorusCharacterCoordinates (T := U) eT)).toIntLinearEquiv.trans
      (LinearEquiv.funCongrLeft ℤ ℤ σ.symm)
  let b : Module.Basis (Fin N) ℤ (rationalCharacters T) := (Pi.basisFun ℤ (Fin N)).map cX.symm
  exact ⟨((addMonoidHomLequivInt ℤ).trans (b.constr ℤ).symm).toAddEquiv⟩

end Valuation

namespace KPBuildingDatum

open BruhatTits.IntegralModels

variable {T : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.X.hom]
  (D : KPBuildingDatum T)

/-- For a split torus and data satisfying the one-group axioms, `T(F)^1` lies in the parahoric
of every facet: it is the image of the units of the integral split torus of Axiom 4.1.20(3). -/
theorem rationalCommonNormKernel_le_parahoric_of_isSplitTorus (hT : IsSplitTorus T)
    (hD : D.SatisfiesGroupAxioms) (x : BuildingFacet D.base.toValuationBuildingData) :
    rationalCommonNormKernel T ≤ D.parahoric x := by
  let B := D.base.toValuationBuildingData
  obtain ⟨g, Fa, -, hx⟩ := x.property
  let Ω := BuildingModelIndex.ofFacet x
  have hΩ : Ω.val = B.translatedApartmentMap g '' Fa := hx
  let A := D.models.torus Ω g Fa hΩ
  have hc := hD.bruhatTitsGroupSchemes.torus_clause Ω g Fa hΩ
  have hsplit : IsSplitTorus A.torus.toGrp := hc.1.1
  have hclosed : IsClosedSubgroup A.inclusion := hc.1.2
  have : IsIso B.i := isIso_of_isMaximalSplitTorus_of_isSplitTorus hT B.isMaximalSplitTorus
  let ψ : (GroupScheme.baseChange (Spec.algebraMap 𝒪[F] F)).obj A.torus.toGrp ≅ T :=
    A.genericIso ≪≫ asIso B.i ≪≫ T.innerIso g
  intro s hs
  rw [← IntegerValuation.characterValuationKernel_normalized] at hs
  have ht := map_characterValuationKernel_le (FML.normalizedMultiplicativeValuation F) ψ.inv
    ⟨s, hs, rfl⟩
  have h := (D.models.model Ω).neutral.map_genericHom_mem_integralPoints_of_split_characterKernel
    normalizedMultiplicativeValuation_le_one_iff hsplit A.inclusion hclosed _ ht
  have hgen : (D.models.model Ω).neutral.genericHom A.inclusion = ψ.hom := by
    rw [IntegralModel.genericHom, A.generic_comm]
    simp only [ψ, Iso.trans_hom, asIso_hom]
    rfl
  rw [hgen, ← rationalPoints.map_comp_apply, ψ.inv_hom_id] at h
  change s ∈ (D.models.model Ω).neutral.integralPoints
  simpa [rationalPoints.map_apply] using h

/-- For a split torus of split rank `N` and data satisfying the one-group axioms, the finite
group of residue-field points of the reductive quotient at every facet has `(q - 1)^N`
elements. -/
theorem card_finiteReductiveQuotientGroup_of_isSplitTorus (hT : IsSplitTorus T) {N : ℕ}
    (hN : splitRank T = N) (hD : D.SatisfiesGroupAxioms)
    (x : BuildingFacet D.base.toValuationBuildingData) :
    Nat.card (D.finiteReductiveQuotientGroup x hD) = (Nat.card 𝓀[F] - 1) ^ N := by
  let B := D.base.toValuationBuildingData
  obtain ⟨g, Fa, -, hx⟩ := x.property
  let Ω := BuildingModelIndex.ofFacet x
  have hΩ : Ω.val = B.translatedApartmentMap g '' Fa := hx
  let M := D.models.model Ω
  let A := D.models.torus Ω g Fa hΩ
  have hc := hD.bruhatTitsGroupSchemes.torus_clause Ω g Fa hΩ
  have hsplit : IsSplitTorus A.torus.toGrp := hc.1.1
  have hclosed : IsClosedSubgroup A.inclusion := hc.1.2
  have : IsIso B.i := isIso_of_isMaximalSplitTorus_of_isSplitTorus hT B.isMaximalSplitTorus
  let ψ : (GroupScheme.baseChange (Spec.algebraMap 𝒪[F] F)).obj A.torus.toGrp ≅ T :=
    A.genericIso ≪≫ asIso B.i ≪≫ T.innerIso g
  -- the generic fibre of the integral torus inclusion is an isomorphism
  have hgen : (GroupScheme.baseChange (Spec.algebraMap 𝒪[F] F)).map A.inclusion =
      (ψ ≪≫ M.neutral.genericIso.symm).hom := by
    rw [Iso.trans_hom, Iso.symm_hom, Iso.eq_comp_inv, A.generic_comm]
    simp only [ψ, Iso.trans_hom, asIso_hom]
    rfl
  have hK : IsIso ((Over.pullback (Spec.algebraMap 𝒪[F] F)).map A.inclusion.hom.hom) := by
    change IsIso ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] F)).map A.inclusion).hom.hom
    rw [hgen]
    exact (inferInstance : IsIso ((Grp.forget _).mapIso (ψ ≪≫ M.neutral.genericIso.symm)).hom)
  have : IsClosedImmersion A.inclusion.hom.hom.left := hclosed
  have : IsIso A.inclusion.hom.hom := isIso_of_isClosedImmersion_of_isIso_pullback (K := F) _ hK
  have : IsIso ((Mon.forget _).map A.inclusion.hom) := ‹IsIso A.inclusion.hom.hom›
  have : IsIso A.inclusion.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map A.inclusion) := ‹IsIso A.inclusion.hom›
  have : IsIso A.inclusion := isIso_of_reflects_iso A.inclusion (Grp.forget₂Mon _)
  let eI : A.torus.toGrp ≅ M.neutral.group := asIso A.inclusion
  -- the special fibre of the neutral model is a split torus of the same rank
  obtain ⟨J, hJ, ⟨eS⟩⟩ := hsplit
  let r := IntegralModel.residueBaseMap 𝒪[F]
  let eK : M.neutral.specialFibre ≅ splitTorus (Spec (CommRingCat.of 𝓀[F])) J :=
    (GroupScheme.baseChange r).mapIso (eI.symm ≪≫ eS) ≪≫ splitTorus.baseChangeIso r J
  let eF : T ≅ splitTorus (Spec (CommRingCat.of F)) J :=
    ψ.symm ≪≫ (GroupScheme.baseChange (Spec.algebraMap 𝒪[F] F)).mapIso eS ≪≫
      splitTorus.baseChangeIso (Spec.algebraMap 𝒪[F] F) J
  have hNJ : Nat.card J = N := by
    have h := splitRank_eq_of_splitIso J eF
    rw [hN] at h
    exact_mod_cast h.symm
  have hsf : IsSplitTorus M.neutral.specialFibre := ⟨J, hJ, ⟨eK⟩⟩
  -- the radical is trivial and the projection is bijective on residue-field points
  let Q := D.quotients.quotient x
  obtain ⟨hrad, hquot, -⟩ := hD.reductiveQuotients.facets.reductive_quotients x
  have hrange := hrad.range_eq_bot hsf.hasTrivialUnipotentRadical
  have hradpts : Q.radicalPoints = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, rfl⟩
    have hy : y ≫ Q.radicalInclusion.hom.hom ∈
        (SubgroupFunctor.range Q.radicalInclusion).carrier (Over.mk (𝟙 _)) := ⟨y, rfl⟩
    rw [hrange] at hy
    exact hy
  have hbij : Function.Bijective Q.projectionPoints := by
    refine ⟨?_, Q.projectionPoints_surjective hrad hquot⟩
    rw [← MonoidHom.ker_eq_bot_iff, Q.ker_projectionPoints hquot, hradpts]
  change Nat.card (rationalPoints Q.quotient) = _
  rw [← Nat.card_congr (MulEquiv.ofBijective Q.projectionPoints hbij).toEquiv]
  change Nat.card (rationalPoints M.neutral.specialFibre) = _
  rw [Nat.card_congr ((rationalPoints.mapEquiv eK).trans ((splitTorus.pointsEquiv J _).trans
      (MulEquiv.piCongrRight fun _ => Units.mapEquiv
        (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).commRingCatIsoToRingEquiv.toMulEquiv))).toEquiv,
    Nat.card_fun, Nat.card_units, hNJ]

end KPBuildingDatum

/-- Proof of `KPSplitTorusBuildingStatement`. -/
theorem kpSplitTorusBuilding : KPSplitTorusBuildingStatement.{u} := by
  intro F _ _ _ _ T N hT hN
  let : IsAffineHom T.X.hom := (RelativeTorus.IsTorus.of_isSplitTorus hT).isAffineHom
  intro D hD T0
  obtain ⟨⟨x⟩⟩ := D.base.toValuationBuildingData.nonempty_unique_buildingFacet_of_isTorus hT.isTorus
  have hT0 : T0 = rationalCommonNormKernel T := by
    refine le_antisymm (D.base.zeroDatum.map_centralizerZero_le_zeroSubgroup.trans
      D.base.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel) ?_
    exact (D.rationalCommonNormKernel_le_parahoric_of_isSplitTorus hT hD x.default).trans
      (D.parahoric_eq_of_isTorus hT.isTorus hD x.default).le
  have hker : T0 = (Plancherel.rationalCharacterValuation T).ker :=
    hT0.trans (Plancherel.rationalCharacterValuation_ker T).symm
  have hnormal : T0.Normal := by
    rw [hker]
    infer_instance
  obtain ⟨e⟩ := nonempty_valuationCoordinates_of_isSplitTorus hT hN
  refine ⟨hT0, ⟨hnormal, e, (QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _
      (rationalCharacterValuation_surjective_of_isSplitTorus hT)).trans
        (AddEquiv.toMultiplicative e)), fun t => rfl⟩,
    fun y => D.card_finiteReductiveQuotientGroup_of_isSplitTorus hT hN hD y⟩

end Langlands.Geometry.Building
