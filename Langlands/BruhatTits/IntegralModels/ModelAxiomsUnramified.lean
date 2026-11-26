import Langlands.BruhatTits.IntegralModels.UnramifiedModelAxioms

/-! # KP Axiom 4.1.20 on supplied data from the unramified statements -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building LocalGalois.Separable GaloisPointComparison IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

section Points

variable {B : ValuationBuildingData G}
  {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (e : B.ReducedBuilding → C.ReducedBuilding) (he_inj : Function.Injective e)
  (he_smul : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)

include he_inj he_smul in
/-- **`G(F)^1_Ω` from `G(K)^1_{e(Ω)}`.** If the base change of a model over `𝒪[F]` to the
maximal unramified integers has integral points `G(K)^1 ∩ Fix(e(Y))`, then the model itself has
integral points `Fix(Y) ∩ G(F)^1`. -/
theorem integralPoints_eq_of_unramified_one (M : IntegralModel ↥𝒪[F] F G)
    (Y : Set B.ReducedBuilding)
    (h : M.baseChangeUnramified.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓ C.pointwiseFixer (e '' Y)) :
    M.integralPoints = B.apartment.pointwiseFixer Y ⊓ Plancherel.rationalCommonNormKernel G := by
  rw [M.integralPoints_eq_comap_baseChangeUnramified, h, Subgroup.comap_inf,
    MaximalUnramified.characterValuationKernel_comap F G,
    MaximalUnramified.pointwiseFixer_comap B C e he_inj he_smul Y, inf_comm]

include he_inj he_smul in
/-- **`G(F)^0_Ω` from `G(K)^0_{e(Ω)}`.** Granting KP Proposition 9.3.24 in the form of
`UnramifiedZeroDescentStatement`, if the base change of a model over `𝒪[F]` has integral points
`G(K)^0 ∩ Fix(e(Y))`, then the model has integral points `Fix(Y) ∩ G(F)^0`. -/
theorem integralPoints_eq_of_unramified_zero (hzero : UnramifiedZeroDescentStatement.{u})
    (hG : IsConnectedReductive G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {Z : GroupScheme (Spec (CommRingCat.of F))} (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (Z0 : ZeroSubgroupDatum i j)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (M : IntegralModel ↥𝒪[F] F G) (Y : Set B.ReducedBuilding)
    (h : M.baseChangeUnramified.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Y)) :
    M.integralPoints = B.apartment.pointwiseFixer Y ⊓ Z0.zeroSubgroup := by
  rw [M.integralPoints_eq_comap_baseChangeUnramified, h, Subgroup.comap_inf,
    ((hzero F G hG).2 E).2 i j Z0,
    MaximalUnramified.pointwiseFixer_comap B C e he_inj he_smul Y, inf_comm]

end Points

variable (P : ParahoricBuildingData G) (R : P.toValuationBuildingData.PolysimplicialRealization)
  (T : P.toValuationBuildingData.ApartmentSplitting)
  (h1 : P.SatisfiesBuildingAxiom R) (h2 : P.HasBoundedOpenStabilizers)
  (h3 : P.SatisfiesAffineApartmentAxiom T) (h4 : P.HasRootReflections)
  (h5 : P.SatisfiesApartmentAxioms) (h6 : P.HasCompatibleApartmentFacets)
  (h7 : P.HasTitsSystem)

set_option maxHeartbeats 4000000 in
include h1 h2 h3 h4 h5 h6 h7 in
/-- **KP Axiom 4.1.20 from the unramified statements.** Let `P`, `R`, `T` satisfy the seven
predicates of the target statement, and let `C`, `A`, `e`, `a` be building data over the
maximal unramified extension with an injective equivariant embedding `e` compatible with the
apartment maps through `a`, Galois-fixed image, facet preimages and `S(K)^1`-fixed apartment
(the relevant conclusions of the apartment-compatible unramified descent). Granting KP
8.3.2/8.3.13 over `K` (`UnramifiedParahoricModelStatement`), KP Fact 2.10.16, KP Proposition
9.3.24, KP Corollary 2.10.10, the closure invariance of `G(K)^1`-fixers, the affine-root
description of `G(K)^0`-fixers and the torus clause over `𝒪[F]`, there is a building model
family over `𝒪[F]` satisfying Axiom 4.1.20 whose neutral models have unramified integral points
`G(K)^0 ∩ Fix(e(Ω))`, for the zero datum built from `P`. -/
theorem BuildingModelFamily.exists_satisfiesModelAxioms_of_unramified
    (hpar : UnramifiedParahoricModelStatement.{u})
    (hdesc : UnramifiedSmoothModelDescentStatement.{u})
    (hzero : UnramifiedZeroDescentStatement.{u})
    (hext : UnramifiedSmoothHomExtensionStatement.{u})
    (hclos : UnramifiedOneFixerClosureStatement.{u})
    (hroot : UnramifiedZeroFixerAffineRootStatement.{u})
    (htor : UnramifiedTorusClauseStatement.{u})
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (A : MaximalUnramified.SemilinearApartmentData C)
    (e : P.toValuationBuildingData.ReducedBuilding → C.ReducedBuilding)
    (a : P.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment)
    (he_inj : Function.Injective e)
    (he_smul : ∀ (g : rationalPoints G) (z : P.toValuationBuildingData.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (he_apt : ∀ w : P.toValuationBuildingData.Apartment,
      e (P.toValuationBuildingData.apartmentMap w) = C.apartmentMap (a w))
    (hA_fix : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
        (z : P.toValuationBuildingData.ReducedBuilding),
      A.action σ (e z) = e z)
    (hfacet : ∀ w : P.toValuationBuildingData.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
        AffineRootSystem.facet P.toValuationBuildingData.affineRoots w)
    (hkernel : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) P.S.toGrp),
      ∀ w : P.toValuationBuildingData.Apartment,
        rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map P.i) s •
          e (P.toValuationBuildingData.apartmentMap w) =
            e (P.toValuationBuildingData.apartmentMap w)) :
    ∃ M : BuildingModelFamily P.toValuationBuildingData ↥𝒪[F],
      M.SatisfiesModelAxioms P ∧
        ∀ Ω : BuildingModelIndex P.toValuationBuildingData,
          (M.model Ω).neutral.baseChangeUnramified.integralPoints =
            (unramifiedZeroDatumOfParahoric P).zeroPoints ⊓ C.pointwiseFixer (e '' Ω.val) := by
  have hG : IsConnectedReductive G := P.isConnectedReductive
  have hbdd : ∀ (Ω : BuildingModelIndex P.toValuationBuildingData) (g : rationalPoints G)
      (Ωa : Set P.toValuationBuildingData.Apartment),
      Ω.val = P.toValuationBuildingData.translatedApartmentMap g '' Ωa →
        P.toValuationBuildingData.IsBoundedSubset Ωa :=
    fun Ω _ _ h => isBoundedSubset_of_buildingModelIndex P R T h1 h2 h3 h4 h5 h6 h7 Ω h
  have hface : ∀ Fa Fa' : Set P.toValuationBuildingData.Apartment,
      AffineRootSystem.IsFaceOf P.toValuationBuildingData.affineRoots Fa Fa' →
        Fa ⊆ apartmentClosure P.toValuationBuildingData Fa' :=
    fun _ _ h => subset_apartmentClosure_of_isFaceOf _ h
  have hfixY : ∀ (Ω : BuildingModelIndex P.toValuationBuildingData)
      (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F), ∀ y ∈ e '' Ω.val,
        A.action σ y = y := by
    rintro Ω σ _ ⟨z, -, rfl⟩
    exact hA_fix σ z
  -- The models.
  have hmodel : ∀ Ω : BuildingModelIndex P.toValuationBuildingData,
      ∃ D : RelativeComponentModelData ↥𝒪[F] F G,
        D.full.baseChangeUnramified.integralPoints =
            characterValuationKernel (MaximalUnramified.valuation F)
                (baseChanged F (inertiaFixedField F) G) ⊓ C.pointwiseFixer (e '' Ω.val) ∧
          D.neutral.baseChangeUnramified.integralPoints =
            (unramifiedZeroDatumOfParahoric P).zeroPoints ⊓ C.pointwiseFixer (e '' Ω.val) :=
    fun Ω => exists_relativeComponentModelData_of_unramified hpar hdesc hzero hG A
      (unramifiedZeroDatumOfParahoric P) (e '' Ω.val)
      (exists_unramified_presentation e a he_smul he_apt hbdd Ω) (hfixY Ω)
  choose model hfull hneut using hmodel
  -- The integral tori.
  have htor' : ∀ (Ω : BuildingModelIndex P.toValuationBuildingData) (g : rationalPoints G)
      (Ωa : Set P.toValuationBuildingData.Apartment)
      (_ : Ω.val = P.toValuationBuildingData.translatedApartmentMap g '' Ωa),
      ∃ T' : IntegralTorusData (model Ω) P.toValuationBuildingData.S
          (P.toValuationBuildingData.i ≫ (G.innerIso g).hom), T'.SatisfiesTorusClause := by
    intro Ω g Ωa h
    refine htor F G hG P.S P.i P.isMaximalSplitTorus C (unramifiedZeroDatumOfParahoric P)
      (a '' Ωa) ((BuildingModelIndex.nonempty_of_eq_translatedApartmentMap h).image a)
      (bddAbove_image_image a (hbdd Ω g Ωa h)) ?_ g (model Ω) ?_
    · rintro s hs _ ⟨w, -, rfl⟩
      rw [← he_apt]
      exact hkernel s hs w
    · rw [hneut Ω, h, image_translatedApartmentMap e a he_smul he_apt]
  choose torus htorus using htor'
  -- The morphisms.
  have hmor : ∀ Ω Ω' : BuildingModelIndex P.toValuationBuildingData,
      ModelMorphismRequired P.toValuationBuildingData Ω Ω' →
        Nonempty (RelativeComponentModelHom (model Ω') (model Ω)) := by
    intro Ω Ω' h
    have hle := one_inf_pointwiseFixer_le e a he_smul he_apt hbdd hclos hface h
    have hfull_le : (model Ω').full.baseChangeUnramified.integralPoints ≤
        (model Ω).full.baseChangeUnramified.integralPoints := by
      rw [hfull Ω', hfull Ω]
      exact hle
    have hneut_le : (model Ω').neutral.baseChangeUnramified.integralPoints ≤
        (model Ω).neutral.baseChangeUnramified.integralPoints := by
      rw [hneut Ω', hneut Ω]
      exact inf_le_inf_of_le_of_inf_le
        (UnramifiedZeroDatum.zeroPoints_le_unramifiedCharacterValuationKernel
        (unramifiedZeroDatumOfParahoric P)) hle
    obtain ⟨φf⟩ := nonempty_hom_of_unramified_le hext (model Ω').full (model Ω).full
      (model Ω').full_smooth hfull_le
    obtain ⟨φn⟩ := nonempty_hom_of_unramified_le hext (model Ω').neutral (model Ω).neutral
      (model Ω').neutral_smooth hneut_le
    exact ⟨⟨φf, φn, comp_hom_eq_of_generic φn (model Ω).inclusion (model Ω').inclusion φf⟩⟩
  refine ⟨⟨model, fun Ω Ω' h => (hmor Ω Ω' h).some, torus⟩,
    ⟨rfl, ?_, ?_, ?_, ?_, htorus, ?_⟩, hneut⟩
  · -- full points
    intro Ω
    exact integralPoints_eq_of_unramified_one e he_inj he_smul (model Ω).full Ω.val (hfull Ω)
  · -- neutral points
    intro Ω
    exact integralPoints_eq_of_unramified_zero e he_inj he_smul hzero hG P.i P.centralizer.j
      P.zeroDatum (unramifiedZeroDatumOfParahoric P) (model Ω).neutral Ω.val (hneut Ω)
  · -- facet constancy
    intro Ω Fb hsub
    apply exists_isIso_neutral_of_unramified_eq hext
    change (model Ω).neutral.baseChangeUnramified.integralPoints =
      (model ⟨Fb.val, Or.inr Fb.property⟩).neutral.baseChangeUnramified.integralPoints
    rw [hneut Ω, hneut ⟨Fb.val, Or.inr Fb.property⟩]
    change _ ⊓ C.pointwiseFixer (e '' Ω.val) = _ ⊓ C.pointwiseFixer (e '' Fb.val)
    obtain ⟨g, Fa, ⟨x, hx⟩, hF⟩ := Fb.property
    subst hx
    have hΩ : Ω.val = P.toValuationBuildingData.translatedApartmentMap g ''
        (AffineRootSystem.facet P.toValuationBuildingData.affineRoots x ∩
          P.toValuationBuildingData.translatedApartmentMap g ⁻¹' Ω.val) := by
      ext y
      constructor
      · intro hy
        have hy' := hsub hy
        rw [hF] at hy'
        obtain ⟨w, hw, rfl⟩ := hy'
        exact ⟨w, ⟨hw, hy⟩, rfl⟩
      · rintro ⟨w, ⟨-, hw⟩, rfl⟩
        exact hw
    have hF' : Fb.val = P.toValuationBuildingData.translatedApartmentMap g ''
        AffineRootSystem.facet P.toValuationBuildingData.affineRoots x := hF
    rw [hΩ, hF', image_translatedApartmentMap e a he_smul he_apt,
      image_translatedApartmentMap e a he_smul he_apt]
    have hFb : P.toValuationBuildingData.IsBoundedSubset
        (AffineRootSystem.facet P.toValuationBuildingData.affineRoots x) :=
      isBoundedSubset_of_isFacet_of_satisfiesApartmentAxioms _ h5 ⟨x, rfl⟩
    have hne := BuildingModelIndex.nonempty_of_eq_translatedApartmentMap hΩ
    have hxF : (a '' AffineRootSystem.facet P.toValuationBuildingData.affineRoots x).Nonempty :=
      ⟨a x, x, AffineRootSystem.mem_facet_self _ _, rfl⟩
    have hsubF : a '' AffineRootSystem.facet P.toValuationBuildingData.affineRoots x ⊆
        AffineRootSystem.facet C.affineRoots (a x) := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : w ∈ a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) := by
        rw [hfacet x]
        exact hw
      exact hw'
    have hsubΩ : a '' (AffineRootSystem.facet P.toValuationBuildingData.affineRoots x ∩
        P.toValuationBuildingData.translatedApartmentMap g ⁻¹' Ω.val) ⊆
        AffineRootSystem.facet C.affineRoots (a x) :=
      (Set.image_mono Set.inter_subset_left).trans hsubF
    refine hroot F G C (unramifiedZeroDatumOfParahoric P) _ _ _ (hne.image a)
      (bddAbove_image_image a fun f => (hFb f).mono (Set.image_mono Set.inter_subset_left))
      hxF (bddAbove_image_image a hFb) ?_
    intro ψ hψ
    exact forall_nonneg_iff_of_subset_facet hsubΩ hsubF (hne.image a) hxF ψ hψ
  · -- closure invariance
    intro g Ωa hne hb
    apply exists_isIso_neutral_of_unramified_eq hext
    rw [hneut, hneut]
    change _ ⊓ C.pointwiseFixer
        (e '' (P.toValuationBuildingData.translatedApartmentMap g '' Ωa)) =
      _ ⊓ C.pointwiseFixer (e '' (P.toValuationBuildingData.translatedApartmentMap g ''
        apartmentClosure P.toValuationBuildingData Ωa))
    rw [image_translatedApartmentMap e a he_smul he_apt,
      image_translatedApartmentMap e a he_smul he_apt]
    apply inf_eq_inf_of_le_of_inf_eq
      (UnramifiedZeroDatum.zeroPoints_le_unramifiedCharacterValuationKernel
        (unramifiedZeroDatumOfParahoric P))
    have hc := hclos F G C (rationalExtend F (inertiaFixedField F) G g) (a '' Ωa)
      (hne.image a) (bddAbove_image_image a hb)
    have hs1 : (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
          (a '' Ωa) ⊆
        (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
          (a '' apartmentClosure P.toValuationBuildingData Ωa) :=
      Set.image_mono (Set.image_mono
        (@subset_closure _ (affineApartmentTopology P.toValuationBuildingData) Ωa))
    have hs2 : (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
          (a '' apartmentClosure P.toValuationBuildingData Ωa) ⊆
        (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
          @closure C.Apartment (unramifiedApartmentTopology C) (a '' Ωa) :=
      Set.image_mono (image_subset_closure_image a subset_rfl)
    apply le_antisymm
    · rw [hc]
      exact inf_le_inf_left _ (unramifiedPointwiseFixer_anti hs2)
    · exact inf_le_inf_left _ (unramifiedPointwiseFixer_anti hs1)
  · -- simply connected case
    intro Ω hSC
    have hK : IsSimplyConnected (baseChanged F (inertiaFixedField F) G) :=
      isSimplyConnectedFieldExtension F (inertiaFixedField F) G hSC
    have hE := UnramifiedZeroDatum.zeroPoints_eq_top_of_isSimplyConnected
      (unramifiedZeroDatumOfParahoric P) hK
    have hle : (model Ω).full.baseChangeUnramified.integralPoints ≤
        (model Ω).neutral.baseChangeUnramified.integralPoints := by
      rw [hfull Ω, hneut Ω, hE, top_inf_eq]
      exact inf_le_right
    obtain ⟨ψ⟩ := nonempty_hom_of_unramified_le hext (model Ω).full (model Ω).neutral
      (model Ω).full_smooth hle
    exact isIso_hom_of_hom (model Ω).inclusion ψ

end Langlands.BruhatTits.IntegralModels
