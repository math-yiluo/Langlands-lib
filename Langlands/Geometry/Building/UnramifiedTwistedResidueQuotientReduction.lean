import Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientStatement
import Langlands.Geometry.Building.SharpChamberClosureOrbit
import Langlands.Geometry.Building.UnramifiedTwistedPointStabilizer
import Langlands.Geometry.Building.UnramifiedZeroPointsGaloisStability
import Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescentStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalChamberFixation
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.BruhatTits.IntegralModels.Transport.Package
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Reduction of the twisted residue quotient to model, radical and descent inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace UnramifiedTwistedResidueQuotient

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom H.X.hom]

/-- The same integral model with its generic identification composed with the inner
automorphism of `z`. -/
abbrev conjModel {R : Type u} [CommRing R] [IsDomain R] [Algebra R (inertiaFixedField F)]
    [IsFractionRing R (inertiaFixedField F)]
    (N : IntegralModel R (inertiaFixedField F) H) (z : rationalPoints H) :
    IntegralModel R (inertiaFixedField F) H where
  group := N.group
  genericIso := N.genericIso ≪≫ H.innerIso z

omit [IsAffineHom H.X.hom] in
theorem conjModel_integralPointMap {R : Type u} [CommRing R] [IsDomain R]
    [Algebra R (inertiaFixedField F)] [IsFractionRing R (inertiaFixedField F)]
    (N : IntegralModel R (inertiaFixedField F) H) (z : rationalPoints H)
    (s : N.integralSections) :
    (conjModel N z).integralPointMap s = z * N.integralPointMap s * z⁻¹ := by
  change rationalPoints.map (N.genericIso.hom ≫ (H.innerIso z).hom)
      (baseChangeSectionHom _ N.group s) = _
  have h : rationalPoints.map (N.genericIso.hom ≫ (H.innerIso z).hom) =
      (rationalPoints.map (H.innerIso z).hom).comp (rationalPoints.map N.genericIso.hom) := by
    ext y
    simp [rationalPoints.map_apply]
  rw [h, rationalPoints_map_innerIso]
  rfl

set_option maxHeartbeats 1600000 in
/-- Translating a smooth model whose integral points are `G(K)^0 ∩ G(K)_{g x}` back to the
apartment point `x`, KP 8.4.12 (through `unramifiedRadicalPreimage_le_zeroFixer_facet`) bounds
its radical preimage by elements fixing pointwise every translated chamber through `g x`. -/
theorem radicalPreimage_fixes_facet
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (B : MaximalUnramified.BuildingData F H) (E : UnramifiedZeroDatum F H)
    {g : rationalPoints H} {x : B.Apartment} {y : B.ReducedBuilding}
    (hx : g • B.apartmentMap x = y)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H) (hN : N.IsSmooth)
    (hNP : N.integralPoints = E.zeroPoints ⊓ B.fixer y)
    {U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (i : U ⟶ N.specialFibre) (hi : IsUnipotentRadical i)
    {x₀ : B.Apartment} (hcl : x ∈ AffineRootSystem.facetClosure B.affineRoots x₀)
    {p : rationalPoints H}
    (hp : p ∈ ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap) :
    ∀ z ∈ AffineRootSystem.facet B.affineRoots x₀,
      p • (g • B.apartmentMap z) = g • B.apartmentMap z := by
  have hN' : (conjModel N g⁻¹).integralPoints =
      E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' {x}) := by
    ext p'
    constructor
    · rintro ⟨s, rfl⟩
      rw [conjModel_integralPointMap]
      have hs : N.integralPointMap s ∈ E.zeroPoints ⊓ B.fixer y := hNP ▸ ⟨s, rfl⟩
      refine ⟨E.normal_zeroPoints.conj_mem _ hs.1 _, ?_⟩
      apply B.apartment.mem_pointwiseFixer.mpr
      rintro _ ⟨_, rfl, rfl⟩
      have h2 : N.integralPointMap s • y = y := B.mem_fixer.mp hs.2
      rw [inv_inv, mul_smul, mul_smul, hx, h2, ← hx, inv_smul_smul]
    · rintro ⟨hz, hf⟩
      have hmem : g * p' * g⁻¹ ∈ N.integralPoints := by
        rw [hNP]
        refine ⟨E.normal_zeroPoints.conj_mem _ hz _, B.mem_fixer.mpr ?_⟩
        have h3 := B.apartment.mem_pointwiseFixer.mp hf (B.apartmentMap x) ⟨x, rfl, rfl⟩
        rw [← hx, mul_smul, mul_smul, inv_smul_smul]
        change g • (p' • B.apartmentMap x) = g • B.apartmentMap x
        rw [h3]
      obtain ⟨s, hs⟩ := hmem
      exact ⟨s, by rw [conjModel_integralPointMap, hs]; group⟩
  have hmem : g⁻¹ * p * g ∈ ((rationalPoints.map i).range.comap
      (conjModel N g⁻¹).reduction).map (conjModel N g⁻¹).integralPointMap := by
    obtain ⟨s, hs, rfl⟩ := hp
    exact ⟨s, hs, by rw [conjModel_integralPointMap, inv_inv]⟩
  have hfix := (unramifiedRadicalPreimage_le_zeroFixer_facet B E hgen hcl
    (conjModel N g⁻¹) hN hN' i hi hmem).2
  intro z hz
  have h4 : (g⁻¹ * p * g) • B.apartmentMap z = B.apartmentMap z :=
    B.apartment.mem_pointwiseFixer.mp hfix (B.apartmentMap z) ⟨z, hz, rfl⟩
  calc p • (g • B.apartmentMap z) = g • ((g⁻¹ * p * g) • B.apartmentMap z) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • B.apartmentMap z := by rw [h4]

set_option maxHeartbeats 1600000 in
/-- Coefficient conjugation preserves the zero subgroup, stated over `inertiaFixedField F`. -/
theorem rationalConjugate_mem_zeroPoints'
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    {p : rationalPoints (baseChanged F (inertiaFixedField F) G)} (hp : p ∈ E.zeroPoints) :
    rationalConjugate F (inertiaFixedField F) G σ p ∈ E.zeroPoints :=
  UnramifiedZeroDatum.rationalConjugate_mem_zeroPoints F G E σ hp

/-- Twisted conjugation preserves `G(K)^0 ∩ G(K)_y` at a twisted-fixed point `y`. -/
theorem twisted_mem_zeroPoints_fixer
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (A : MaximalUnramified.SemilinearApartmentData B)
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
    (y : B.ReducedBuilding)
    (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, c σ • A.action σ y = y)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    {p : rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hp : p ∈ E.zeroPoints ⊓ B.fixer y) :
    c σ * rationalConjugate F (inertiaFixedField F) G σ p * (c σ)⁻¹ ∈
      E.zeroPoints ⊓ B.fixer y := by
  refine ⟨E.normal_zeroPoints.conj_mem _
    (rationalConjugate_mem_zeroPoints' G E σ hp.1) _, ?_⟩
  apply B.mem_fixer.mpr
  have h := A.twistedAction_smul c hc σ p y
  have hty : A.twistedAction c hc σ y = y := by
    rw [MaximalUnramified.SemilinearApartmentData.twistedAction_apply]
    exact hy σ
  have hpy : p • y = y := B.mem_fixer.mp hp.2
  rw [hpy, hty, twistedRationalConjugateAction_apply] at h
  exact h.symm

end UnramifiedTwistedResidueQuotient

private instance residueQuotientReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

set_option maxHeartbeats 6400000 in
open UnramifiedTwistedResidueQuotient in
/-- The conclusion of `UnramifiedTwistedResidueQuotientStatement` for an arbitrary supplied
building datum, semilinear apartment datum and twisted-fixed point, from the parahoric model
statement, KP 8.4.12 and the Frobenius descent of the reductive quotient. -/
theorem exists_twistedResidueQuotient_of_inputs
    (hM : UnramifiedParahoricModelStatement.{u})
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (hdesc : UnramifiedTwistedReductiveQuotientDescentStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (A : MaximalUnramified.SemilinearApartmentData B)
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
    (hfin : ∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1)
    (y : B.ReducedBuilding)
    (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, c σ • A.action σ y = y) :
    letI : Fintype 𝓀[F] := Fintype.ofFinite _
    letI : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
      (residueToFixedField F).toAlgebra
    letI : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
      fixedFieldResidueIsAlgClosure F
    ∀ φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      (∀ x : fixedFieldIntegers F,
        IsLocalRing.residue (fixedFieldIntegers F)
            (Langlands.GroupScheme.Descent.FiniteUnramified.fixedFieldIntegerAut F φ x) =
          IsLocalRing.residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F]) →
      ∃ R : GroupScheme (Spec (CommRingCat.of 𝓀[F])), IsConnectedReductive R ∧
        ∃ (P : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
          (q : P →* (Over.mk (𝟙 (Spec (CommRingCat.of
              (IsLocalRing.ResidueField (fixedFieldIntegers F))))) ⟶
            ((GroupScheme.baseChange (algebraBaseMap 𝓀[F]
              (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj R).X))
          (θP : P → P),
          P ≤ B.fixer y ∧
          Function.Surjective q ∧
          (∀ g : P, (θP g : rationalPoints (baseChanged F (inertiaFixedField F) G)) =
            c φ * rationalConjugate F (inertiaFixedField F) G φ g * (c φ)⁻¹) ∧
          (∀ g : P, q (θP g) =
            descentBasePoint
              (algebraBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
              (galoisBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
                (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                  (IsLocalRing.ResidueField (fixedFieldIntegers F))))
              (galoisBaseMap_over 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
                (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                  (IsLocalRing.ResidueField (fixedFieldIntegers F))))
              R (q g)) ∧
          (∀ Y : Set B.ReducedBuilding, B.HasChamberClosurePresentation Y y →
            ∀ g : P, q g = 1 →
              ((g : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y = Y) ∧
          (∀ Y Y' : Set B.ReducedBuilding,
            B.HasChamberClosurePresentation Y y → B.HasChamberClosurePresentation Y' y →
            ∃ h : P, Y' = ((h : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y) := by
  intro φ hφ
  obtain ⟨g, x, hx⟩ := B.exists_smul_apartmentMap y
  obtain ⟨Dm, -, hDm⟩ := hM F G B E g {x} (Set.singleton_nonempty x) (fun f => by
    rw [Set.image_singleton]
    exact bddAbove_singleton)
  have hP : Dm.neutral.integralPoints = E.zeroPoints ⊓ B.fixer y := by
    rw [hDm, Set.image_singleton, hx]
    exact congrArg (E.zeroPoints ⊓ ·) (B.apartment.pointwiseFixer_singleton y)
  have : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  have : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  obtain ⟨Q, hQ⟩ := SpecialFibreQuotientData.exists_isReductiveQuotient Dm
  have hstab : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (p),
      p ∈ Dm.neutral.integralPoints →
        c σ * rationalConjugate F (inertiaFixedField F) G σ p * (c σ)⁻¹ ∈
          Dm.neutral.integralPoints := fun σ p hp => by
    rw [hP] at hp ⊢
    exact twisted_mem_zeroPoints_fixer G E B A c hc y hy σ hp
  obtain ⟨R, hR, e, he⟩ := hdesc F G c hc hfin Dm hstab Q hQ φ hφ
  obtain ⟨x₀, hreg, hcl⟩ := (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs).exists_regularPoint_closure x
  have hY₀ : B.HasChamberClosurePresentation
      ((fun z => g • B.apartmentMap z) '' AffineRootSystem.facet B.affineRoots x₀) y :=
    ⟨g, x₀, x, hreg, rfl, hcl, hx⟩
  have hker : ∀ p : Dm.neutral.integralPoints, Q.parahoricReduction p = 1 →
      ((p : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) ''
        ((fun z => g • B.apartmentMap z) '' AffineRootSystem.facet B.affineRoots x₀) =
        (fun z => g • B.apartmentMap z) '' AffineRootSystem.facet B.affineRoots x₀ := by
    intro p hp
    have hp' : p ∈ Q.positivePoints.subgroupOf Dm.neutral.integralPoints := by
      rw [← Q.ker_parahoricReduction hQ.2.1]
      exact hp
    have hfix := radicalPreimage_fixes_facet hgen B E hx Dm.neutral Dm.neutral_smooth hP
      Q.radicalInclusion hQ.1 hcl (Subgroup.mem_subgroupOf.mp hp')
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, (hfix z hz).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, hfix z hz⟩
  have htrans : ∀ Y Y' : Set B.ReducedBuilding,
      B.HasChamberClosurePresentation Y y → B.HasChamberClosurePresentation Y' y →
      ∃ h : Dm.neutral.integralPoints,
        Y' = ((h : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y := by
    intro Y Y' hY hY'
    obtain ⟨h, hh, hhY⟩ := E.exists_zeroPoints_fixer_smul_chamber_eq B hY hY'
    exact ⟨⟨h, by rw [hP]; exact hh⟩, hhY.symm⟩
  refine ⟨R, hR, Dm.neutral.integralPoints,
    (rationalPoints.map e.inv).comp Q.parahoricReduction,
    fun p => ⟨_, hstab φ p p.2⟩, ?_, ?_, fun p => rfl, fun p => he p (hstab φ p p.2), ?_,
    htrans⟩
  · rw [hP]
    exact inf_le_right
  · intro z
    obtain ⟨p, hp⟩ := Q.parahoricReduction_surjective hQ.1 hQ.2.1 (rationalPoints.map e.hom z)
    exact ⟨p, by rw [MonoidHom.comp_apply, hp, rationalPoints_map_inv_hom]⟩
  · intro Y hY p hp
    refine B.kernel_stabilizes_of_transitive Dm.neutral.integralPoints
      ((rationalPoints.map e.inv).comp Q.parahoricReduction) hY₀ (fun p' hp' => hker p' ?_)
      htrans Y hY p hp
    have h1 := congrArg (rationalPoints.map e.hom) hp'
    rwa [MonoidHom.comp_apply, rationalPoints_map_hom_inv, map_one] at h1

set_option maxHeartbeats 1600000 in
/-- The twisted residue quotient follows from the parahoric model statement, the upstairs
radical root generation statement (KP 8.4.12) and the Frobenius descent of the reductive
quotient. -/
theorem unramifiedTwistedResidueQuotient_of_inputs
    (hM : UnramifiedParahoricModelStatement.{u})
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (hdesc : UnramifiedTwistedReductiveQuotientDescentStatement.{u}) :
    UnramifiedTwistedResidueQuotientStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hfin y hy
  exact exists_twistedResidueQuotient_of_inputs hM hgen hdesc G
    (Kottwitz.nonempty_unramifiedZeroDatum_baseChanged F G hG).some _ _ c hc hfin y hy

/-- The twisted residue quotient statement follows from the parahoric model statement, the
upstairs radical root generation statement (KP 8.4.12) and the Frobenius descent of the
reductive quotient of a twisted-stable model. -/
def UnramifiedTwistedResidueQuotientInputsReductionStatement : Prop :=
  UnramifiedParahoricModelStatement.{u} →
    UnramifiedUpstairsRadicalRootGenerationStatement.{u} →
      UnramifiedTwistedReductiveQuotientDescentStatement.{u} →
        UnramifiedTwistedResidueQuotientStatement.{u}

/-- The reduction is proved. -/
theorem unramifiedTwistedResidueQuotientInputsReduction :
    UnramifiedTwistedResidueQuotientInputsReductionStatement.{u} :=
  fun hM hgen hdesc => unramifiedTwistedResidueQuotient_of_inputs hM hgen hdesc

end Langlands.Geometry.Building
