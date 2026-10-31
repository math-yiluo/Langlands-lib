import Langlands.Representation.Geometric.ParabolicOrbitNormalizedCoefficient
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.Equivalences

/-! Transport from the actual orbit coefficient to refined smooth induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open CategoryTheory GeneralLinear Induction
universe uG uH uV uW

section Pullback
variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- Pull back smooth actions along a continuous homomorphism. -/
def smoothPullbackFunctor (φ : H →* G) (hφ : Continuous φ) :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H where
  obj A := SmoothRep.of (A.representation.comp φ) (isSmooth_comp φ hφ A.isSmooth)
  map f := SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom f).toLinearMap
      isIntertwining' h := (SmoothRep.hom f).isIntertwining' (φ h) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Equality relabeling is continuous pullback along the actual subgroup identification. -/
theorem subgroupEqualityFunctor_eq_pullback (H K : Subgroup G) (h : H = K) :
    subgroupEqualityFunctor.{uG, uV} H K h =
      smoothPullbackFunctor (MulEquiv.subgroupCongr h.symm).toMonoidHom
        (continuous_subtype_val.subtype_mk _) := by
  subst K
  rfl

end Pullback

section Induction
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Relabel the inducing subgroup while retaining the same ambient functions. -/
def compactInducedSubgroupCongr (H K : Subgroup G) (h : H = K)
    (σ : Representation ℂ K V) :
    (compactInduced H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom)).Equiv
      (compactInduced K σ) := by
  subst K
  exact Representation.Equiv.refl _

/-- Relabel smooth induction along equality of the actual inducing subgroups. -/
def smoothInducedSubgroupCongr (H K : Subgroup G) (h : H = K)
    (σ : Representation ℂ K V) :
    (smoothInduced H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom)).Equiv
      (smoothInduced K σ) := by
  subst K
  exact Representation.Equiv.refl _

@[simp] theorem smoothInducedSubgroupCongr_eval (H K : Subgroup G) (h : H = K)
    (σ : Representation ℂ K V)
    (f : SmoothFunctions H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom)) (g : G) :
    eval K σ (smoothInducedSubgroupCongr H K h σ f) g =
      eval H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom) f g := by
  subst K
  rfl

@[simp] theorem compactInducedSubgroupCongr_eval (H K : Subgroup G) (h : H = K)
    (σ : Representation ℂ K V)
    (f : CompactFunctions H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom)) (g : G) :
    eval K σ (compactInducedSubgroupCongr H K h σ f).val g =
      eval H (σ.comp (MulEquiv.subgroupCongr h).toMonoidHom) f.val g := by
  subst K
  rfl

/-- Compact-to-smooth induction for a compact actual coset space. -/
def compactSmoothEquiv (H : Subgroup G) [CompactSpace (LeftQuotient H)]
    (σ : Representation ℂ H V) :
    (compactInduced H σ).Equiv (smoothInduced H σ) :=
  (compactInclusion H σ).ofBijective (compactInclusion_bijective_of_compactSpace H σ)

@[simp] theorem compactSmoothEquiv_eval (H : Subgroup G)
    [CompactSpace (LeftQuotient H)] (σ : Representation ℂ H V)
    (f : CompactFunctions H σ) (g : G) :
    eval H σ (compactSmoothEquiv H σ f) g = eval H σ f.val g := rfl

end Induction

section Coefficient
variable (F : Type uG) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] {n : ℕ} [LocallyCompactSpace (GeneralLinear n F)]
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The genuine section action with the actual forward quotient-integration ratio. -/
abbrev parabolicOrbitIntegratedCoefficient (χ : B.Levi F →* ℂˣ)
    (ρ : Representation ℂ (B.Levi F) V) :=
  twist (Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F B C w))
    (parabolicOrbitNestedCoefficientAction F B C w χ ρ)

/-- The actual quotient coefficient map, with the section actions explicitly typed. -/
def parabolicOrbitIntegratedCoefficientMap (χ : B.Levi F →* ℂˣ)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) :
    (parabolicOrbitIntegratedCoefficient F B C w χ ρ).IntertwiningMap
      (parabolicOrbitIntegratedCoefficient F B C w χ τ) :=
  twistIntertwining
    (Jacquet.complexCharacter (parabolicOrbitStagesHaarRatio F B C w))
    ({ toLinearMap := Representation.Coinvariants.map
          (parabolicOrbitNestedCoefficient F B C w χ ρ)
          (parabolicOrbitNestedCoefficient F B C w χ τ)
          (parabolicOrbitNestedCoefficientMap F B C w χ f)
       isIntertwining' l := LinearMap.ext fun z =>
         parabolicOrbitNestedCoefficientAction_natural F B C w χ f l z } :
      (parabolicOrbitNestedCoefficientAction F B C w χ ρ).IntertwiningMap
        (parabolicOrbitNestedCoefficientAction F B C w χ τ))

end Coefficient
end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open CategoryTheory GeneralLinear Geometric Induction
universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : MinimalRepresentatives B C) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
  (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The literal geometric piece has the explicit inverse-conjugation pullbacks. -/
theorem geometricPieceFunctor_eq_pullback :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    geometricPieceFunctor.{uF, uV} T B C w.val S R hS.2.1 hR.2.1 =
      T.normalizedRefinedJacquetFunctor B S ⋙
        smoothPullbackFunctor (MulEquiv.subgroupCongr hS.2.1).toMonoidHom
          (continuous_subtype_val.subtype_mk _) ⋙
        intersectionTransportFunctor F.Carrier B C w.val ⋙
        smoothPullbackFunctor (MulEquiv.subgroupCongr hR.2.1.symm).toMonoidHom
          (continuous_subtype_val.subtype_mk _) ⋙
        T.normalizedRefinedInductionFunctor C R ⋙ SmoothRep.toRep := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  unfold geometricPieceFunctor
  rw [subgroupEqualityFunctor_eq_pullback, subgroupEqualityFunctor_eq_pullback]

/-- Move the target inverse half through induction, identify the normalized
coefficient, and use compactness of the actual refined parabolic quotient. -/
def parabolicOrbitInductionTransportEquiv
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    (twist (Jacquet.inverseHalfCharacter (T.leviModulus C))
      (compactInduced (parabolicOrbitStagesQuotient F.Carrier B C w.val)
        (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ))).Equiv
      (T.normalizedRefinedInduced C R
        (refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
          (T.normalizedRefinedJacquet B S ρ))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let K := parabolicOrbitStagesQuotient F.Carrier B C w.val
  have hK : K = refinedParabolic F.Carrier C R :=
    (parabolicOrbitStages_comap_section F.Carrier B C w.val).trans hR.1
  have : CompactSpace (LeftQuotient K) := by
    rw [hK]
    exact Parabolic.refinedParabolicQuotientCompact F T C R
  let χ : SmoothCharacter ℂ (C.Levi F.Carrier) :=
    ⟨Jacquet.inverseHalfCharacter (T.leviModulus C),
      Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus C)⟩
  let e₁ := compactInductionTwistEquiv K χ
    (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ)
  let e₂ := compactSmoothEquiv K (T.parabolicOrbitNormalizedNestedCoefficient B C w ρ)
  let e₃ := smoothInducedEquiv K
    (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ)
  let e₄ := smoothInducedSubgroupCongr K (refinedParabolic F.Carrier C R) hK
    (twist (T.refinedParabolicHalfModulus C R)
      ((refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
        (T.normalizedRefinedJacquet B S ρ)).comp (refinedLeviProjection F.Carrier C R)))
  exact ((e₁.trans e₂).trans e₃).trans e₄

/-- Evaluation of the transport is coefficient transport after multiplication
by the target inverse half modulus. -/
theorem parabolicOrbitInductionTransportEquiv_eval
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ (f : CompactFunctions (parabolicOrbitStagesQuotient F.Carrier B C w.val)
      (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ))
      (x : C.Levi F.Carrier),
    eval _ _ (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR ρ f) x =
      T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ
        ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) •
          eval _ _ f.val x) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro f x
  let K := parabolicOrbitStagesQuotient F.Carrier B C w.val
  let σ := parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ
  let τ := twist (T.refinedParabolicHalfModulus C R)
    ((refinedIntersectionTransport F.Carrier B C w.val S R hS.2.1 hR.2.1
      (T.normalizedRefinedJacquet B S ρ)).comp (refinedLeviProjection F.Carrier C R))
  have hK : K = refinedParabolic F.Carrier C R :=
    (parabolicOrbitStages_comap_section F.Carrier B C w.val).trans hR.1
  have : CompactSpace (LeftQuotient K) := by
    rw [hK]
    exact Parabolic.refinedParabolicQuotientCompact F T C R
  let χ : SmoothCharacter ℂ (C.Levi F.Carrier) :=
    ⟨Jacquet.inverseHalfCharacter (T.leviModulus C),
      Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus C)⟩
  let e₁ := compactInductionTwistEquiv K χ σ
  let e₂ := compactSmoothEquiv K (T.parabolicOrbitNormalizedNestedCoefficient B C w ρ)
  let e₃ := smoothInducedEquiv K
    (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ)
  exact (smoothInducedSubgroupCongr_eval K (refinedParabolic F.Carrier C R) hK
    τ (e₃ (e₂ (e₁ f))) x).trans (by rfl)

/-- The induction transport commutes with every original source intertwiner. -/
theorem parabolicOrbitInductionTransportEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    ∀ z : CompactFunctions (parabolicOrbitStagesQuotient F.Carrier B C w.val)
      (parabolicOrbitIntegratedCoefficient F.Carrier B C w.val (T.leviHalfModulus B) ρ),
    T.parabolicOrbitInductionTransportEquiv B C w S R hS hR τ
      (compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w.val)
        (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w.val
          (T.leviHalfModulus B) f) z) =
      T.normalizedRefinedInducedMap C R
        (refinedIntersectionTransportMap F.Carrier B C w.val S R hS.2.1 hR.2.1
          (T.normalizedRefinedJacquetMap B S f))
        (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR ρ z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  intro z
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change eval _ _ (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR τ
      (compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w.val)
        (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w.val
          (T.leviHalfModulus B) f) z)) x =
    T.normalizedRefinedJacquetMap B S f
      (eval _ _ (T.parabolicOrbitInductionTransportEquiv B C w S R hS hR ρ z) x)
  have hτ := T.parabolicOrbitInductionTransportEquiv_eval B C w S R hS hR τ
    (compactInducedMap (parabolicOrbitStagesQuotient F.Carrier B C w.val)
      (parabolicOrbitIntegratedCoefficientMap F.Carrier B C w.val
        (T.leviHalfModulus B) f) z) x
  have hρ := T.parabolicOrbitInductionTransportEquiv_eval B C w S R hS hR ρ z x
  refine Eq.trans hτ (Eq.trans ?_ (congrArg (T.normalizedRefinedJacquetMap B S f) hρ).symm)
  change T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR τ
      ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) •
        Representation.Coinvariants.map _ _
          (parabolicOrbitNestedCoefficientMap F.Carrier B C w.val (T.leviHalfModulus B) f)
          (eval _ _ z.val x)) =
    T.normalizedRefinedJacquetMap B S f
      (T.parabolicOrbitNormalizedNestedCoefficientEquiv B C w S R hS hR ρ
        ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) • eval _ _ z.val x))
  simpa only [map_smul] using
    T.parabolicOrbitNormalizedNestedCoefficientEquiv_natural B C w S R hS hR f
      ((Jacquet.inverseHalfCharacter (T.leviModulus C) x : ℂ) • eval _ _ z.val x)

end Langlands.PadicField.TopologicalData
