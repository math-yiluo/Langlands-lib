import Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement
import Langlands.Representation.Induction.CharacterTwistProof

/-! Natural character-localized compact induction in split stages. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Induction.SplitStagesCharacter

open MeasureTheory MeasureTheory.Measure QuotientIntegration HarmonicAnalysis
open SplitKernelLocalization

universe uG uL uV uW

section Intersection

variable {G : Type uG} [Group G] {L : Type uL} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Exchange the two intersection realizations without changing quotient classes. -/
def ordinaryIntersectionEquiv (r : G →* L) (H : Subgroup G)
    (σ : Representation ℂ H V) :
    Jacquet.Coinvariants σ (kernelIntersection r H) ≃ₗ[ℂ]
      Representation.Coinvariants (σ.comp (r.ker.subtype.subgroupComap H)) where
  toLinearMap := Jacquet.lift σ (kernelIntersection r H)
    (Representation.Coinvariants.mk _) (fun a => LinearMap.ext fun v => by
      exact Representation.Coinvariants.mk_self_apply _
        (intersectionEquiv r H a) v)
  invFun := Representation.Coinvariants.lift _ (Jacquet.mk σ (kernelIntersection r H))
    (fun i => LinearMap.ext fun v =>
      Jacquet.mk_apply_subgroup σ (kernelIntersection r H)
        ((intersectionEquiv r H).symm i) v)
  left_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => rfl
  right_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => rfl

@[simp] theorem ordinaryIntersectionEquiv_mk (r : G →* L) (H : Subgroup G)
    (σ : Representation ℂ H V) (v : V) :
    ordinaryIntersectionEquiv r H σ (Jacquet.mk σ (kernelIntersection r H) v) =
      Representation.Coinvariants.mk (σ.comp (r.ker.subtype.subgroupComap H)) v := rfl

end Intersection

section Comparison

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
variable (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
variable (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
variable (θ : SmoothCharacter ℂ r.ker)
variable (hθ : SectionInvariant r s θ.toMonoidHom)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ)

local notation "K" => P.comap s
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "σP" => σ.comp φ
local notation "I" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rP)) HP
local notation "A" => kernelIntersection rP HP
local notation "θP" => SmoothCharacter.toMonoidHom (kernelCharacter r s hrs P hker θ)
local notation "η" => intersectionCharacter rP θP HP
local notation "hSI" => section_mem s P H hsH
local notation "hθP" => sectionInvariant r s hrs P hker θ hθ
local notation "ξ" => characterExtension r s hrs θ.toMonoidHom hθ
local notation "ξHP" => MonoidHom.comp (MonoidHom.comp ξ H.subtype) φ

/-- The actual inverse extension, whose open kernel is unchanged. -/
def inverseExtension : SmoothCharacter ℂ G where
  toMonoidHom := ξ⁻¹
  isOpen_ker := by
    convert (smoothCharacterExtension r s hrs hr hs θ hθ).isOpen_ker using 1
    ext g
    exact inv_eq_one

local notation "ε" => inverseExtension r s hrs hr hs θ hθ
local notation "σt" => twist (MonoidHom.comp (SmoothCharacter.toMonoidHom ε) H.subtype) σ
local notation "σtP" => MonoidHom.comp σt φ

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TopologicalSpace L] [IsTopologicalGroup L] in
/-- The ambient extension restricts to the exact nested intersection character. -/
theorem extension_intersection (a : A) : ξHP a = η a := by
  exact characterExtension_kernel r s hrs θ.toMonoidHom hθ
    (splitStagesKernelEquiv r s hrs P hker (intersectionToKernel rP HP a))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TopologicalSpace L] [IsTopologicalGroup L] in
/-- The ambient extension is one on precisely the section elements used here. -/
theorem extension_subgroupSection (l : K) :
    ξHP (subgroupSection sP HP hSI l) = 1 :=
  characterExtension_section r s hrs θ.toMonoidHom hθ l

/-- Identity on vectors identifies the localized coefficient with the ordinary
coefficient of the inverse-extended twist, retaining its section action. -/
def coefficientUntwist :
    (subgroupAction rP sP θP hθP HP hSI σP).Equiv
      (splitKernelCoefficientAction rP sP HP hSI σtP) where
  toLinearEquiv :=
    (twistSectionEquiv (subgroupRetraction rP HP) (subgroupSection sP HP hSI)
      η (subgroupInvariant rP sP θP hθP HP hSI) ξHP
      (extension_intersection r s hrs P H hker hHP θ hθ)
      (extension_subgroupSection r s hrs P H hHP hsH θ hθ) σP).toLinearEquiv.trans
        (ordinaryIntersectionEquiv rP HP σtP)
  isIntertwining' l := by
    apply Jacquet.Localization.hom_ext
    ext v
    change Representation.Coinvariants.mk (MonoidHom.comp σtP ((rP).ker.subtype.subgroupComap HP))
        (σP (subgroupSection sP HP hSI l) v) =
      Representation.Coinvariants.mk (MonoidHom.comp σtP ((rP).ker.subtype.subgroupComap HP))
        (σtP (splitKernelSection sP HP hSI l) v)
    congr 1
    change σ (φ (subgroupSection sP HP hSI l)) v =
      ((ξ (s (l : L)))⁻¹ : ℂˣ) • σ (φ (subgroupSection sP HP hSI l)) v
    rw [characterExtension_section]
    simp

omit [T2Space G] [LocallyCompactSpace G] [IsTopologicalGroup L] in
@[simp] theorem coefficientUntwist_mk (v : V) :
    coefficientUntwist r s hrs hr hs P H hker hHP hsH θ hθ σ
        (Jacquet.Localization.mk σP A η v) =
      Representation.Coinvariants.mk (MonoidHom.comp σtP ((rP).ker.subtype.subgroupComap HP)) v := rfl

include hσ in
omit [T2Space G] [LocallyCompactSpace G] [IsTopologicalGroup L] in
theorem twisted_smooth : IsSmooth σt := by
  apply (isSmooth_twist_iff _ σ _).mpr hσ
  exact IsOpen.preimage continuous_subtype_val (SmoothCharacter.isOpen_ker ε)


omit [T2Space G] [LocallyCompactSpace G] [IsTopologicalGroup L] in
@[simp] theorem coefficientUntwist_symm_mk (v : V) :
    (coefficientUntwist r s hrs hr hs P H hker hHP hsH θ hθ σ).symm
        (Representation.Coinvariants.mk (MonoidHom.comp σtP ((rP).ker.subtype.subgroupComap HP)) v) =
      Jacquet.Localization.mk σP A η v := by
  apply (coefficientUntwist r s hrs hr hs P H hker hHP hsH θ hθ σ).injective
  exact (coefficientUntwist r s hrs hr hs P H hker hHP hsH θ hθ σ).apply_symm_apply _

/-- Untwist the source localization and then multiply actual compact functions
by the inverse extension. -/
def inductionUntwist :
    (localizedAction r s θ.toMonoidHom hθ (compactInduced H σ)).Equiv
      (((compactInduced H σt).toCoinvariants r.ker).comp s) :=
  (extensionTwistEquiv r s hrs θ.toMonoidHom hθ (compactInduced H σ)).trans
    (restrictAlongEquiv s (normalCoinvariantsEquiv r.ker
      (compactInductionTwistEquiv H ε σ)))

omit [T2Space G] [LocallyCompactSpace G] [IsTopologicalGroup L] in
@[simp] theorem inductionUntwist_mk (f : CompactFunctions H σ) :
    inductionUntwist r s hrs hr hs H θ hθ σ
        (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f) =
      Representation.Coinvariants.mk ((compactInduced H σt).comp r.ker.subtype)
        (compactInductionTwistEquiv H ε σ f) := rfl

variable [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
variable [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
variable [MeasurableSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [BorelSpace
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
variable [MeasurableSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable [BorelSpace (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
variable (ν : Measure (LeftQuotient
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)))
variable [IsFiniteMeasureOnCompacts ν]
variable (hKernelBasis : ∀ O : Set (splitStagesRetraction r s hrs P hker).ker,
  IsOpen O → (1 : (splitStagesRetraction r s hrs P hker).ker) ∈ O →
    ∃ U : OpenSubgroup (splitStagesRetraction r s hrs P hker).ker,
      IsCompact (U : Set (splitStagesRetraction r s hrs P hker).ker) ∧
        (U : Set (splitStagesRetraction r s hrs P hker).ker) ⊆ O)
variable (μN : Measure (splitStagesRetraction r s hrs P hker).ker)
variable (μI : Measure
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : IsCompatible
  ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype) μN μI ν)
variable (hN : IsClosed (r.ker : Set G))
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O)

local notation "χ" => haarCharacter r s hrs P H hker hH hsH
local notation "κ" => coefficientAction r s hrs P H hker hHP hH hsH θ hθ σ
local notation "eC" => coefficientUntwist r s hrs hr hs P H hker hHP hsH θ hθ σ

/-- The comparison on the exact source and target carriers. -/
def comparisonEquiv :
    (localizedAction r s θ.toMonoidHom hθ (compactInduced H σ)).Equiv
      (compactInduced K κ) :=
  (inductionUntwist r s hrs hr hs H θ hθ σ).trans
    ((splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σt
      (twisted_smooth r s hrs hr hs H θ hθ σ hσ)
      ν hKernelBasis μN μI hCompatible hN hBasis).trans
        (compactInducedEquiv K (twistEquiv χ (Representation.Equiv.symm eC))))


/-- The forward comparison has exactly the published inverse-weighted integral. -/
theorem comparisonEquiv_eval_mk (f : CompactFunctions H σ) (l : L) :
    eval K κ
      (comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f)).val l =
      AlgebraicIntegral.integral ν
        (integrand r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l) := by
  let ht := twisted_smooth r s hrs hr hs H θ hθ σ hσ
  let F := compactInductionTwistEquiv H ε σ f
  let S := splitStagesKernelSlice r s hrs hr hs P H hker hHP hP hH hsH σt ht F l
  let Q := quotientCoinvariantSimple I
    (MonoidHom.comp σtP ((rP).ker.subtype.subgroupComap HP)) S
  have he : Q.map (Representation.Equiv.symm eC).toLinearEquiv.toLinearMap =
      integrand r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l := by
    ext q
    obtain ⟨n, rfl⟩ := Quotient.exists_rep q
    change (Representation.Equiv.symm eC)
      (Representation.Coinvariants.mk (MonoidHom.comp σtP ((rP).ker.subtype.subgroupComap HP))
        (eval H σt F.val (((n : P) : G) * s l))) =
      Jacquet.Localization.mk σP A η
        (((θP n)⁻¹ : ℂˣ) • eval H σ f.val (((n : P) : G) * s l))
    rw [coefficientUntwist_symm_mk]
    congr 1
    change ((ξ (((n : P) : G) * s l))⁻¹ : ℂˣ) •
        eval H σ f.val (((n : P) : G) * s l) = _
    have hw : ξ (((n : P) : G) * s l) = θP n := by
      rw [map_mul, characterExtension_section, mul_one]
      exact characterExtension_kernel r s hrs θ.toMonoidHom hθ
        (splitStagesKernelEquiv r s hrs P hker n)
    rw [hw]
  change (Representation.Equiv.symm eC)
    (eval K (twist χ (splitKernelCoefficientAction rP sP HP hSI σtP))
      (splitStagesCompactEquiv r s hrs hr hs P H hker hHP hP hH hsH σt ht
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Representation.Coinvariants.mk _ F)).val l) = _
  rw [splitStagesCompactEquiv_eval_mk_integral]
  change (Representation.Equiv.symm eC) (AlgebraicIntegral.integral ν Q) = _
  exact (AlgebraicIntegral.integral_linearMap Q
    (quotientCoinvariantSimple_finMeasSupp I _ ν S)
    (Representation.Equiv.symm eC).toLinearEquiv.toLinearMap).symm.trans
      (congrArg (AlgebraicIntegral.integral ν) he)

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {τ : Representation ℂ H W} (hτ : IsSmooth τ)

/-- The canonical descended simple function commutes with every coefficient map. -/
theorem integrand_natural (T : σ.IntertwiningMap τ)
    (f : CompactFunctions H σ) (l : L) :
    integrand r s hrs hr hs P H hker hHP hP hH hsH θ τ hτ
        (compactInducedMap H T f) l =
      (integrand r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l).map
        (twistIntertwining χ
          (subgroupMap rP sP θP hθP HP hSI (restrictAlongMap φ T))).toLinearMap := by
  ext q
  obtain ⟨n, rfl⟩ := Quotient.exists_rep q
  change Jacquet.Localization.mk (τ.comp φ) A η
      (((θP n)⁻¹ : ℂˣ) • T (eval H σ f.val (((n : P) : G) * s l))) =
    Jacquet.Localization.mk (τ.comp φ) A η
      (T (((θP n)⁻¹ : ℂˣ) • eval H σ f.val (((n : P) : G) * s l)))
  simp only [Units.smul_def, map_smul]

/-- The comparison is natural across independent coefficient universes. -/
theorem comparisonEquiv_natural (T : σ.IntertwiningMap τ)
    (z : Jacquet.Localization.Coinvariants (compactInduced H σ) r.ker θ.toMonoidHom) :
    comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ τ hτ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (sectionMap r s θ.toMonoidHom hθ (compactInducedMap H T) z) =
      compactInducedMap K
        (twistIntertwining χ
          (subgroupMap rP sP θP hθP HP hSI (restrictAlongMap φ T)))
        (comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ
          ν hKernelBasis μN μI hCompatible hN hBasis z) := by
  obtain ⟨f, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ z
  rw [sectionMap_mk]
  refine Subtype.ext (Subtype.ext (Subtype.ext (funext ?_)))
  intro l
  change eval K (coefficientAction r s hrs P H hker hHP hH hsH θ hθ τ)
      (comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ τ hτ
        ν hKernelBasis μN μI hCompatible hN hBasis
        (Jacquet.Localization.mk (compactInduced H τ) r.ker θ.toMonoidHom
          (compactInducedMap H T f))).val l =
    (twistIntertwining χ
      (subgroupMap rP sP θP hθP HP hSI (restrictAlongMap φ T)))
      (eval K κ
        (comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ
          ν hKernelBasis μN μI hCompatible hN hBasis
          (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f)).val l)
  rw [comparisonEquiv_eval_mk, comparisonEquiv_eval_mk,
    integrand_natural r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ hτ T f l]
  exact AlgebraicIntegral.integral_linearMap _
    (integrand_finMeasSupp r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ ν f l) _

end Comparison

end Langlands.Induction.SplitStagesCharacter

namespace Langlands.Induction

open SplitStagesCharacter

universe uG uL uV uW

/-- Natural character-localized compact induction in split stages, with the
canonical inverse-weighted quotient integral and independent coefficient universes. -/
theorem splitStagesCharacterComparison :
    SplitStagesCharacterComparisonStatement.{uG, uL, uV, uW} := by
  intro G _ _ _ _ _ L _ _ _ r s hrs hr hs P H hker hHP hP hH hsH θ hθ
    _ _ _ _ _ _ _ ν _ μN μI _ _ _ _ _ _ hCompatible hN hBasis hKernelBasis
    V W _ _ _ _ σ hσ τ hτ
  dsimp only
  refine ⟨comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ
      ν hKernelBasis μN μI hCompatible hN hBasis,
    comparisonEquiv r s hrs hr hs P H hker hHP hP hH hsH θ hθ τ hτ
      ν hKernelBasis μN μI hCompatible hN hBasis, ?_, ?_, ?_⟩
  · exact comparisonEquiv_eval_mk r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ
      ν hKernelBasis μN μI hCompatible hN hBasis
  · exact comparisonEquiv_eval_mk r s hrs hr hs P H hker hHP hP hH hsH θ hθ τ hτ
      ν hKernelBasis μN μI hCompatible hN hBasis
  · exact comparisonEquiv_natural r s hrs hr hs P H hker hHP hP hH hsH θ hθ σ hσ
      ν hKernelBasis μN μI hCompatible hN hBasis hτ

end Langlands.Induction
