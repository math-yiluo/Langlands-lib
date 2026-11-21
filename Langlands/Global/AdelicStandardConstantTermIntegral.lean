import Langlands.Global.AdelicConstantTermAverage
import Langlands.Global.AdelicStandardLeviHeightRestriction
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected

/-! # Constant terms along standard unipotent radicals

For a connected reductive `G` over a number field, a maximal split torus `i`, a generic
cocharacter `ν` and `J ⊆ Δ₀`, the standard unipotent radical `U_J` has closed adelic points and
compact quotient `U_J(F) \ U_J(𝔸)`. The image `Λ₀` of `P₀(F)` in `G(𝔸)` is discrete, contains
`U_J(F)` and normalizes `U_J(F)` and `U_J(𝔸)`. So the constant-term identities of
`Langlands.Global.AdelicConstantTermAverage` hold for `Λ = P₀(F)` and `U = U_J`. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme AdelicSubgroupPoints

section Structural

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The standard parabolic `P_J` normalizes its standard unipotent radical `U_J`, on every test
scheme. -/
theorem standardUnipotent_isNormalizedBy_standardParabolic (J : Set (characterLattice T)) :
    (standardUnipotent i ν J).IsNormalizedBy (standardParabolic i ν J) := by
  intro S g x hg hx
  rw [mem_standardUnipotent] at hx ⊢
  rw [mem_standardParabolic] at hg
  intro ζ hζ
  exact Dynamic.conj_mem_unipotent _ (hg ζ hζ) (hx ζ hζ)

theorem smooth_standardUnipotentScheme (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) : Smooth (Standard.unipotentScheme i ν J).X.hom := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  have hU := Standard.isRepresentedBy_unipotentHom i ν J
  rw [(heq ζ hζ).2.2] at hU
  exact (dynamicSmooth k G (CommGroupScheme.groupHom ζ ≫ i) _ _).2.2 hU

theorem connectedSpace_standardUnipotentScheme (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) : ConnectedSpace (Standard.unipotentScheme i ν J).X.left := by
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  have hU := Standard.isRepresentedBy_unipotentHom i ν J
  rw [(heq ζ hζ).2.2] at hU
  exact DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _ hU

end Structural

section Adelic

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

theorem standardUnipotent_eq_range (J : Set (characterLattice T)) :
    standardUnipotent i ν J = SubgroupFunctor.range (Standard.unipotentHom i ν J) :=
  (Standard.isRepresentedBy_unipotentHom i ν J).2.symm

private theorem unipotentScheme_instances (J : Set (characterLattice T)) :
    IsClosedImmersion (Standard.unipotentHom i ν J).hom.hom.left ∧
      IsAffine (Standard.unipotentScheme i ν J).X.left := by
  have hci : IsClosedImmersion (Standard.unipotentHom i ν J).hom.hom.left :=
    Standard.isClosedSubgroup_unipotentHom i ν J
  have : IsAffineHom (Standard.unipotentScheme i ν J).X.hom := by
    rw [← Over.w (Standard.unipotentHom i ν J).hom.hom]
    infer_instance
  exact ⟨hci, isAffine_of_isAffineHom (Standard.unipotentScheme i ν J).X.hom⟩

/-- `U_J(𝔸)` is closed in `G(𝔸)`. -/
theorem isClosed_adelicPoints_standardUnipotent (J : Set (characterLattice T)) :
    IsClosed (adelicPoints F G (standardUnipotent i ν J) : Set (AdelicGroupPoints F G)) := by
  obtain ⟨h1, h2⟩ := unipotentScheme_instances F G i ν J
  rw [standardUnipotent_eq_range F G i ν J]
  exact isClosed_adelicPoints_range F G (Standard.unipotentHom i ν J)

/-- `U_J(F) \ U_J(𝔸)` is compact. -/
theorem compactSpace_standardUnipotent (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    CompactSpace (RationalQuotient F G (standardUnipotent i ν J)) := by
  obtain ⟨h1, h2⟩ := unipotentScheme_instances F G i ν J
  rw [standardUnipotent_eq_range F G i ν J]
  exact compactSpace_rationalQuotient_range_unipotent F (Standard.unipotentHom i ν J)
    (smooth_standardUnipotentScheme i ν hG hi hν J hJ)
    (connectedSpace_standardUnipotentScheme i ν hG hi hν J hJ)
    (RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν J hJ)

/-- The image `Λ₀` of `P₀(F)` in `G(𝔸)`, for `P₀` the standard minimal parabolic. -/
def minimalParabolicImage : Subgroup (AdelicGroupPoints F G) :=
  (rationalSubgroup F G (standardParabolic i ν ∅)).map
    (adelicPoints F G (standardParabolic i ν ∅)).subtype

theorem minimalParabolicImage_le :
    minimalParabolicImage F G i ν ≤ AdelicGroupPoints.rationalSubgroup F G := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact ⟨q.val, rfl⟩

theorem isDiscrete_minimalParabolicImage :
    IsDiscrete (minimalParabolicImage F G i ν : Set (AdelicGroupPoints F G)) :=
  (AdelicGroupPoints.isDiscrete_rationalSubgroup F G).mono (minimalParabolicImage_le F G i ν)

theorem mem_minimalParabolicImage_of_rational {x : RationalGroupPoints F G}
    (hx : x ∈ (standardParabolic i ν ∅).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F F)))) :
    AdelicGroupPoints.rational F G x ∈ minimalParabolicImage F G i ν :=
  ⟨rational F G (standardParabolic i ν ∅) ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩

section Order

variable {hG : IsConnectedReductive G} {hi : IsMaximalSplitTorus i} {hν : IsGenericCocharacter i ν}

include hG hi hν in
theorem standardUnipotent_le_minimalParabolic (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardUnipotent i ν J ≤ standardParabolic i ν ∅ := by
  have h := ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).2
    (Set.empty_subset J)
  intro S g hg
  exact standardUnipotent_le_standardParabolic i ν ∅ S (h.2 S hg)

include hG hi hν in
theorem minimalParabolic_le_standardParabolic (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardParabolic i ν ∅ ≤ standardParabolic i ν J :=
  ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.mp
    (Set.empty_subset J)

include hG hi hν in
/-- `U_J(F) ⊆ Λ₀`. -/
theorem rationalSubgroup_standardUnipotent_le (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∀ w ∈ rationalSubgroup F G (standardUnipotent i ν J),
      ((w : adelicPoints F G (standardUnipotent i ν J)) : AdelicGroupPoints F G) ∈
        minimalParabolicImage F G i ν := by
  rintro _ ⟨q, rfl⟩
  exact mem_minimalParabolicImage_of_rational F G i ν
    (standardUnipotent_le_minimalParabolic F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ _ q.2)

include hG hi hν in
/-- `Λ₀` normalizes `U_J(F)`. -/
theorem conj_rationalSubgroup_standardUnipotent (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∀ l ∈ minimalParabolicImage F G i ν, ∀ w ∈ rationalSubgroup F G (standardUnipotent i ν J),
      ∃ w' ∈ rationalSubgroup F G (standardUnipotent i ν J),
        ((w' : adelicPoints F G (standardUnipotent i ν J)) : AdelicGroupPoints F G) =
          l * w * l⁻¹ := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨y, rfl⟩
  have hxJ := minimalParabolic_le_standardParabolic F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
    _ x.2
  have hc := standardUnipotent_isNormalizedBy_standardParabolic i ν J _ x.val y.val hxJ y.2
  refine ⟨rational F G (standardUnipotent i ν J) ⟨x.val * y.val * x.val⁻¹, hc⟩, ⟨_, rfl⟩, ?_⟩
  change AdelicGroupPoints.rational F G (x.val * y.val * x.val⁻¹) =
    AdelicGroupPoints.rational F G x.val * AdelicGroupPoints.rational F G y.val *
      (AdelicGroupPoints.rational F G x.val)⁻¹
  rw [map_mul, map_mul, map_inv]

include hG hi hν in
/-- `Λ₀` normalizes `U_J(𝔸)`. -/
theorem conj_adelicPoints_standardUnipotent (J : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∀ l ∈ minimalParabolicImage F G i ν, ∀ w ∈ adelicPoints F G (standardUnipotent i ν J),
      l * w * l⁻¹ ∈ adelicPoints F G (standardUnipotent i ν J) := by
  rintro _ ⟨z, -, rfl⟩ w hw
  exact standardUnipotent_isNormalizedBy_standardParabolic i ν J _ z.val w
    (minimalParabolic_le_standardParabolic F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ _ z.2) hw

end Order

/-- **Statement form.** For connected reductive `G` over a number field, a maximal split torus
`i`, a generic cocharacter `ν` and `J ⊆ Δ₀`, the nonnegative constant term along the standard
unipotent radical `U_J` of a measurable left `P₀(F)`-invariant function is left
`P₀(F)`-invariant, and its integral over a Borel fundamental domain of `P₀(F)` in `G(𝔸)` equals
that of the function. -/
def StandardConstantTermIntegralStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
    ∀ J ⊆ simpleRelativeRoots i ν,
      haveI := isClosed_adelicPoints_standardUnipotent F G i ν J
      ∀ {f : AdelicGroupPoints F G → ℝ≥0∞}, Measurable f →
        (∀ l ∈ minimalParabolicImage F G i ν, ∀ x, f (l * x) = f x) →
        (∀ l ∈ minimalParabolicImage F G i ν, ∀ g,
          ConstantTermAverage.lowerConstantTerm F G (standardUnipotent i ν J) f (l * g) =
            ConstantTermAverage.lowerConstantTerm F G (standardUnipotent i ν J) f g) ∧
        ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
            (isDiscrete_minimalParabolicImage F G i ν),
          ConstantTermAverage.lowerConstantTerm F G (standardUnipotent i ν J) f g ∂Measure.haar =
        ∫⁻ g in LeftCosetSpace.fundamentalDomain (minimalParabolicImage F G i ν)
            (isDiscrete_minimalParabolicImage F G i ν), f g ∂Measure.haar

/-- Proof of `StandardConstantTermIntegralStatement`. -/
theorem standardConstantTermIntegral : StandardConstantTermIntegralStatement.{u} := by
  intro F _ _ G _ _ _ T i ν hG hi hν J hJ
  have : IsClosed (adelicPoints F G (standardUnipotent i ν J) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_standardUnipotent F G i ν J
  have : CompactSpace (RationalQuotient F G (standardUnipotent i ν J)) :=
    compactSpace_standardUnipotent F G i ν hG hi hν J hJ
  intro f hf hfΛ
  have hΓ := And.intro
    (rationalSubgroup_standardUnipotent_le F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
    (conj_rationalSubgroup_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ)
  have hnorm := conj_adelicPoints_standardUnipotent F G i ν (hG := hG) (hi := hi) (hν := hν) J hJ
  exact ⟨fun l hl g => ConstantTermAverage.lowerConstantTerm_mul_left F G
      (standardUnipotent i ν J) (minimalParabolicImage F G i ν) hΓ hnorm hf hfΛ ⟨l, hl⟩ g,
    ConstantTermAverage.setLIntegral_lowerConstantTerm F G (standardUnipotent i ν J)
      (minimalParabolicImage F G i ν) hΓ hnorm (isDiscrete_minimalParabolicImage F G i ν) hf hfΛ⟩

end Adelic

end Langlands.Global.StandardConstantTerm
