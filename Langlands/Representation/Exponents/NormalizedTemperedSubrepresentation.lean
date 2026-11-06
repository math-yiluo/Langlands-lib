import Langlands.Representation.Exponents.NormalizedTemperedSubrepresentationStatement
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.BruhatTits.Unipotent.JacquetCompactContainmentProof
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-! # Normalized-exponent temperedness passes to subrepresentations -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance subrepresentationAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  {P M U : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- A compatible presentation identifies every supplied geometric radical
with a dynamic unipotent group, so its compact subsets lie in compact subgroups. -/
theorem pointImage_radical_isLimitOfCompactSubgroups_of_presentation
    (hG : IsConnectedReductive G) (pres : ParabolicRootPresentation p l a)
    {r : U ⟶ P} (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (pointImage (r ≫ p)) := by
  have := hG.smooth
  have hpoints : pointImage (r ≫ p) =
      (Dynamic.unipotent (CommGroupScheme.groupHom pres.splitComponentCocharacter ≫
        a ≫ l ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    congrArg (fun H : SubgroupFunctor G =>
      H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      (pres.range_comp_radical_eq hr)
  rw [hpoints]
  exact BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
    BruhatTits.dynamicUnipotentCompactOpenContainment k G hG _

/-- The actual normalized Jacquet map for intertwiners between independent
carrier universes. The underlying quotient map is unchanged by normalization. -/
def jacquetIntertwining
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    {τ : SmoothRep.{0, u, w} ℂ (rationalPoints G)}
    (f : π.representation.IntertwiningMap τ.representation) :
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation.IntertwiningMap
      ((jacquetFunctor p l r hp hr hl hmul).obj τ).representation :=
  twistIntertwining
    (HaarModulus.closedInverseHalfCharacter (pointImage (r ≫ p))
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr))
    (Jacquet.Localization.map (pointImage (r ≫ p)) 1 (pointImage (l ≫ p))
      (pointImage_le_normalizer p l r hr)
      (Jacquet.Localization.isInvariant_one _ _ _) f)

/-- An injective intertwiner between independent carrier universes preserves
every normalized Jacquet exponent for a parabolic with a root presentation. -/
theorem isNormalizedJacquetExponent_of_injective_intertwining
    (hG : IsConnectedReductive G) (pres : ParabolicRootPresentation p l a)
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
    {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    {τ : SmoothRep.{0, u, w} ℂ (rationalPoints G)}
    (f : π.representation.IntertwiningMap τ.representation)
    (hf : Function.Injective f)
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha τ χ := by
  let F := jacquetIntertwining r hp hl hr hmul f
  have hF : Function.Injective F :=
    Jacquet.Localization.map_injective_of_smooth _
      (pointImage_radical_isLimitOfCompactSubgroups_of_presentation hG pres hr)
      1 (IsLocallyConstant.const 1) (pointImage (l ≫ p))
      (pointImage_le_normalizer p l r hr)
      (Jacquet.Localization.isInvariant_one _ _ (pointImage_le_normalizer p l r hr))
      f hf τ.isSmooth
  refine ⟨hχ.1, ?_⟩
  intro hbot
  apply hχ.2
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply hF
  rw [map_zero]
  have hx' := map_mem_generalizedWeightSpace (splitComponentPointsMap (l ≫ p) a)
    χ (splitComponentPointsMap_mem_center (l ≫ p) ha) F hx
  change F x ∈ normalizedJacquetWeightSpace p l r hp hl hr hmul ha τ χ at hx'
  rw [show normalizedJacquetWeightSpace p l r hp hl hr hmul ha τ χ = ⊥ from hbot] at hx'
  exact hx'

/-- Normalized-exponent temperedness passes through an injective intertwiner
between independent carrier universes. This includes maps into an induced carrier
in `Type (max u v)`. Presentation coverage comes from the tempered target. -/
theorem IsNormalizedExponentTempered.of_injective_intertwining
    {hG : IsConnectedReductive G}
    {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    {τ : SmoothRep.{0, u, w} ℂ (rationalPoints G)}
    (hτ : IsNormalizedExponentTempered hG τ)
    (f : π.representation.IntertwiningMap τ.representation)
    (hf : Function.Injective f) :
    IsNormalizedExponentTempered hG π := by
  have := hG.smooth
  refine ⟨Langlands.isAdmissible_of_injective f hf hτ.isAdmissible, ?_⟩
  intro P M A p l a hp hl ha
  have hcone := hτ.parabolic p l a hp hl ha
  refine ⟨hcone.1, ?_⟩
  intro pres U r hr hmul χ hχ
  exact hcone.2 pres U r hr hmul χ
    (isNormalizedJacquetExponent_of_injective_intertwining
      hG pres r hp hl hr hmul ha f hf hχ)

/-- The same closure property for a morphism in one fixed-universe smooth
representation category. -/
theorem IsNormalizedExponentTempered.of_injective
    {hG : IsConnectedReductive G}
    {π τ : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (hτ : IsNormalizedExponentTempered hG τ)
    (f : π ⟶ τ) (hf : Function.Injective (SmoothRep.hom f)) :
    IsNormalizedExponentTempered hG π :=
  hτ.of_injective_intertwining (SmoothRep.hom f) hf

/-- Normalized-exponent temperedness is invariant under equivalences of the
actual representations, including equivalences between carrier universes. -/
theorem isNormalizedExponentTempered_equiv_iff
    {hG : IsConnectedReductive G}
    {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    {τ : SmoothRep.{0, u, w} ℂ (rationalPoints G)}
    (e : π.representation.Equiv τ.representation) :
    IsNormalizedExponentTempered hG π ↔ IsNormalizedExponentTempered hG τ :=
  ⟨fun hπ => hπ.of_injective_intertwining e.symm.toIntertwiningMap e.symm.injective,
    fun hτ => hτ.of_injective_intertwining e.toIntertwiningMap e.injective⟩

/-- The uniform supporting statement used in the subrepresentation step
of Renard VII.2.6. -/
theorem normalizedTemperedSubrepresentation :
    NormalizedTemperedSubrepresentationStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π τ f hf hτ
  exact hτ.of_injective f hf

end Langlands.Aubert.General.RepresentedParabolic
