import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.LeftCosetProduct
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # The full principal adelic quotient as a product with the positive split centre -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)

local notation "T₀" => canonicalTorus F G
local notation "i₀" => canonicalComponent F G
local notation "hs₀" => isSplitComponent_canonicalComponent F G
local notation "hi₀" => canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
local notation "A₀" => intrinsicSubgroup F T₀
local notation "N₀" => AdelicGroupPoints.normOneSubgroup F G
local notation "H₀" => AdelicGroupPoints.rationalNormOneSubgroup F G
local notation "Γ₀" => AdelicGroupPoints.rationalSubgroup F G

omit [NumberField F] in
private theorem canonicalSplit : IsSplitTorus (T₀).toGrp := (hs₀).1.1.1

local notation "hT₀" => canonicalSplit F G

private def splitIndex : Type := (hT₀).choose

local instance : Fintype (splitIndex F G) := @Fintype.ofFinite _ (hT₀).choose_spec.1

private def splitting : (T₀).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (splitIndex F G) :=
  Classical.choice (hT₀).choose_spec.2

/-- The positive points of the central split torus identify with the actual subgroup `A_G`. -/
def positiveCentreEquiv : A₀ ≃ₜ* canonicalSubgroup F G := by
  letI := canonical_finiteIndex F G hG
  let b := positiveFactor F G T₀ i₀ hi₀ (splitIndex F G) (splitting F G)
  have hb (a : A₀) : positivePointMap F G T₀ i₀ a ∈ canonicalSubgroup F G := by
    rw [canonicalSubgroup_eq_imageSubgroup F G]
    exact ⟨a.val, a.property, rfl⟩
  refine
    { toFun := fun a => ⟨positivePointMap F G T₀ i₀ a, hb a⟩
      invFun := fun a => b a.val
      left_inv := positiveFactor_positivePointMap F G T₀ i₀ hi₀ _ _
      right_inv := ?_
      map_mul' := fun a a' => Subtype.ext (map_mul (positivePointMap F G T₀ i₀) a a')
      continuous_toFun := (positivePointMap F G T₀ i₀).continuous.subtype_mk hb
      continuous_invFun := b.continuous.comp continuous_subtype_val }
  intro a
  have ha : a.val ∈ imageSubgroup F T₀ G i₀ := by
    simpa only [← canonicalSubgroup_eq_imageSubgroup F G] using a.property
  obtain ⟨t, ht, heq⟩ := ha
  apply Subtype.ext
  change positivePointMap F G T₀ i₀ (b a.val) = a.val
  rw [← heq]
  exact congrArg (positivePointMap F G T₀ i₀)
    (positiveFactor_positivePointMap F G T₀ i₀ hi₀ _ _ ⟨t, ht⟩)

@[simp] theorem positiveCentreEquiv_coe (a : A₀) :
    (positiveCentreEquiv F G hG a : AdelicGroupPoints F G) =
      positivePointMap F G T₀ i₀ a := rfl

/-- The actual positive central factor is identified with the entire ambient logarithm space. -/
def positiveCentreLogEquiv : canonicalSubgroup F G ≃ₜ* Multiplicative (AdelicGroupPoints.RealCharacterDual F G) :=
  haveI := canonical_finiteIndex F G hG
  (positiveCentreEquiv F G hG).symm.trans
    (positiveAmbientLogEquiv F G T₀ i₀ hi₀ (splitIndex F G) (splitting F G))

@[simp] theorem positiveCentreLogEquiv_apply (a : canonicalSubgroup F G) :
    positiveCentreLogEquiv F G hG a = AdelicGroupPoints.characterLogHom F G a.val := by
  let := canonical_finiteIndex F G hG
  change positiveAmbientLogEquiv F G T₀ i₀ hi₀ (splitIndex F G) (splitting F G)
    ((positiveCentreEquiv F G hG).symm a) = _
  rw [← characterLogHom_positivePointMap F G T₀ i₀ hi₀ (splitIndex F G) (splitting F G),
    ← positiveCentreEquiv_coe F G hG, ContinuousMulEquiv.apply_symm_apply]

/-- The intrinsic positive and norm-one factors multiply to the actual adelic group. -/
def intrinsicNormOneDecomposition : A₀ × N₀ ≃ₜ* AdelicGroupPoints F G :=
  haveI := canonical_finiteIndex F G hG
  normOneDecompositionMulEquiv F G T₀ i₀ hi₀ (splitIndex F G) (splitting F G) (hs₀).1.2

@[simp] theorem intrinsicNormOneDecomposition_apply (p : A₀ × N₀) :
    intrinsicNormOneDecomposition F G hG p = positivePointMap F G T₀ i₀ p.1 * p.2.val := rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem normOne_mem_principal (n : N₀) : n.val ∈ Γ₀ ↔ n ∈ H₀ := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, congrArg Subtype.val hq⟩

/-- In intrinsic product coordinates the principal subgroup lies in the second factor. -/
theorem intrinsicNormOneDecomposition_mem_principal (p : A₀ × N₀) :
    intrinsicNormOneDecomposition F G hG p ∈ Γ₀ ↔ p.1 = 1 ∧ p.2 ∈ H₀ := by
  let := canonical_finiteIndex F G hG
  change positivePointMap F G T₀ i₀ p.1 * p.2.val ∈ Γ₀ ↔ _
  constructor
  · intro hp
    have hp₁ := AdelicGroupPoints.rationalSubgroup_le_normOneSubgroup F G hp
    have h := positiveFactor_normOne F G T₀ i₀ hi₀ _ (splitting F G) ⟨_, hp₁⟩
    rw [positiveFactor_mul_normOne] at h
    refine ⟨h, (normOne_mem_principal F G p.2).mp ?_⟩
    simpa only [h, map_one, one_mul] using hp
  · rintro ⟨h, hp⟩
    simpa only [h, map_one, one_mul] using (normOne_mem_principal F G p.2).mpr hp

/-- Inclusion of norm-one representatives identifies their principal quotient with `[G]`. -/
def canonicalNormOneQuotientHomeomorph : AdelicGroupPoints.NormOneRationalQuotient F G ≃ₜ
    CanonicalQuotient F G :=
  haveI := canonical_finiteIndex F G hG
  normOneQuotientHomeomorph F G hi₀ (canonicalSubgroup_eq_imageSubgroup F G)
    (splitIndex F G) (splitting F G) (hs₀).1.2

@[simp] theorem coe_canonicalNormOneQuotientHomeomorph :
    ⇑(canonicalNormOneQuotientHomeomorph F G hG) =
      normOneToQuotient F G (canonicalRestrictionTorus F G) (canonicalRestrictionComponent F G) :=
  haveI := canonical_finiteIndex F G hG
  coe_normOneQuotientHomeomorph F G hi₀ (canonicalSubgroup_eq_imageSubgroup F G) _ _ (hs₀).1.2

/-- Retain the actual split-centre coordinate when dividing out only by rational points. -/
def principalQuotientProductHomeomorph : AdelicGroupPoints.RationalQuotient F G ≃ₜ
    canonicalSubgroup F G × CanonicalQuotient F G :=
  (LeftCosetSpace.productHomeomorph (intrinsicNormOneDecomposition F G hG) H₀ Γ₀
    (intrinsicNormOneDecomposition_mem_principal F G hG)).trans
      ((positiveCentreEquiv F G hG).toHomeomorph.prodCongr (canonicalNormOneQuotientHomeomorph F G hG))

private theorem principalQuotientProductHomeomorph_chart (p : A₀ × N₀) :
    principalQuotientProductHomeomorph F G hG
        (LeftCosetSpace.mk Γ₀ (intrinsicNormOneDecomposition F G hG p)) =
      (positiveCentreEquiv F G hG p.1, LeftCosetSpace.mk (canonicalRationalSubgroup F G) p.2.val) := by
  unfold principalQuotientProductHomeomorph
  rw [Homeomorph.trans_apply, LeftCosetSpace.productHomeomorph_mk]
  change (_, canonicalNormOneQuotientHomeomorph F G hG (LeftCosetSpace.mk H₀ p.2)) = _
  rw [coe_canonicalNormOneQuotientHomeomorph]
  rfl

/-- On a representative `a * n`, the two coordinates are `a` and the class of `n` in `[G]`. -/
@[simp] theorem principalQuotientProductHomeomorph_mk (a : canonicalSubgroup F G) (n : N₀) :
    principalQuotientProductHomeomorph F G hG (LeftCosetSpace.mk Γ₀ (a.val * n.val)) =
      (a, LeftCosetSpace.mk (canonicalRationalSubgroup F G) n.val) := by
  obtain ⟨t, rfl⟩ := (positiveCentreEquiv F G hG).surjective a
  exact principalQuotientProductHomeomorph_chart F G hG (t, n)

/-- The second coordinate is the ordinary quotient map on representatives. -/
@[simp] theorem principalQuotientProductHomeomorph_snd_mk (g : AdelicGroupPoints F G) :
    (principalQuotientProductHomeomorph F G hG (LeftCosetSpace.mk Γ₀ g)).2 =
      LeftCosetSpace.mk (canonicalRationalSubgroup F G) g := by
  obtain ⟨p, rfl⟩ := (intrinsicNormOneDecomposition F G hG).surjective g
  rw [principalQuotientProductHomeomorph_chart]
  have ha : (positiveCentreEquiv F G hG p.1).val ∈ canonicalRationalSubgroup F G :=
    subgroup_le_rationalSubgroup F G (canonicalRestrictionTorus F G)
      (canonicalRestrictionComponent F G) (positiveCentreEquiv F G hG p.1).property
  exact (LeftCosetSpace.mk_subgroup_mul (canonicalRationalSubgroup F G) ⟨_, ha⟩ p.2.val).symm

/-- The product identification for the inherited quotient sigma algebras. -/
def principalQuotientProductEquiv : AdelicGroupPoints.RationalQuotient F G ≃ᵐ
    canonicalSubgroup F G × CanonicalQuotient F G :=
  haveI := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  (principalQuotientProductHomeomorph F G hG).toMeasurableEquiv

@[simp] theorem coe_principalQuotientProductEquiv :
    ⇑(principalQuotientProductEquiv F G hG) = principalQuotientProductHomeomorph F G hG := rfl

/-- The normalized Haar measure before taking the image of the positive points in `G(𝔸_F)`. -/
def intrinsicCentreHaarMeasure : Measure A₀ :=
  haveI := canonical_finiteIndex F G hG
  intrinsicPositiveHaarMeasure F G T₀ i₀ hi₀ (hs₀).1.2 hT₀

instance intrinsicCentreHaarMeasure_sigmaFinite : SigmaFinite (intrinsicCentreHaarMeasure F G hG) := by
  let := canonical_finiteIndex F G hG
  unfold intrinsicCentreHaarMeasure
  rw [intrinsicPositiveHaarMeasure_eq F G T₀ i₀ hi₀ (splitIndex F G) (splitting F G)]
  exact normalizedPositiveHaarMeasure_sigmaFinite F G T₀ i₀ hi₀
    (splitIndex F G) (splitting F G) (hs₀).1.2

/-- The intrinsic product has exactly the existing ambient Haar measure. -/
theorem measurePreserving_intrinsicNormOneDecomposition :
    MeasurePreserving (intrinsicNormOneDecomposition F G hG)
      ((intrinsicCentreHaarMeasure F G hG).prod (Measure.haar : Measure N₀))
      (Measure.haar : Measure (AdelicGroupPoints F G)) := by
  let := canonical_finiteIndex F G hG
  exact measurePreserving_normOneDecomposition_intrinsic F G T₀ i₀ hi₀
    (splitIndex F G) (splitting F G) (hs₀).1.2 hT₀

/-- The Haar measure on `A_G` normalized by the existing ambient and norm-one Haar measures. -/
def positiveCentreHaarMeasure : Measure (canonicalSubgroup F G) :=
  Measure.map (positiveCentreEquiv F G hG) (intrinsicCentreHaarMeasure F G hG)

instance positiveCentreHaarMeasure_isHaarMeasure :
    (positiveCentreHaarMeasure F G hG).IsHaarMeasure := by
  let := canonical_finiteIndex F G hG
  let := positiveIsTopologicalGroup F T₀ (splitIndex F G) (splitting F G)
  let : (intrinsicCentreHaarMeasure F G hG).IsHaarMeasure :=
    intrinsicPositiveHaarMeasure_isHaarMeasure F G T₀ i₀ hi₀ (hs₀).1.2 hT₀
  exact (positiveCentreEquiv F G hG).isHaarMeasure_map _

/-- The comparison with the actual image preserves the chosen normalization. -/
theorem measurePreserving_positiveCentreEquiv :
    MeasurePreserving (positiveCentreEquiv F G hG) (intrinsicCentreHaarMeasure F G hG)
      (positiveCentreHaarMeasure F G hG) :=
  ⟨(positiveCentreEquiv F G hG).continuous.measurable, rfl⟩

/-- The existing measure on `[G]` is defined by pushforward along this inclusion. -/
theorem measurePreserving_canonicalNormOneQuotientHomeomorph :
    MeasurePreserving (canonicalNormOneQuotientHomeomorph F G hG)
      (AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G) (canonicalMeasure F G) := by
  rw [coe_canonicalNormOneQuotientHomeomorph]
  exact ⟨measurable_normOneToQuotient F G (canonicalRestrictionTorus F G)
    (canonicalRestrictionComponent F G), rfl⟩

end Langlands.Global.RestrictionSplitCentre
