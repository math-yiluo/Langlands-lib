import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Automorphic.GroupSchemeRestrictionCuspidalL2
import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2Hilbert

/-! # Cuspidal `L²` spaces of the canonical quotient `[G]` and independence of the split
component -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "S₀" => canonicalRestrictionTorus F G
local notation "j₀" => canonicalRestrictionComponent F G
local notation "T₀" => canonicalTorus F G
local notation "i₀" => canonicalComponent F G
local notation "hj₀" => isSplitComponent_canonicalRestrictionComponent F G
local notation "hs₀" => isSplitComponent_canonicalComponent F G

section Transport

variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
  {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable (hj : IsSplitComponent j)

/-- Continuous functions on the quotient of any split component of the restriction and on the
canonical quotient, identified by composition with the identity on representatives. -/
def continuousToCanonical : C(Quotient F G S j, ℂ) ≃ₗ[ℂ] C(CanonicalQuotient F G, ℂ) where
  toFun f := f.comp ⟨(toCanonicalQuotient hj).symm, (toCanonicalQuotient hj).symm.continuous⟩
  invFun f := f.comp ⟨toCanonicalQuotient hj, (toCanonicalQuotient hj).continuous⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro q
    exact congrArg f ((toCanonicalQuotient hj).symm_apply_apply q)
  right_inv f := by
    apply ContinuousMap.ext
    intro q
    exact congrArg f ((toCanonicalQuotient hj).apply_symm_apply q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem continuousToCanonical_apply (f : C(Quotient F G S j, ℂ))
    (q : CanonicalQuotient F G) :
    continuousToCanonical hj f q = f ((toCanonicalQuotient hj).symm q) := rfl

@[simp] theorem continuousToCanonical_symm_apply (f : C(CanonicalQuotient F G, ℂ))
    (q : Quotient F G S j) :
    (continuousToCanonical hj).symm f q = f (toCanonicalQuotient hj q) := rfl

/-- The two pullbacks to `G(𝔸_F)` agree under the identification. -/
theorem quotientContinuousPullback_continuousToCanonical (f : C(Quotient F G S j, ℂ)) :
    quotientContinuousPullback F G S₀ j₀ (continuousToCanonical hj f) =
      quotientContinuousPullback F G S j f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : (toCanonicalQuotient hj).symm
      (LeftCosetSpace.mk (canonicalRationalSubgroup F G) x) =
        LeftCosetSpace.mk (rationalSubgroup F G S j) x := by
    rw [Homeomorph.symm_apply_eq, toCanonicalQuotient_mk]
  exact congrArg f hx

/-- The identification intertwines the two continuous right actions. -/
theorem continuousToCanonical_rightAction (g : AdelicGroupPoints F G)
    (f : C(Quotient F G S j, ℂ)) :
    continuousToCanonical hj (continuousQuotientRightAction F G S j g f) =
      continuousQuotientRightAction F G S₀ j₀ g (continuousToCanonical hj f) := by
  apply ContinuousMap.ext
  intro q
  change f (LeftCosetSpace.rightTranslate (rationalSubgroup F G S j) g
      ((toCanonicalQuotient hj).symm q)) =
    f ((toCanonicalQuotient hj).symm
      (LeftCosetSpace.rightTranslate (canonicalRationalSubgroup F G) g q))
  congr 1
  rw [Homeomorph.eq_symm_apply, toCanonicalQuotient_rightTranslate, Homeomorph.apply_symm_apply]

/-- Square integrability for the two quotient measures corresponds. -/
theorem memLp_continuousToCanonical_iff (f : C(Quotient F G S j, ℂ)) :
    MemLp (continuousToCanonical hj f) 2 (canonicalMeasure F G) ↔
      MemLp f 2 (quotientHaarMeasure F G S j) := by
  have hm := measurePreserving_toCanonicalQuotient hj
  constructor
  · intro hf
    have hcomp := hf.comp_measurePreserving hm
    have heq : (continuousToCanonical hj f : CanonicalQuotient F G → ℂ) ∘
        toCanonicalQuotientMeasurableEquiv hj = f := by
      funext p
      exact congrArg f ((toCanonicalQuotient hj).symm_apply_apply p)
    rwa [heq] at hcomp
  · intro hf
    exact hf.comp_measurePreserving (MeasurePreserving.symm _ hm)

set_option maxRecDepth 20000 in
/-- On `L²` classes, the continuous identification is `toCanonicalL2Equiv`. -/
theorem quotientContinuousL2ToLp_continuousToCanonical
    (f : quotientContinuousL2Submodule F G (quotientHaarMeasure F G S j)) :
    quotientContinuousL2ToLp F G (canonicalMeasure F G)
        ⟨continuousToCanonical hj f.val,
          (memLp_continuousToCanonical_iff hj f.val).mpr f.property⟩ =
      toCanonicalL2Equiv hj (quotientContinuousL2ToLp F G _ f) :=
  rfl

set_option maxRecDepth 20000 in
/-- For a split component `i` of `G`, composing the identification of the positive-torus
quotient with the restriction quotient of `j` and then with the canonical quotient gives the
identification with the canonical quotient. -/
theorem toCanonicalL2Equiv_splitComponentL2Equiv {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} (hs : IsSplitComponent i)
    (f : QuotientL2 F G T i (positiveRationalQuotientHaarMeasure F G T i)) :
    toCanonicalL2Equiv hj (splitComponentL2Equiv F G hj hs f) =
      splitComponentL2Equiv F G hj₀ hs f := by
  change Lp.compMeasurePreserving (toCanonicalQuotientMeasurableEquiv hj).symm
      (MeasurePreserving.symm _ (measurePreserving_toCanonicalQuotient hj))
      (Lp.compMeasurePreserving
        (quotientMeasurableEquiv F G (subgroup_eq_of_splitComponents F G hj hs)).symm
        (MeasurePreserving.symm _ (measurePreserving_quotientMeasurableEquiv F G _)) f) =
    Lp.compMeasurePreserving
      (quotientMeasurableEquiv F G (subgroup_eq_of_splitComponents F G hj₀ hs)).symm
      (MeasurePreserving.symm _ (measurePreserving_quotientMeasurableEquiv F G _)) f
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply compMeasurePreserving_congr
  have hce : ∀ p, toCanonicalQuotientMeasurableEquiv hj
      (quotientMeasurableEquiv F G (subgroup_eq_of_splitComponents F G hj hs) p) =
        quotientMeasurableEquiv F G (subgroup_eq_of_splitComponents F G hj₀ hs) p := by
    intro p
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ p
    rw [quotientMeasurableEquiv_mk, quotientMeasurableEquiv_mk,
      coe_toCanonicalQuotientMeasurableEquiv, toCanonicalQuotient_mk]
  funext q
  obtain ⟨p, rfl⟩ :=
    (quotientMeasurableEquiv F G (subgroup_eq_of_splitComponents F G hj₀ hs)).surjective q
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  rw [← hce p]
  simp only [MeasurableEquiv.symm_apply_apply]

section ParabolicTransport

variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))
variable (hInv : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
  (hInv' : QuotientRightInvariant F G (canonicalMeasure F G))

theorem continuousToCanonical_mem_parabolicCuspidalL2_iff (f : C(Quotient F G S j, ℂ)) :
    continuousToCanonical hj f ∈ quotientParabolicCuspidalL2Subrepresentation F G hPD hG
        measuresU (canonicalMeasure F G) hInv' ↔
      f ∈ quotientParabolicCuspidalL2Subrepresentation F G hPD hG measuresU
        (quotientHaarMeasure F G S j) hInv := by
  rw [mem_quotientParabolicCuspidalL2Subrepresentation,
    mem_quotientParabolicCuspidalL2Subrepresentation,
    quotientContinuousPullback_continuousToCanonical, memLp_continuousToCanonical_iff]

/-- The continuous parabolic-vanishing `L²` functions on the two quotients correspond. -/
def parabolicCuspidalL2FunctionsToCanonical :
    QuotientParabolicCuspidalL2Functions F G hPD hG measuresU
        (quotientHaarMeasure F G S j) hInv ≃ₗ[ℂ]
      QuotientParabolicCuspidalL2Functions F G hPD hG measuresU (canonicalMeasure F G) hInv' where
  toFun f := ⟨continuousToCanonical hj f.val,
    (continuousToCanonical_mem_parabolicCuspidalL2_iff hj hPD hG measuresU hInv hInv'
      f.val).mpr f.property⟩
  invFun f := ⟨(continuousToCanonical hj).symm f.val,
    (continuousToCanonical_mem_parabolicCuspidalL2_iff hj hPD hG measuresU hInv hInv'
      _).mp (by rw [LinearEquiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((continuousToCanonical hj).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousToCanonical hj).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousToCanonical hj) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousToCanonical hj) _ _)

theorem parabolicCuspidalL2FunctionsToCanonical_rightAction (g : AdelicGroupPoints F G)
    (f : QuotientParabolicCuspidalL2Functions F G hPD hG measuresU
      (quotientHaarMeasure F G S j) hInv) :
    parabolicCuspidalL2FunctionsToCanonical hj hPD hG measuresU hInv hInv'
        (quotientParabolicCuspidalL2RightAction F G hPD hG measuresU _ hInv g f) =
      quotientParabolicCuspidalL2RightAction F G hPD hG measuresU _ hInv' g
        (parabolicCuspidalL2FunctionsToCanonical hj hPD hG measuresU hInv hInv' f) :=
  Subtype.ext (continuousToCanonical_rightAction hj g f.val)

/-- The function correspondence is `toCanonicalL2Equiv` on `L²` classes. -/
theorem quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsToCanonical
    (f : QuotientParabolicCuspidalL2Functions F G hPD hG measuresU
      (quotientHaarMeasure F G S j) hInv) :
    quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv'
        (parabolicCuspidalL2FunctionsToCanonical hj hPD hG measuresU hInv hInv' f) =
      toCanonicalL2Equiv hj (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU _ hInv f) :=
  rfl

set_option maxRecDepth 20000 in
/-- `toCanonicalL2Equiv` carries the continuous parabolic-vanishing image for any split
component of the restriction onto the canonical image. -/
theorem toCanonicalL2Equiv_mem_parabolicCuspidalL2Image_iff
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj φ ∈ quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU
        (canonicalMeasure F G) hInv' ↔
      φ ∈ quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU
        (quotientHaarMeasure F G S j) hInv := by
  rw [mem_quotientContinuousParabolicCuspidalL2Image,
    mem_quotientContinuousParabolicCuspidalL2Image]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(parabolicCuspidalL2FunctionsToCanonical hj hPD hG measuresU hInv hInv').symm f, ?_⟩
    apply (toCanonicalL2Equiv hj).injective
    rw [← quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsToCanonical hj hPD hG
      measuresU hInv hInv',
      LinearEquiv.apply_symm_apply, hf]
  · rintro ⟨f, rfl⟩
    exact ⟨parabolicCuspidalL2FunctionsToCanonical hj hPD hG measuresU hInv hInv' f,
      quotientParabolicCuspidalL2ToLp_parabolicCuspidalL2FunctionsToCanonical hj hPD hG
        measuresU hInv hInv' f⟩

end ParabolicTransport

section CuspFormTransport

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)
variable (hInv : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
  (hInv' : QuotientRightInvariant F G (canonicalMeasure F G))

theorem continuousToCanonical_mem_cuspidalFormL2_iff (f : C(Quotient F G S j, ℂ)) :
    continuousToCanonical hj f ∈ quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth
        hcalc hPD hG hrho hK hN (canonicalMeasure F G) hInv' ↔
      f ∈ quotientCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (quotientHaarMeasure F G S j) hInv := by
  rw [mem_quotientCuspidalFormL2Subrepresentation, mem_quotientCuspidalFormL2Subrepresentation,
    quotientContinuousPullback_continuousToCanonical, memLp_continuousToCanonical_iff]

/-- The continuous square-integrable `AdelicCuspidalForms` functions on the two quotients
correspond. -/
def cuspidalFormL2FunctionsToCanonical :
    QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (quotientHaarMeasure F G S j) hInv ≃ₗ[ℂ]
      QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (canonicalMeasure F G) hInv' where
  toFun f := ⟨continuousToCanonical hj f.val,
    (continuousToCanonical_mem_cuspidalFormL2_iff hj Kinf rho hsmooth hcalc hPD hG hrho hK hN
      hInv hInv' f.val).mpr f.property⟩
  invFun f := ⟨(continuousToCanonical hj).symm f.val,
    (continuousToCanonical_mem_cuspidalFormL2_iff hj Kinf rho hsmooth hcalc hPD hG hrho hK hN
      hInv hInv' _).mp (by rw [LinearEquiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((continuousToCanonical hj).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((continuousToCanonical hj).apply_symm_apply f.val)
  map_add' _ _ := Subtype.ext (map_add (continuousToCanonical hj) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (continuousToCanonical hj) _ _)

theorem cuspidalFormL2FunctionsToCanonical_finiteRightAction (c : FiniteAdelicGroupPoints F G)
    (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      (quotientHaarMeasure F G S j) hInv) :
    cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv hInv'
        (quotientCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
          _ hInv c f) =
      quotientCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv'
        c (cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
          hInv' f) :=
  Subtype.ext (continuousToCanonical_rightAction hj (AdelicGroupPoints.ofFinite F G c) f.val)

/-- The `AdelicCuspidalForms` correspondence is `toCanonicalL2Equiv` on `L²` classes. -/
theorem quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsToCanonical
    (f : QuotientCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      (quotientHaarMeasure F G S j) hInv) :
    quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv'
        (cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
          hInv' f) =
      toCanonicalL2Equiv hj
        (quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ hInv f) :=
  rfl

set_option maxRecDepth 20000 in
/-- `toCanonicalL2Equiv` carries the `AdelicCuspidalForms` image for any split component of
the restriction onto the canonical image. -/
theorem toCanonicalL2Equiv_mem_cuspidalFormL2Image_iff
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj φ ∈ quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho
        hK hN (canonicalMeasure F G) hInv' ↔
      φ ∈ quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (quotientHaarMeasure F G S j) hInv := by
  rw [mem_quotientCuspidalFormL2Image, mem_quotientCuspidalFormL2Image]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
      hInv').symm f, ?_⟩
    apply (toCanonicalL2Equiv hj).injective
    rw [← quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth
      hcalc hPD hG hrho hK hN hInv hInv',
      LinearEquiv.apply_symm_apply, hf]
  · rintro ⟨f, rfl⟩
    exact ⟨cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth hcalc hPD hG hrho hK hN hInv
      hInv' f, quotientCuspidalFormL2ToLp_cuspidalFormL2FunctionsToCanonical hj Kinf rho hsmooth
        hcalc hPD hG hrho hK hN hInv hInv' f⟩

end CuspFormTransport

end Transport

section Canonical

variable (F G)
variable (hCST : CentralSplitTorusCharacterStatement.{0})

section Parabolic

variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))

/-- The continuous parabolic-vanishing image in `L²([G])` for the canonical measure, as a
subrepresentation of `canonicalL2RightAction`. -/
def canonicalParabolicCuspidalL2Image : Subrepresentation (canonicalL2RightAction F G hCST hG) :=
  quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU (canonicalMeasure F G)
    (canonicalMeasure_rightInvariant F G hCST hG)

/-- Distinct continuous parabolic-vanishing functions give distinct canonical `L²` classes. -/
theorem canonicalParabolicCuspidalL2ToLp_injective :
    Function.Injective (quotientParabolicCuspidalL2ToLp F G hPD hG measuresU
      (canonicalMeasure F G) (canonicalMeasure_rightInvariant F G hCST hG)) := by
  have := canonicalMeasure_isOpenPosMeasure F G hCST hG
  exact quotientParabolicCuspidalL2ToLp_injective F G hPD hG measuresU _ _

variable {F G}

/-- `toCanonicalL2Equiv` carries the continuous parabolic-vanishing image for any split
component of the restriction onto `canonicalParabolicCuspidalL2Image`. -/
theorem toCanonicalL2Equiv_mem_canonicalParabolicCuspidalL2Image_iff
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hj : IsSplitComponent j)
    (hInv : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj φ ∈ canonicalParabolicCuspidalL2Image F G hCST hPD hG measuresU ↔
      φ ∈ quotientContinuousParabolicCuspidalL2Image F G hPD hG measuresU
        (quotientHaarMeasure F G S j) hInv :=
  toCanonicalL2Equiv_mem_parabolicCuspidalL2Image_iff hj hPD hG measuresU hInv _ φ

end Parabolic

section CuspForms

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)

/-- The image of square-integrable continuous `AdelicCuspidalForms` functions in `L²([G])`
for the canonical measure. -/
def canonicalCuspidalFormL2Image :
    Subrepresentation (rationalQuotientL2FiniteRightAction F G (canonicalMeasure F G)
      (canonicalMeasure_rightInvariant F G hCST hG)) :=
  quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
    (canonicalMeasure F G) (canonicalMeasure_rightInvariant F G hCST hG)

/-- Distinct continuous `AdelicCuspidalForms` functions give distinct canonical `L²` classes. -/
theorem canonicalCuspidalFormL2ToLp_injective :
    Function.Injective (quotientCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
      (canonicalMeasure F G) (canonicalMeasure_rightInvariant F G hCST hG)) := by
  have := canonicalMeasure_isOpenPosMeasure F G hCST hG
  exact quotientCuspidalFormL2ToLp_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN _ _

variable {F G}

/-- `toCanonicalL2Equiv` carries the `AdelicCuspidalForms` image for any split component of
the restriction onto `canonicalCuspidalFormL2Image`. -/
theorem toCanonicalL2Equiv_mem_canonicalCuspidalFormL2Image_iff
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hj : IsSplitComponent j)
    (hInv : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj φ ∈
        canonicalCuspidalFormL2Image F G hCST Kinf rho hsmooth hcalc hPD hG hrho hK hN ↔
      φ ∈ quotientCuspidalFormL2Image F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
        (quotientHaarMeasure F G S j) hInv :=
  toCanonicalL2Equiv_mem_cuspidalFormL2Image_iff hj Kinf rho hsmooth hcalc hPD hG hrho hK hN
    hInv _ φ

end CuspForms

section FullAE

variable (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)

/-- The almost-everywhere cuspidal subspace of `L²([G])` for the canonical measure. -/
def canonicalFullAEL2CuspidalSubmodule : Submodule ℂ (Lp ℂ 2 (canonicalMeasure F G)) :=
  haveI := canonical_finiteIndex F G hG
  splitComponentFullAEL2CuspidalSubmodule F G hPD hG
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

@[simp]
theorem mem_canonicalFullAEL2CuspidalSubmodule (φ : Lp ℂ 2 (canonicalMeasure F G)) :
    φ ∈ canonicalFullAEL2CuspidalSubmodule F G hCST hPD hG ↔
      φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S₀ j₀ (canonicalMeasure F G) :=
  Iff.rfl

/-- `canonicalL2Equiv` carries the published positive-torus locus of the chosen split component
of `G` onto the canonical cuspidal subspace. -/
theorem mem_canonicalFullAEL2CuspidalSubmodule_iff (φ : Lp ℂ 2 (canonicalMeasure F G)) :
    φ ∈ canonicalFullAEL2CuspidalSubmodule F G hCST hPD hG ↔
      (canonicalL2Equiv F G).symm φ ∈ fullAEL2CuspidalLocus F G hPD hG T₀ i₀ :=
  haveI := canonical_finiteIndex F G hG
  mem_splitComponentFullAEL2CuspidalSubmodule_iff F G hPD hG
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀ φ

theorem isClosed_canonicalFullAEL2CuspidalSubmodule :
    IsClosed (canonicalFullAEL2CuspidalSubmodule F G hCST hPD hG :
      Set (Lp ℂ 2 (canonicalMeasure F G))) :=
  haveI := canonical_finiteIndex F G hG
  isClosed_splitComponentFullAEL2CuspidalSubmodule_of_connectedReductive F G hPD hG
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

/-- The canonical cuspidal subspace as a subrepresentation of `canonicalL2RightAction`. -/
def canonicalFullAEL2CuspidalSubrepresentation :
    Subrepresentation (canonicalL2RightAction F G hCST hG) :=
  haveI := canonical_finiteIndex F G hG
  splitComponentReductiveFullAEL2CuspidalSubrepresentation F G hPD hG
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

/-- The orthogonal projection of `L²([G])` onto the canonical cuspidal subspace. -/
def canonicalFullAEL2CuspidalOrthogonalProjection :
    Lp ℂ 2 (canonicalMeasure F G) →L[ℂ] canonicalFullAEL2CuspidalSubmodule F G hCST hPD hG :=
  haveI := canonical_finiteIndex F G hG
  splitComponentFullAEL2CuspidalOrthogonalProjection F G hPD hG
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

/-- The orthogonal cuspidal projection as an intertwining map of `canonicalL2RightAction`. -/
def canonicalFullAEL2CuspidalProjectionIntertwiner :
    (canonicalL2RightAction F G hCST hG).IntertwiningMap
      (canonicalFullAEL2CuspidalSubrepresentation F G hCST hPD hG).toRepresentation :=
  haveI := canonical_finiteIndex F G hG
  splitComponentFullAEL2CuspidalProjectionIntertwiner F G hPD hG
    (canonical_characterRestrict_injective F G hCST hG) hj₀ hs₀

variable {F G}

/-- `toCanonicalL2Equiv` carries the cuspidal locus for any split component of the restriction
onto the canonical cuspidal subspace. -/
theorem toCanonicalL2Equiv_mem_canonicalFullAEL2CuspidalSubmodule_iff
    {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
    {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G} (hj : IsSplitComponent j)
    (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)) :
    toCanonicalL2Equiv hj φ ∈ canonicalFullAEL2CuspidalSubmodule F G hCST hPD hG ↔
      φ ∈ quotientFullAEL2CuspidalLocus F G hPD hG S j (quotientHaarMeasure F G S j) := by
  have := canonical_finiteIndex F G hG
  have hi := canonical_characterRestrict_injective F G hCST hG
  rw [mem_canonicalFullAEL2CuspidalSubmodule_iff,
    ← mem_splitComponentFullAEL2CuspidalSubmodule F G hPD hG hi hj hs₀,
    mem_splitComponentFullAEL2CuspidalSubmodule_iff F G hPD hG hi hj hs₀]
  have he : toCanonicalL2Equiv hj φ =
      canonicalL2Equiv F G ((splitComponentL2Equiv F G hj hs₀).symm φ) := by
    rw [canonicalL2Equiv, ← toCanonicalL2Equiv_splitComponentL2Equiv hj hs₀,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he, LinearIsometryEquiv.symm_apply_apply]

end FullAE

end Canonical

end Langlands.Global.RestrictionSplitCentre
