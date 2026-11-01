import Langlands.Representation.Aubert.CorrectedOrbitCutData
import Langlands.Representation.Geometric.ParabolicOrbitCompactComparison

/-! Actual cross-cut quotient coordinates, coefficients and integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.QuotientIntegration

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- A continuous group equivalence carrying the actual subgroups induces a
homeomorphism on their actual left quotients. -/
def leftQuotientHomeomorph (e : G ≃ₜ* H) (P : Subgroup G) (Q : Subgroup H)
    (h : ∀ x, e x ∈ Q ↔ x ∈ P) :
    Induction.LeftQuotient P ≃ₜ Induction.LeftQuotient Q where
  toFun := Quotient.map' e (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    simpa only [← map_inv, ← map_mul] using (h (y * x⁻¹)).mpr hxy)
  invFun := Quotient.map' e.symm (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    apply (h _).mp
    simpa only [map_mul, map_inv, e.apply_symm_apply] using hxy)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (leftQuotientMap P) (e.symm_apply_apply x)
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (leftQuotientMap Q) (e.apply_symm_apply x)
  continuous_toFun := e.continuous.quotient_map' _
  continuous_invFun := e.symm.continuous.quotient_map' _

@[simp]
theorem leftQuotientHomeomorph_mk (e : G ≃ₜ* H) (P : Subgroup G) (Q : Subgroup H)
    (h : ∀ x, e x ∈ Q ↔ x ∈ P) (x : G) :
    leftQuotientHomeomorph e P Q h (leftQuotientMap P x) =
      leftQuotientMap Q (e x) := rfl

end Langlands.QuotientIntegration

namespace Langlands.Geometric

open GeneralLinear Induction

universe uF

variable (F : Type uF) [CommRing F] [TopologicalSpace F]
  {n : ℕ} (B D C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- Both nested kernels use the same actual target-radical coordinate. -/
def parabolicOrbitNestedKernelCutEquiv :
    (parabolicOrbitStagesRetraction F B C w).ker ≃ₜ*
      (parabolicOrbitStagesRetraction F D C w).ker :=
  (parabolicOrbitNestedRadicalEquiv F B C w).trans
    (parabolicOrbitNestedRadicalEquiv F D C w).symm

@[simp]
theorem parabolicOrbitNestedKernelCutEquiv_val
    (x : (parabolicOrbitStagesRetraction F B C w).ker) :
    (parabolicOrbitNestedKernelCutEquiv F B D C w x).val.val = x.val.val := rfl

/-- Across source cuts the kernel equivalence preserves the actual intersection. -/
theorem parabolicOrbitNestedKernelCutEquiv_mem
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w)
    (x : (parabolicOrbitStagesRetraction F B C w).ker) :
    parabolicOrbitNestedKernelCutEquiv F B D C w x ∈
        parabolicOrbitNestedIntersection F D C w ↔
      x ∈ parabolicOrbitNestedIntersection F B C w := by
  change parabolicOrbitNestedRadicalEquiv F B C w x ∈
      parabolicOrbitRadicalIntersection F D C w ↔
    parabolicOrbitNestedRadicalEquiv F B C w x ∈
      parabolicOrbitRadicalIntersection F B C w
  rw [parabolicOrbitRadicalIntersection_eq_of_sourceCuts C h hw]

/-- The common target-radical coordinate identifies the two actual quotient
domains used in the source-cut orbital integrals. -/
def parabolicOrbitNestedQuotientCutHomeomorph
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w) :
    QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F B C w) ≃ₜ
      QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F D C w) :=
  QuotientIntegration.leftQuotientHomeomorph
    (parabolicOrbitNestedKernelCutEquiv F B D C w)
    (parabolicOrbitNestedIntersection F B C w)
    (parabolicOrbitNestedIntersection F D C w)
    (parabolicOrbitNestedKernelCutEquiv_mem F B D C w h hw)

@[simp]
theorem parabolicOrbitNestedQuotientCutHomeomorph_mk
    (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w)
    (x : (parabolicOrbitStagesRetraction F B C w).ker) :
    parabolicOrbitNestedQuotientCutHomeomorph F B D C w h hw
        (quotientMap (parabolicOrbitNestedIntersection F B C w) x) =
      quotientMap (parabolicOrbitNestedIntersection F D C w)
        (parabolicOrbitNestedKernelCutEquiv F B D C w x) := rfl

end Langlands.Geometric

namespace Langlands.Aubert.Support

open GeneralLinear Geometric Induction

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
  (B D C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The actual positive-half inducing coefficient restricted to the nested
radical intersection, for normalized induction of normalized Jacquet. -/
abbrev cutOrbitNestedCoefficient (B : BlockShape n) :=
  parabolicOrbitNestedCoefficient F.Carrier B C w (T.leviHalfModulus B)
    (T.normalizedJacquet B ρ)

variable (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w)

/-- Actual projection on the source Jacquet representatives descends through
the two actual orbit-intersection coinvariant relations. -/
def cutOrbitCoefficientMap :
    Representation.Coinvariants (cutOrbitNestedCoefficient T ρ C w B) →ₗ[ℂ]
      Representation.Coinvariants (cutOrbitNestedCoefficient T ρ C w D) :=
  by
    let := T.topology
    exact Representation.Coinvariants.lift _
      ((Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)).comp
        (Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h)))
      (fun i => LinearMap.ext fun x => by
        let iD : parabolicOrbitNestedIntersection F.Carrier D C w :=
          ⟨parabolicOrbitNestedKernelCutEquiv F.Carrier B D C w i.val,
            (parabolicOrbitNestedKernelCutEquiv_mem F.Carrier B D C w h hw i.val).mpr
              i.property⟩
        let b := stabilizerToInducing (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier w)
          (parabolicOrbitNestedInclusion F.Carrier B C w
            (parabolicOrbitNestedIntersectionInclusion F.Carrier B C w i))
        let d := stabilizerToInducing (D.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier w)
          (parabolicOrbitNestedInclusion F.Carrier D C w
            (parabolicOrbitNestedIntersectionInclusion F.Carrier D C w iD))
        obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
        change Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
            (Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h)
              (Transition.inducing T B ρ b (B.jacquetMk ρ v))) =
          Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
            (Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h)
              (B.jacquetMk ρ v))
        rw [Transition.inducing_mk, Transition.quotient_mk, Transition.quotient_mk]
        have hi := Representation.Coinvariants.mk_self_apply
          (cutOrbitNestedCoefficient T ρ C w D) iD (D.jacquetMk ρ v)
        change Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
            (Transition.inducing T D ρ d (D.jacquetMk ρ v)) =
          Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
            (D.jacquetMk ρ v) at hi
        rw [Transition.inducing_mk] at hi
        exact hi)

@[simp]
theorem cutOrbitCoefficientMap_mk (x : B.JacquetModule ρ) :
    cutOrbitCoefficientMap T ρ B D C w h hw
        (Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w B) x) =
      Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
        (Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h) x) := rfl

section Integrals

open MeasureTheory HarmonicAnalysis QuotientIntegration

variable [TopologicalSpace F.Carrier] [IsTopologicalRing F.Carrier]

local instance (E : BlockShape n) : MeasurableSpace
    (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F.Carrier E C w)) := borel _
local instance (E : BlockShape n) : BorelSpace
    (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F.Carrier E C w)) := ⟨rfl⟩

/-- The genuine descended simple functions commute with the source-cut
coefficient projection on their common actual quotient coordinates. -/
theorem cutOrbitSimple_comp
    (fB : CompactFunctions (parabolicOrbitNestedIntersection F.Carrier B C w)
      (cutOrbitNestedCoefficient T ρ C w B))
    (fD : CompactFunctions (parabolicOrbitNestedIntersection F.Carrier D C w)
      (cutOrbitNestedCoefficient T ρ C w D))
    (hf : ∀ x : (parabolicOrbitStagesRetraction F.Carrier B C w).ker,
      eval _ _ fD.val (parabolicOrbitNestedKernelCutEquiv F.Carrier B D C w x) =
        Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ fB.val x)) :
    (quotientCoinvariantSimple _ _ fD).comp
        (parabolicOrbitNestedQuotientCutHomeomorph F.Carrier B D C w h hw)
        (parabolicOrbitNestedQuotientCutHomeomorph F.Carrier B D C w h hw).continuous.measurable =
      (quotientCoinvariantSimple _ _ fB).map
        (cutOrbitCoefficientMap T ρ B D C w h hw) := by
  ext q
  induction q using Quotient.inductionOn with
  | h x =>
    change Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
        (eval _ _ fD.val (parabolicOrbitNestedKernelCutEquiv F.Carrier B D C w x)) =
      Representation.Coinvariants.mk (cutOrbitNestedCoefficient T ρ C w D)
        (Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ fB.val x))
    exact congrArg (Representation.Coinvariants.mk _) (hf x)

/-- A single measure and its actual pushforward make the cross-cut integral
square commute, with no separately chosen normalization. -/
theorem cutOrbitIntegral_map
    (ν : Measure (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F.Carrier B C w)))
    [IsFiniteMeasureOnCompacts ν]
    (fB : CompactFunctions (parabolicOrbitNestedIntersection F.Carrier B C w)
      (cutOrbitNestedCoefficient T ρ C w B))
    (fD : CompactFunctions (parabolicOrbitNestedIntersection F.Carrier D C w)
      (cutOrbitNestedCoefficient T ρ C w D))
    (hf : ∀ x : (parabolicOrbitStagesRetraction F.Carrier B C w).ker,
      eval _ _ fD.val (parabolicOrbitNestedKernelCutEquiv F.Carrier B D C w x) =
        Transition.quotient ρ (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ fB.val x)) :
    AlgebraicIntegral.integral
        (Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F.Carrier B D C w h hw) ν)
        (quotientCoinvariantSimple _ _ fD) =
      cutOrbitCoefficientMap T ρ B D C w h hw
        (AlgebraicIntegral.integral ν (quotientCoinvariantSimple _ _ fB)) := by
  rw [← AlgebraicIntegral.integral_comp _ _
    (parabolicOrbitNestedQuotientCutHomeomorph F.Carrier B D C w h hw).continuous.measurable,
    cutOrbitSimple_comp T ρ B D C w h hw fB fD hf]
  exact AlgebraicIntegral.integral_linearMap _
    (quotientCoinvariantSimple_finMeasSupp _ _ ν fB) _

end Integrals

end Langlands.Aubert.Support

namespace Langlands.Aubert.Support

open GeneralLinear Geometric Induction MeasureTheory QuotientIntegration HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
  (B D C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- The actual compact-orbit inducing coefficient for a cut term. -/
abbrev cutOrbitCoefficient :=
  parabolicOrbitCoefficient F.Carrier B C w (T.leviHalfModulus B)
    (T.normalizedJacquet B (letI := T.topology; A.representation))

/-- The genuine compact kernel slice supplied by induction in stages. -/
def cutOrbitKernelSlice :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w) →
      C.Levi F.Carrier →
        CompactFunctions (parabolicOrbitNestedIntersection F.Carrier B C w)
          (cutOrbitNestedCoefficient T A.representation C w B) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.parabolicLocallyCompactSpace C
  have hσ : IsSmooth (cutOrbitCoefficient T A B C w) :=
    isSmooth_comp (parabolicOrbitToSourceLevi F.Carrier B C w)
      (continuous_parabolicOrbitToSourceLevi F.Carrier B C w)
      ((isSmooth_twist_iff (T.leviHalfModulus B) _
        (T.isOpen_ker_leviHalfModulus B)).mpr
          ((T.normalizedJacquetFunctor B).obj A).isSmooth)
  exact splitStagesKernelSlice
    (C.leviProjection F.Carrier) (C.leviInParabolic F.Carrier)
    (C.leviProjection_section F.Carrier)
    (C.leviProjectionContinuous F.Carrier).continuous
    (C.leviInParabolicContinuous F.Carrier).continuous
    (parabolicOrbitStages F.Carrier B C w)
    (parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_kernel_le F.Carrier B C w)
    (parabolicOrbitStabilizer_le_stages F.Carrier B C w)
    (isClosed_parabolicOrbitStages F.Carrier B C w)
    (isClosed_parabolicOrbitStabilizer F.Carrier B C w)
    (parabolicOrbitStages_section_mem F.Carrier B C w)
    (cutOrbitCoefficient T A B C w) hσ

@[simp]
theorem cutOrbitKernelSlice_eval :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (f : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w))
      (l : C.Levi F.Carrier) (x : (parabolicOrbitStagesRetraction F.Carrier B C w).ker),
      eval _ _ (cutOrbitKernelSlice T A B C w f l).val x =
        eval _ _ f.val (x.val.val * C.leviInParabolic F.Carrier l) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro f l x
  rfl

/-- The actual descended simple integrand of a compact orbit function at a
Levi point, rather than an independently supplied family of simple functions. -/
def cutOrbitIntegrand :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w) →
      C.Levi F.Carrier →
        SimpleFunc (QuotientIntegration.LeftQuotient
          (parabolicOrbitNestedIntersection F.Carrier B C w))
          (Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
  let : BorelSpace (QuotientIntegration.LeftQuotient
    (parabolicOrbitNestedIntersection F.Carrier B C w)) := ⟨rfl⟩
  intro f l
  exact quotientCoinvariantSimple _ _ (cutOrbitKernelSlice T A B C w f l)

@[simp]
theorem cutOrbitIntegrand_mk :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    ∀ (f : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w))
      (l : C.Levi F.Carrier) (x : (parabolicOrbitStagesRetraction F.Carrier B C w).ker),
      cutOrbitIntegrand T A B C w f l
          (quotientMap (parabolicOrbitNestedIntersection F.Carrier B C w) x) =
        Representation.Coinvariants.mk (cutOrbitNestedCoefficient T A.representation C w B)
          (eval _ _ f.val (x.val.val * C.leviInParabolic F.Carrier l)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro f l x
  rfl

/-- The actual compact stages slices commute with the source-cut projection,
after integration against one quotient measure and its pushforward. -/
theorem cutOrbitStagesIntegral_map (h : B.cuts ⊆ D.cuts)
    (hw : TypeASolomon.SourceIncreasing B w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier B C w)) := borel _
    letI : MeasurableSpace (QuotientIntegration.LeftQuotient
      (parabolicOrbitNestedIntersection F.Carrier D C w)) := borel _
    ∀ (ν : Measure (QuotientIntegration.LeftQuotient
        (parabolicOrbitNestedIntersection F.Carrier B C w)))
      [IsFiniteMeasureOnCompacts ν]
      (fB : CompactFunctions (parabolicOrbitStabilizer F.Carrier B C w)
        (cutOrbitCoefficient T A B C w))
      (fD : CompactFunctions (parabolicOrbitStabilizer F.Carrier D C w)
        (cutOrbitCoefficient T A D C w)),
      (∀ q : C.parabolic F.Carrier, eval _ _ fD.val q =
        Transition.quotient A.representation (unipotentSubgroup_le_of_cuts_subset h)
          (eval _ _ fB.val q)) →
      ∀ l : C.Levi F.Carrier,
        AlgebraicIntegral.integral
            (Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F.Carrier B D C w h hw) ν)
            (cutOrbitIntegrand T A D C w fD l) =
          cutOrbitCoefficientMap T A.representation B D C w h hw
            (AlgebraicIntegral.integral ν (cutOrbitIntegrand T A B C w fB l)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ν hν fB fD hf l
  apply cutOrbitIntegral_map T A.representation B D C w h hw ν
    (cutOrbitKernelSlice T A B C w fB l) (cutOrbitKernelSlice T A D C w fD l)
  intro x
  change eval _ _ fD.val (x.val.val * C.leviInParabolic F.Carrier l) =
    Transition.quotient A.representation (unipotentSubgroup_le_of_cuts_subset h)
      (eval _ _ fB.val (x.val.val * C.leviInParabolic F.Carrier l))
  exact hf _

end Langlands.Aubert.Support
