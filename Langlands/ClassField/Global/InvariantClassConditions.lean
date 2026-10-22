import Langlands.ClassField.Global.InvariantStatement
import Langlands.ClassField.Global.CohomologyMaps

/-! # Global invariant conditions on actual cohomology classes -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

namespace FundamentalClass

/-- Restriction multiplies the invariant by the base-extension degree. -/
def InvariantRestrictionOnClasses (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F F' E : Type u) [Field F] [Field F'] [Field E]
    [NumberField F] [NumberField F'] [NumberField E]
    [Algebra F F'] [Algebra F E] [Algebra F' E] [IsScalarTower F F' E] [IsGalois F E],
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    ∀ a : relativeIdeleClassCohomology F E 2,
      inv F' E (relativeIdeleClassRestriction F F' E 2 a) =
        Module.finrank F F' • inv F E a

/-- Inflation through the actual idele-class inclusion preserves the invariant. -/
def InvariantInflationOnClasses (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F E L : Type u) [Field F] [Field E] [Field L]
    [NumberField F] [NumberField E] [NumberField L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsGalois F E] [IsGalois F L],
    ∀ a : relativeIdeleClassCohomology F E 2,
      inv F L (relativeIdeleClassInflation F E L 2 a) = inv F E a

/-- Equality of a local image and a restricted global class is detected by invariants. -/
def InvariantLocalOnClasses (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [IsGalois (padicField v).Carrier (w.adicCompletion E)],
    haveI : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
      FiniteExtension.local_finite v w
    ∀ (a : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2)
      (b : relativeIdeleClassCohomology F E 2),
      localIdeleClassMap v w 2 a = decompositionRestriction v w 2 b ↔
        (Module.finrank F E /
          Module.finrank (padicField v).Carrier (w.adicCompletion E)) • inv F E b =
            (I (residuePrime v)).relative (padicField v) (w.adicCompletion E) a

/-- The image and functoriality conditions, expressed on actual cohomology classes. -/
def IsGlobalInvariantOnClasses
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (inv : GlobalInvariantMaps.{u}) : Prop :=
  InvariantImages inv ∧ InvariantRestrictionOnClasses inv ∧
    InvariantInflationOnClasses inv ∧ InvariantLocalOnClasses I inv

/-- Injectivity makes the cochain restriction equivalence equivalent to its class formula. -/
theorem invariantRestriction_iff_classes (inv : GlobalInvariantMaps.{u})
    (hi : InvariantImages inv) :
    InvariantRestriction inv ↔ InvariantRestrictionOnClasses inv := by
  constructor
  · intro h F F' E _ _ _ _ _ _ _ _ _ _ _ a
    let : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    obtain ⟨x, rfl⟩ := RelativeIdeleCocycle.cohomologyClass_surjective a
    obtain ⟨y, hy⟩ := RelativeIdeleCocycle.cohomologyClass_surjective
      (relativeIdeleClassRestriction F F' E 2 x.cohomologyClass)
    rw [← hy]
    exact (h F F' E x y).1
      ((relativeIdeleClassRestriction_cohomologyClass_eq_iff x y).1 hy.symm)
  · intro h F F' E _ _ _ _ _ _ _ _ _ _ _ x y
    let : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    rw [← relativeIdeleClassRestriction_cohomologyClass_eq_iff]
    constructor
    · intro hxy
      rw [← hxy]
      exact h F F' E x.cohomologyClass
    · intro hxy
      apply (hi F' E).1
      exact (h F F' E x.cohomologyClass).trans hxy.symm

/-- Injectivity recovers every power in the cochain inflation condition from one formula. -/
theorem invariantInflation_iff_classes (inv : GlobalInvariantMaps.{u})
    (hi : InvariantImages inv) :
    InvariantInflation inv ↔ InvariantInflationOnClasses inv := by
  constructor
  · intro h F E L _ _ _ _ _ _ _ _ _ _ _ _ a
    obtain ⟨x, rfl⟩ := RelativeIdeleCocycle.cohomologyClass_surjective a
    obtain ⟨y, hy⟩ := RelativeIdeleCocycle.cohomologyClass_surjective
      (relativeIdeleClassInflation F E L 2 x.cohomologyClass)
    have hxy := (relativeIdeleClassInflation_cohomologyClass_eq_iff x y 1).1
      (by simpa using hy.symm)
    simpa only [one_nsmul, hy] using (h F E L x y 1).1 hxy
  · intro h F E L _ _ _ _ _ _ _ _ _ _ _ _ x y m
    rw [← relativeIdeleClassInflation_cohomologyClass_eq_iff]
    constructor
    · intro hxy
      calc
        m • inv F L y.cohomologyClass = inv F L (m • y.cohomologyClass) :=
          (map_nsmul _ _ _).symm
        _ = inv F L (relativeIdeleClassInflation F E L 2 x.cohomologyClass) :=
          congrArg (inv F L) hxy.symm
        _ = inv F E x.cohomologyClass := h F E L x.cohomologyClass
    · intro hxy
      apply (hi F L).1
      rw [map_nsmul]
      exact (h F E L x.cohomologyClass).trans hxy.symm

/-- Both local formulations quantify over all representatives of all actual classes. -/
theorem invariantLocal_iff_classes
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (inv : GlobalInvariantMaps.{u}) :
    InvariantLocal I inv ↔ InvariantLocalOnClasses I inv := by
  constructor
  · intro h F _ _ E _ _ _ _ v w _ _ a b
    induction a using groupCohomology.H2_induction_on with
    | h z =>
      obtain ⟨y, rfl⟩ := RelativeIdeleCocycle.cohomologyClass_surjective b
      exact (localIdeleClassMap_eq_decompositionRestriction_iff v w z y).trans
        (h F E v w z y)
  · intro h F _ _ E _ _ _ _ v w _ _ z y
    exact (localIdeleClassMap_eq_decompositionRestriction_iff v w z y).symm.trans
      (h F E v w (groupCohomology.H2π _ z) y.cohomologyClass)

/-- The cochain conditions and the conditions on classes describe the same maps. -/
theorem isGlobalInvariant_iff_classes
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (inv : GlobalInvariantMaps.{u}) :
    IsGlobalInvariant I inv ↔ IsGlobalInvariantOnClasses I inv := by
  constructor
  · rintro ⟨hi, hr, hf, hl⟩
    exact ⟨hi, (invariantRestriction_iff_classes inv hi).1 hr,
      (invariantInflation_iff_classes inv hi).1 hf, (invariantLocal_iff_classes I inv).1 hl⟩
  · rintro ⟨hi, hr, hf, hl⟩
    exact ⟨hi, (invariantRestriction_iff_classes inv hi).2 hr,
      (invariantInflation_iff_classes inv hi).2 hf, (invariantLocal_iff_classes I inv).2 hl⟩

end FundamentalClass

open FundamentalClass in
/-- The global invariant existence obligation, using the actual maps on cohomology. -/
def GlobalInvariantClassStatement : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∃ inv : GlobalInvariantMaps.{u}, IsGlobalInvariantOnClasses I inv

/-- Replacing the cochain relations by class formulas leaves the existence target unchanged. -/
theorem globalInvariantStatement_iff_classes :
    GlobalInvariantStatement.{u} ↔ GlobalInvariantClassStatement.{u} := by
  constructor
  · intro h I hI
    obtain ⟨inv, hinv⟩ := h I hI
    exact ⟨inv, (FundamentalClass.isGlobalInvariant_iff_classes I inv).1 hinv⟩
  · intro h I hI
    obtain ⟨inv, hinv⟩ := h I hI
    exact ⟨inv, (FundamentalClass.isGlobalInvariant_iff_classes I inv).2 hinv⟩

end Langlands.ClassField.Global
