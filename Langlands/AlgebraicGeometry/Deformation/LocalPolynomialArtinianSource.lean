import Langlands.AlgebraicGeometry.Deformation.LocalAdicArtinianTests
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.FiniteType

/-! # Local polynomial sources for actual augmented Artinian tests -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry.Deformation.LocalPolynomialArtinianSource

variable {k K σ : Type u} [CommRing k] [Field K] [Algebra k K]
  (ε : MvPolynomial σ k →ₐ[k] K)

/-- The prime ideal belonging to the specified polynomial residue map. -/
abbrev residueIdeal : Ideal (MvPolynomial σ k) := RingHom.ker ε.toRingHom

instance : (residueIdeal ε).IsPrime := RingHom.ker_isPrime ε.toRingHom

/-- The polynomial ring localized at the kernel of the specified residue map. -/
abbrev ring := Localization.AtPrime (residueIdeal ε)

/-- The original scalar-preserving map from polynomials into their local source. -/
abbrev polynomialMap : MvPolynomial σ k →ₐ[k] ring ε :=
  Algebra.algHom k (MvPolynomial σ k) (ring ε)

/-- The specified residue map extends to the local polynomial source. -/
def augmentation : ring ε →ₐ[k] K :=
  IsLocalization.liftAlgHom (M := (residueIdeal ε).primeCompl)
    (f := ε) (fun y ↦ isUnit_iff_ne_zero.mpr y.property)

@[simp]
lemma augmentation_polynomialMap :
    (augmentation ε).comp (polynomialMap ε) = ε := by
  apply AlgHom.ext
  intro p
  exact IsLocalization.lift_eq _ p

/-- Surjectivity of the original presentation gives the prescribed residue field. -/
lemma augmentation_surjective (hε : Function.Surjective ε) :
    Function.Surjective (augmentation ε) := by
  intro x
  obtain ⟨p, hp⟩ := hε x
  exact ⟨polynomialMap ε p, (DFunLike.congr_fun (augmentation_polynomialMap ε) p).trans hp⟩

variable (A : ArtinianTest k K)

/-- All actual algebra maps from the local source that preserve the augmentation. -/
abbrev Maps := {α : ring ε →ₐ[k] A.algebra // A.augmentation.comp α = augmentation ε}

/-- Polynomial coordinates in an actual test, with the specified residue values. -/
abbrev Coordinates := {a : σ → A.algebra // ∀ i, A.augmentation (a i) = ε (MvPolynomial.X i)}

/-- Read the actual variable values of an augmentation-preserving local-source map. -/
def coordinates (α : Maps ε A) : Coordinates ε A :=
  ⟨fun i ↦ α.val (polynomialMap ε (MvPolynomial.X i)), fun i ↦ by
    change (A.augmentation.comp α.val) (polynomialMap ε (MvPolynomial.X i)) = _
    rw [α.property]
    exact DFunLike.congr_fun (augmentation_polynomialMap ε) (MvPolynomial.X i)⟩

private lemma coordinates_augmentation (a : Coordinates ε A) :
    A.augmentation.comp (MvPolynomial.aeval a.val) = ε := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa using a.property i

/-- Extend specified polynomial coordinates to the local source.
The augmentation detects the units needed for localization. -/
def extend (a : Coordinates ε A) : Maps ε A := by
  let hlocal : IsLocalHom A.augmentation.toRingHom :=
    IsLocalHom.of_surjective _ A.augmentation_surjective
  let α : ring ε →ₐ[k] A.algebra :=
    IsLocalization.liftAlgHom (M := (residueIdeal ε).primeCompl)
      (f := MvPolynomial.aeval a.val) (fun y ↦ by
        apply isUnit_of_map_unit A.augmentation.toRingHom
        apply isUnit_iff_ne_zero.mpr
        change (A.augmentation.comp (MvPolynomial.aeval a.val)) y.val ≠ 0
        rw [coordinates_augmentation ε A a]
        exact y.property)
  refine ⟨α, ?_⟩
  apply IsLocalization.algHom_ext (residueIdeal ε).primeCompl
  rw [AlgHom.comp_assoc, augmentation_polynomialMap]
  have hα : α.comp (polynomialMap ε) = MvPolynomial.aeval a.val := by
    apply AlgHom.ext
    intro p
    exact IsLocalization.lift_eq _ p
  rw [hα]
  exact coordinates_augmentation ε A a

@[simp]
lemma extend_polynomialMap (a : Coordinates ε A) :
    (extend ε A a).val.comp (polynomialMap ε) = MvPolynomial.aeval a.val := by
  apply AlgHom.ext
  intro p
  exact IsLocalization.lift_eq _ p

@[simp]
lemma coordinates_extend (a : Coordinates ε A) :
    coordinates ε A (extend ε A a) = a := by
  apply Subtype.ext
  funext i
  exact (DFunLike.congr_fun (extend_polynomialMap ε A a) (MvPolynomial.X i)).trans
    (MvPolynomial.aeval_X a.val i)

@[simp]
lemma extend_coordinates (α : Maps ε A) :
    extend ε A (coordinates ε A α) = α := by
  apply Subtype.ext
  apply IsLocalization.algHom_ext (residueIdeal ε).primeCompl
  rw [extend_polynomialMap]
  apply MvPolynomial.algHom_ext
  intro i
  exact MvPolynomial.aeval_X _ _

/-- All actual augmentation-preserving local-source maps are exactly their
variable values with the originally specified residues. -/
def coordinateEquiv : Maps ε A ≃ Coordinates ε A where
  toFun := coordinates ε A
  invFun := extend ε A
  left_inv := extend_coordinates ε A
  right_inv := coordinates_extend ε A

/-- Every actual test admits a map from the local polynomial source with
the prescribed augmentation, including nonsplit augmented tests. -/
lemma maps_nonempty : Nonempty (Maps ε A) := by
  choose a ha using fun i ↦ A.augmentation_surjective (ε (MvPolynomial.X i))
  exact ⟨extend ε A ⟨a, ha⟩⟩

variable {A} {B : ArtinianTest k K}

/-- Postcompose an actual local-source map by an actual test arrow. -/
def postcomp (q : A ⟶ B) (α : Maps ε A) : Maps ε B :=
  ⟨(ArtinianTest.toAlgHom q).comp α.val, by
    rw [← AlgHom.comp_assoc, ArtinianTest.augmentation_comp, α.property]⟩

/-- Every compatible local-source map lifts across every surjective actual
test arrow; no coefficient-field section is used. -/
lemma postcomp_surjective (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q)) :
    Function.Surjective (postcomp ε q) := by
  intro β
  choose a ha using fun i ↦ hq ((coordinates ε B β).val i)
  let c : Coordinates ε A := ⟨a, fun i ↦ by
    rw [← ArtinianTest.augmentation_comp q]
    change B.augmentation (ArtinianTest.toAlgHom q (a i)) = _
    rw [ha i]
    exact (coordinates ε B β).property i⟩
  refine ⟨extend ε A c, ?_⟩
  apply (coordinateEquiv ε B).injective
  apply Subtype.ext
  funext i
  change ArtinianTest.toAlgHom q
    ((extend ε A c).val (polynomialMap ε (MvPolynomial.X i))) = _
  have hc := DFunLike.congr_fun (extend_polynomialMap ε A c) (MvPolynomial.X i)
  change (extend ε A c).val (polynomialMap ε (MvPolynomial.X i)) = _ at hc
  rw [hc, MvPolynomial.aeval_X]
  exact ha i

variable [Finite σ] [IsNoetherianRing k] (hε : Function.Surjective ε)

/-- The actual finite adic test of the noetherian local polynomial source. -/
def test (n : ℕ) : ArtinianTest k K :=
  LocalAdicArtinianTests.test (augmentation ε) (augmentation_surjective ε hε) n

/-- The original quotient map from the local polynomial source. -/
abbrev projection (n : ℕ) : ring ε →ₐ[k] (test ε hε n).algebra :=
  LocalAdicArtinianTests.projection (augmentation ε) (augmentation_surjective ε hε) n

/-- The actual transition from a later local-polynomial adic test. -/
abbrev transition {n m : ℕ} (hnm : n ≤ m) : test ε hε m ⟶ test ε hε n :=
  LocalAdicArtinianTests.transition (augmentation ε) (augmentation_surjective ε hε) hnm

/-- An actual finite-stage test arrow gives its original compatible source map. -/
def ofStage {n : ℕ} (α : test ε hε n ⟶ A) : Maps ε A :=
  ⟨(ArtinianTest.toAlgHom α).comp (projection ε hε n), by
    rw [← AlgHom.comp_assoc, ArtinianTest.augmentation_comp]
    exact LocalAdicArtinianTests.augmentation_projection _ _ n⟩

/-- Every actual test receives an actual arrow from some finite stage
of the same local polynomial source. -/
lemma exists_stage_map : ∃ n : ℕ, Nonempty (test ε hε n ⟶ A) := by
  obtain ⟨a⟩ := maps_nonempty ε A
  obtain ⟨n, α, _⟩ := LocalAdicArtinianTests.exists_unique_factor (augmentation ε)
    (augmentation_surjective ε hε) a.val a.property
  exact ⟨n, ⟨α⟩⟩

/-- Every actual finite-stage arrow lifts through a surjective test arrow
after passing to a sufficiently late stage of the same actual adic tower. -/
theorem exists_stage_lift {n : ℕ} (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q))
    (β : test ε hε n ⟶ B) :
    ∃ (m : ℕ) (hnm : n ≤ m) (α : test ε hε m ⟶ A),
      α ≫ q = transition ε hε hnm ≫ β := by
  obtain ⟨a, ha⟩ := postcomp_surjective ε q hq (ofStage ε hε β)
  obtain ⟨t, ht⟩ := LocalAdicArtinianTests.exists_bound (augmentation ε)
    (augmentation_surjective ε hε) a.val a.property
  let m := max n t
  have hn : n ≤ m := Nat.le_max_left n t
  have ht' : IsLocalRing.maximalIdeal (ring ε) ^ (m + 1) ≤
      RingHom.ker a.val.toRingHom :=
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_max_right n t) 1)).trans ht
  let α : test ε hε m ⟶ A :=
    LocalAdicArtinianTests.factor (augmentation ε) (augmentation_surjective ε hε)
      a.val a.property m ht'
  refine ⟨m, hn, α, ?_⟩
  apply ArtinianTest.hom_ext
  apply Ideal.Quotient.algHom_ext
  change (ArtinianTest.toAlgHom (α ≫ q)).comp (projection ε hε m) =
    (ArtinianTest.toAlgHom (transition ε hε hn ≫ β)).comp (projection ε hε m)
  calc
    (ArtinianTest.toAlgHom (α ≫ q)).comp (projection ε hε m) =
        (ArtinianTest.toAlgHom q).comp a.val := by
      rw [ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc]
      exact congrArg ((ArtinianTest.toAlgHom q).comp)
        (LocalAdicArtinianTests.factor_projection _ _ _ _ _ ht')
    _ = (ofStage ε hε β).val := congrArg Subtype.val ha
    _ = (ArtinianTest.toAlgHom (transition ε hε hn ≫ β)).comp
        (projection ε hε m) := by
      rw [ArtinianTest.toAlgHom_comp, AlgHom.comp_assoc]
      exact congrArg ((ArtinianTest.toAlgHom β).comp)
        (LocalAdicArtinianTests.projection_transition (augmentation ε)
          (augmentation_surjective ε hε) hn).symm

section FiniteTypeResidue

variable (k K) [Algebra.FiniteType k K]

/-- Choose a finite polynomial presentation of the original residue algebra. -/
def finitePresentation :
    Σ d : ℕ, {φ : MvPolynomial (ULift.{u} (Fin d)) k →ₐ[k] K //
      Function.Surjective φ} := by
  have h := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k K)
  let d := Classical.choose h
  let φ := Classical.choose (Classical.choose_spec h)
  have hφ : Function.Surjective φ := Classical.choose_spec (Classical.choose_spec h)
  let e := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
  exact ⟨d, φ.comp e.toAlgHom, hφ.comp e.surjective⟩

/-- The actual Artinian-test tower of a chosen finite polynomial residue
presentation. The original `k`-structure is retained even for inseparable `K/k`. -/
def finiteTypeTest (n : ℕ) : ArtinianTest k K :=
  test (σ := ULift.{u} (Fin (finitePresentation k K).1))
    (finitePresentation k K).2.val (finitePresentation k K).2.property n

/-- Every actual test receives an arrow from the chosen finite-residue tower. -/
lemma finiteType_exists_stage_map (A : ArtinianTest k K) :
    ∃ n : ℕ, Nonempty (finiteTypeTest k K n ⟶ A) :=
  exists_stage_map (σ := ULift.{u} (Fin (finitePresentation k K).1))
    (finitePresentation k K).2.val (finitePresentation k K).2.property

/-- The chosen finite-residue tower lifts actual finite-stage arrows across
every surjective actual test arrow, after moving to a later stage. -/
theorem finiteType_exists_stage_lift {A B : ArtinianTest k K}
    {n : ℕ} (q : A ⟶ B) (hq : Function.Surjective (ArtinianTest.toAlgHom q))
    (β : finiteTypeTest k K n ⟶ B) :
    ∃ (m : ℕ) (hnm : n ≤ m) (α : finiteTypeTest k K m ⟶ A),
      α ≫ q =
        transition (σ := ULift.{u} (Fin (finitePresentation k K).1))
          (finitePresentation k K).2.val (finitePresentation k K).2.property hnm ≫ β :=
  exists_stage_lift (σ := ULift.{u} (Fin (finitePresentation k K).1))
    (finitePresentation k K).2.val (finitePresentation k K).2.property q hq β

end FiniteTypeResidue

end Langlands.AlgebraicGeometry.Deformation.LocalPolynomialArtinianSource
