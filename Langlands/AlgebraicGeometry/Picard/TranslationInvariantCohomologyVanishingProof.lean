import Langlands.AlgebraicGeometry.Picard.TranslationInvariantCohomologyVanishingStatement
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingProof
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantPullbackIdentitiesProof
import Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackSplitRetractionProof

/-! # Cohomology vanishing for nontrivial translation-invariant line bundles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- The structural section of multiplication is the first coordinate inclusion. -/
private theorem multiplicationSection_comp_multiplication
    (S : Scheme.{u}) (A : AbelianScheme S) :
    Limits.prod.lift (𝟙 A.X) (1 : A.X ⟶ A.X) ≫
        ((Limits.prod.fst : A.X ⨯ A.X ⟶ A.X) *
          (Limits.prod.snd : A.X ⨯ A.X ⟶ A.X)) = 𝟙 A.X := by
  rw [MonObj.comp_mul, Limits.prod.lift_fst, Limits.prod.lift_snd, mul_one]

/-- Actual cohomology pullback along multiplication is a monomorphism. -/
private theorem multiplicationPullbackMono
    (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
    (M : A.X.left.Modules) (n : ℕ) :
    Mono (DerivedSections.relativeCohomologyPullback
      ((Limits.prod.fst : A.X ⨯ A.X ⟶ A.X) *
        (Limits.prod.snd : A.X ⨯ A.X ⟶ A.X)) M n) := by
  let m : A.X ⨯ A.X ⟶ A.X :=
    (Limits.prod.fst : A.X ⨯ A.X ⟶ A.X) *
      (Limits.prod.snd : A.X ⨯ A.X ⟶ A.X)
  let j : A.X ⟶ A.X ⨯ A.X := Limits.prod.lift (𝟙 A.X) (1 : A.X ⟶ A.X)
  have w : j ≫ m = 𝟙 A.X := multiplicationSection_comp_multiplication _ A
  exact (show SplitMono (DerivedSections.relativeCohomologyPullback m M n) from
    { retraction :=
        DerivedSections.relativeCohomologyPullback j
          ((Scheme.Modules.pullback m.left).obj M) n ≫
        (DerivedSections.relativeCohomology A.X.hom n).map
          ((DerivedSections.relativeCohomologySplitCoefficientIso m j w).hom.app M)
      id := DerivedSections.relativeCohomologyPullbackSplitRetractionStatement R m j w M n }).mono

/-- The Künneth induction using monicity of multiplication pullback. -/
private theorem translationInvariantCohomologyVanishing_of_multiplicationPullbackMono
    (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left)
    (hL : GroupScheme.IsTranslationInvariant A.toGrp L)
    (hne : ¬ Nonempty (L ≅ LineBundle.trivial A.X.left))
    (hmono : ∀ n : ℕ, Mono (DerivedSections.relativeCohomologyPullback
      ((Limits.prod.fst : A.X ⨯ A.X ⟶ A.X) *
        (Limits.prod.snd : A.X ⨯ A.X ⟶ A.X)) L.obj n)) :
    ∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj L.obj) := by
  have h0 := algClosedFieldTranslationInvariantH0Vanishing K A L hL hne
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact h0
    · let P : Over (Spec (CommRingCat.of K)) := A.X ⨯ A.X
      let m : P ⟶ A.X :=
        (Limits.prod.fst : P ⟶ A.X) * (Limits.prod.snd : P ⟶ A.X)
      have hs (ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
          Subsingleton (TensorProduct K
            ((DerivedSections.relativeCohomology A.X.hom ab.1.1).obj L.obj)
            ((DerivedSections.relativeCohomology A.X.hom ab.1.2).obj L.obj)) := by
        by_cases ha : ab.1.1 < n
        · have := ModuleCat.subsingleton_of_isZero (ih ab.1.1 ha)
          infer_instance
        · have hb : ab.1.2 < n := by
            have hab := ab.property
            omega
          have := ModuleCat.subsingleton_of_isZero (ih ab.1.2 hb)
          infer_instance
      have := hs
      have hsum : IsZero (ModuleCat.of K
          (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
            TensorProduct K
              ((DerivedSections.relativeCohomology A.X.hom ab.1.1).obj L.obj)
              ((DerivedSections.relativeCohomology A.X.hom ab.1.2).obj L.obj))) :=
        ModuleCat.isZero_of_subsingleton _
      obtain ⟨eK⟩ := coherentFieldExternalTensorKunneth K A.X A.X L L n
      obtain ⟨eM⟩ := (algClosedFieldTranslationInvariantPullbackIdentities K A L hL).1
      have hprod : IsZero ((DerivedSections.relativeCohomology P.hom n).obj
          ((Scheme.Modules.pullback m.left).obj L.obj)) :=
        hsum.of_iso ((DerivedSections.relativeCohomology P.hom n).mapIso eM ≪≫ eK)
      have := hmono n
      apply (IsZero.iff_id_eq_zero _).2
      apply (cancel_mono (DerivedSections.relativeCohomologyPullback m L.obj n)).1
      exact hprod.eq_of_tgt _ _

/-- A nontrivial translation-invariant line bundle over an algebraically closed
field has zero actual relative cohomology in every natural degree. -/
theorem algClosedFieldTranslationInvariantCohomologyVanishing :
    AlgClosedFieldTranslationInvariantCohomologyVanishingStatement.{u} := by
  intro K _ _ A L hL hne
  exact translationInvariantCohomologyVanishing_of_multiplicationPullbackMono
    K A L hL hne
    (multiplicationPullbackMono (CommRingCat.of K) A L.obj)

end Langlands.AbelianScheme
