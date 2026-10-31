import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedReductionProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineFromNoetherianProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeSeparatedStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Separatedness of the chosen dual parameter scheme (proof) -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable (seesaw : RigidifiedClassesEqualizerClosedStatement.{u})

include seesaw in
/-- If the agreement locus of two rigidified classes is always closed, then the parameter scheme
of any universal Picard-zero family is separated over the base. -/
theorem isSeparated_of_isUniversalPicardZero {S : Scheme.{u}} (A : AbelianScheme S)
    {P : Over S} (L : RigidifiedFamily A P) (hL : IsUniversalPicardZero A L) :
    IsSeparated P.hom := by
  let cl := RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A) L
  have cl_comp {T U : Over S} (h : T ⟶ U) (k : U ⟶ P) :
      cl T (h ≫ k) = RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
        (unitSection_comp A) h (cl U k) :=
    RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
      RigidifiedModule.pullbackCoherence L h k
  -- The fibre square `P ×_S P` as a test scheme, with its two projections.
  let T : Over S := Over.mk (pullback.fst P.hom P.hom ≫ P.hom)
  let p₁ : T ⟶ P := Over.homMk (pullback.fst P.hom P.hom)
  let p₂ : T ⟶ P := Over.homMk (pullback.snd P.hom P.hom) (by simp [T, pullback.condition])
  obtain ⟨Z, ι, hι, hZ⟩ := seesaw S A T (cl T p₁) (cl T p₂)
  -- The diagonal lies in the agreement locus.
  let d : P ⟶ T := Over.homMk (pullback.diagonal P.hom) (by simp [T])
  have hd₁ : d ≫ p₁ = 𝟙 P := by ext; simp [d, p₁]
  have hd₂ : d ≫ p₂ = 𝟙 P := by ext; simp [d, p₂]
  obtain ⟨g, hg⟩ := (hZ P d).mpr (by rw [← cl_comp, ← cl_comp, hd₁, hd₂])
  -- On the agreement locus the two projections agree, by uniqueness of classification.
  let Z' : Over S := Over.mk (ι ≫ T.hom)
  let i : Z' ⟶ T := Over.homMk ι
  have hi : cl Z' (i ≫ p₁) = cl Z' (i ≫ p₂) := by
    rw [cl_comp, cl_comp]
    exact (hZ Z' i).mp ⟨𝟙 Z, by simp [i, Z']⟩
  have hpz : IsPicardZeroClass A (cl Z' (i ≫ p₁)) :=
    isPicardZeroClass_pullback picardZeroPullback A (i ≫ p₁)
      (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L) hL.1
  have heq : i ≫ p₁ = i ≫ p₂ := by
    obtain ⟨_, _, hu⟩ := hL.2 Z' ⟨_, hpz⟩
    exact (hu _ rfl).trans (hu _ hi.symm).symm
  have heq' : ι ≫ pullback.fst P.hom P.hom = ι ≫ pullback.snd P.hom P.hom := by
    simpa [i, p₁, p₂] using congrArg CommaMorphism.left heq
  -- Hence the closed immersion `ι` and the diagonal define the same subobject.
  let k : Z ⟶ P.left := ι ≫ pullback.fst P.hom P.hom
  have hg' : g ≫ ι = pullback.diagonal P.hom := by simpa [d] using hg
  have hι' : k ≫ pullback.diagonal P.hom = ι := by
    apply pullback.hom_ext
    · simp [k]
    · simp [k, heq']
  have hgk : g ≫ k = 𝟙 P.left := by
    simp only [k, ← Category.assoc, hg', pullback.diagonal_fst]
  have hkg : k ≫ g = 𝟙 Z := by
    rw [← cancel_mono ι, Category.assoc, hg', hι', Category.id_comp]
  have : IsIso g := ⟨⟨k, hgk, hkg⟩⟩
  exact ⟨hg' ▸ inferInstance⟩

include seesaw in
/-- The conditional reduction: a closed agreement locus for rigidified classes makes the
chosen dual parameter scheme separated over every base. -/
theorem relativeDualSchemeSeparated_of_equalizerClosed :
    RelativeDualSchemeSeparatedStatement.{u} := by
  intro S _ A hA
  exact isSeparated_of_isUniversalPicardZero seesaw A (poincareFamily A hA)
    (poincareFamily_universal A hA)

/-- Over a quasi-separated base, the chosen dual parameter scheme is separated. The closed
agreement locus is supplied by composing the published affine, noetherian-approximation and
Zariski-separatedness results. -/
theorem relativeDualSchemeSeparated : RelativeDualSchemeSeparatedStatement.{u} :=
  relativeDualSchemeSeparated_of_equalizerClosed
    (rigidifiedClassesEqualizerClosedReduction
      (rigidifiedClassesEqualizerClosedAffine_of_noetherian
        rigidifiedClassesEqualizerClosedNoetherianAffine
        rigidifiedClassesNoetherianApproximation)
      rigidifiedClassesZariskiSeparated)

end Langlands.AbelianScheme
