import Langlands.Global.AdelicGL
import Langlands.Global.AdelesLocallyCompactProof
import Mathlib.Topology.CompactOpen

/-! # Local compactness and compact-open translation on actual adelic matrix groups -/

noncomputable section

universe uF uV

namespace Langlands.Global

open NumberField IsDedekindDomain
open scoped RestrictedProduct

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

namespace FiniteAdelicGL

/-- Local compactness of the actual finite adelic matrix group with its units topology. -/
instance locallyCompactSpace : LocallyCompactSpace (FiniteAdelicGL F n) := by
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) :=
    finiteAdeles_locallyCompactSpace F
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → FiniteAdeleRing (𝓞 F) F))
  let : T2Space (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → FiniteAdeleRing (𝓞 F) F))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end FiniteAdelicGL

namespace AdelicGL

/-- Local compactness of the actual full adelic matrix group with its units topology. -/
instance locallyCompactSpace : LocallyCompactSpace (AdelicGL F n) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let : LocallyCompactSpace (AdeleRing (𝓞 F) F) := adeles_locallyCompactSpace F
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AdeleRing (𝓞 F) F))
  let : T2Space (Matrix (Fin n) (Fin n) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → AdeleRing (𝓞 F) F))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

variable {V : Type uV} [TopologicalSpace V]

/-- Actual right translation of a continuous function on the adelic matrix group. -/
def rightTranslate (g : AdelicGL F n) (f : C(AdelicGL F n, V)) :
    C(AdelicGL F n, V) :=
  f.comp (ContinuousMap.mulRight g)

@[simp]
theorem rightTranslate_apply (g x : AdelicGL F n) (f : C(AdelicGL F n, V)) :
    rightTranslate F n g f x = f (x * g) := rfl

@[simp]
theorem rightTranslate_one (f : C(AdelicGL F n, V)) :
    rightTranslate F n 1 f = f := by
  ext x
  simp

/-- This is a left action on functions: the two right translations compose in group order. -/
theorem rightTranslate_mul (g h : AdelicGL F n) (f : C(AdelicGL F n, V)) :
    rightTranslate F n (g * h) f =
      rightTranslate F n g (rightTranslate F n h f) := by
  ext x
  simp [mul_assoc]

/-- Evaluation is jointly continuous on the actual compact-open function space and group. -/
theorem continuous_evaluation :
    Continuous (fun p : C(AdelicGL F n, V) × AdelicGL F n => p.1 p.2) :=
  continuous_eval

/-- The group element and continuous function can vary simultaneously. -/
theorem continuous_rightTranslate :
    Continuous (fun p : AdelicGL F n × C(AdelicGL F n, V) =>
      rightTranslate F n p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_evaluation F n).comp
    ((continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.mul (continuous_fst.comp continuous_fst)))

/-- The compact-open orbit map of every actual continuous function is continuous. -/
theorem continuous_rightTranslate_orbit (f : C(AdelicGL F n, V)) :
    Continuous (fun g : AdelicGL F n => rightTranslate F n g f) :=
  (continuous_rightTranslate F n).comp (continuous_id.prodMk continuous_const)

end AdelicGL

end Langlands.Global
