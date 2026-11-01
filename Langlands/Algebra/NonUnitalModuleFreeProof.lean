import Langlands.Algebra.NonUnitalModuleFreeStatements
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Langlands.CategoryTheory.Renard.HomExactnessComparison
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! The actual regular-sum quotient and projective splitting in Renard I.5.3. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleFreeProof

universe uA uM

open NonUnitalModuleFree NonUnitalModuleFreeStatements

variable {A : Type uA} [NonUnitalRing A]

/-- Assemble the original orbit maps, indexed by all vectors of the target. -/
def quotientMap (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    object.{uA, uM, max uA uM} hA M.obj ⟶ M :=
  ObjectProperty.homMk (fromFamily (fun m : M.obj => m))

/-- A fixing idempotent in the summand indexed by m supplies its preimage. -/
theorem quotientMap_surjective (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    Function.Surjective (quotientMap hA M).hom.toAddMonoidHom := by
  intro m
  obtain ⟨e, he⟩ := M.property m
  refine ⟨inclusion M.obj m (ULift.up (e : A)), ?_⟩
  change fromFamily.{uA, uM, max uA uM, max uA uM} (fun n : M.obj => n)
    (inclusion M.obj m (ULift.up (e : A))) = m
  exact (fromFamily_single (fun n : M.obj => n) m (e : A)).trans he

/-- The source quotient assertion with explicit original-carrier surjectivity. -/
theorem freeQuotient : FreeQuotientStatement.{uA, uM} := by
  intro A _ hA M
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  exact ⟨M.obj, quotientMap hA M,
    (NondegenerateModuleExactnessConcrete.epi_iff hA _).mpr
      (quotientMap_surjective hA M),
    quotientMap_surjective hA M⟩

/-- Split the regular-sum quotient of a projective through its actual kernel. -/
theorem projectiveFreeSummand : ProjectiveFreeSummandStatement.{uA, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  intro P hP
  obtain ⟨I, q, hq, _⟩ := freeQuotient A hA P
  let := hq
  let : Projective (ShortComplex.kernelSequence q).X₃ := by
    change Projective P
    exact (Langlands.Renard.homProjectiveComparison P).mp hP
  have hS : (ShortComplex.kernelSequence q).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact q) inferInstance hq
  exact ⟨I, kernel q, ⟨hS.splittingOfProjective.isoBinaryBiproduct ≪≫
    biprod.braiding _ _⟩⟩

/-- Both positive free-module assertions with no additional object premise. -/
theorem freeModuleAssertions : FreeModuleAssertions.{uA, uM} :=
  ⟨freeQuotient, projectiveFreeSummand⟩

example : FreeModuleAssertions.{uA, uM} := freeModuleAssertions.{uA, uM}
example : FreeModuleAssertions.{0, 1} := freeModuleAssertions.{0, 1}
example : FreeModuleAssertions.{1, 0} := freeModuleAssertions.{1, 0}

end Langlands.Algebra.NonUnitalModuleFreeProof
