import Langlands.Algebra.NondegenerateModuleExactnessStatements
import Langlands.Algebra.NondegenerateModuleAbelianProof
import Langlands.Algebra.NondegenerateModuleAdjunction
import Langlands.Algebra.NondegeneratePartRangeExactnessProof
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Exactness of the actual nondegenerate inclusion and part functor

Inclusion preserves kernels and cokernels by published closure. The part
functor preserves kernels by its actual right adjunction and epis by the
published idempotent-adjusted surjective lift.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory CategoryTheory.Limits

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- The actual inclusion preserves kernels and cokernels by original closure. -/
theorem nondegenerateInclusion_preservesHomology (hA : IsIdempotented A) :
    (nondegenerateInclusion.{uA, uM} A).PreservesHomology := by
  let h := nondegenerateModuleClosureStatement.{uA, uM} A hA
  let := h.2.1
  let := h.2.2.1
  exact
    { preservesKernels := fun {_ _} f => (nondegenerateProperty A).preservesKernels_ι f
      preservesCokernels := fun {_ _} f => (nondegenerateProperty A).preservesCokernels_ι f }

/-- The restricted original preimages give cancellation in the actual full category. -/
theorem nondegeneratePartFunctor_preservesEpimorphisms (hA : IsIdempotented A) :
    (nondegeneratePartFunctor.{uA, uM} hA).PreservesEpimorphisms where
  preserves {M N} f _ := by
    have hf : Epi ((IntegerUnitization.equivalence A).functor.map f) := inferInstance
    have hs : Function.Surjective f.toAddMonoidHom := (ModuleCat.epi_iff_surjective _).1 hf
    have hr := NonUnitalModuleHom.restrictNondegeneratePart_surjective hA f hs
    refine ⟨fun g k w => ?_⟩
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro y
    obtain ⟨x, hx⟩ := hr y
    have hw := congrArg (fun t => t.hom.toAddMonoidHom x) w
    change g.hom.toAddMonoidHom (f.restrictNondegeneratePart hA x) =
      k.hom.toAddMonoidHom (f.restrictNondegeneratePart hA x) at hw
    rw [hx] at hw
    exact hw

/-- The actual part functor preserves kernels and cokernels. -/
theorem nondegeneratePartFunctor_preservesHomology (hA : IsIdempotented A) :
    (nondegeneratePartFunctor.{uA, uM} hA).PreservesHomology := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := nondegeneratePartFunctor_preservesEpimorphisms.{uA, uM} hA
  let : PreservesLimits (nondegeneratePartFunctor.{uA, uM} hA) :=
    (nondegeneratePartAdjunction hA).rightAdjoint_preservesLimits
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Exactness in the actual full subcategory agrees with ambient exactness. -/
theorem nondegenerateInclusion_exact_map_iff (hA : IsIdempotented A)
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) :
    (S.map (nondegenerateInclusion A)).Exact ↔ S.Exact := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, uM} hA
  exact S.exact_map_iff_of_faithful (nondegenerateInclusion A)

/-- The actual inclusion preserves exact short complexes. -/
theorem nondegenerateInclusion_map_exact (hA : IsIdempotented A)
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) (hS : S.Exact) :
    (S.map (nondegenerateInclusion A)).Exact :=
  (nondegenerateInclusion_exact_map_iff hA S).2 hS

/-- The actual inclusion reflects exactness of short complexes. -/
theorem nondegenerateInclusion_exact_of_map_exact (hA : IsIdempotented A)
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A))
    (hS : (S.map (nondegenerateInclusion A)).Exact) : S.Exact :=
  (nondegenerateInclusion_exact_map_iff hA S).1 hS

/-- The actual part functor maps every ambient exact short complex to an exact one. -/
theorem nondegeneratePartFunctor_map_exact (hA : IsIdempotented A)
    (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)) (hS : S.Exact) :
    (S.map (nondegeneratePartFunctor hA)).Exact := by
  let := nondegeneratePartFunctor_preservesHomology.{uA, uM} hA
  exact hS.map (nondegeneratePartFunctor hA)

/-- The entire closed exactness assertion, with no extra certificate as a premise. -/
theorem nondegenerateModuleExactnessStatement :
    NondegenerateModuleExactnessStatement.{uA, uM} := by
  intro A _ hA
  exact ⟨nondegenerateInclusion_preservesHomology hA,
    nondegeneratePartFunctor_preservesHomology hA,
    nondegenerateInclusion_exact_map_iff hA,
    nondegeneratePartFunctor_map_exact hA⟩

example : NondegenerateModuleExactnessStatement.{uA, uM} :=
  nondegenerateModuleExactnessStatement.{uA, uM}

example : NondegenerateModuleExactnessStatement.{0, 1} :=
  nondegenerateModuleExactnessStatement.{0, 1}

example : NondegenerateModuleExactnessStatement.{1, 0} :=
  nondegenerateModuleExactnessStatement.{1, 0}

/-! Complete unapplied interfaces with both unequal universe assignments. -/

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateInclusion.{uA, uM} A).PreservesHomology :=
  @nondegenerateInclusion_preservesHomology.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{uA, uM} hA).PreservesEpimorphisms :=
  @nondegeneratePartFunctor_preservesEpimorphisms.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{uA, uM} hA).PreservesHomology :=
  @nondegeneratePartFunctor_preservesHomology.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) →
    ((S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) :=
  @nondegenerateInclusion_exact_map_iff.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) → S.Exact →
    (S.map (nondegenerateInclusion A)).Exact :=
  @nondegenerateInclusion_map_exact.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) →
    (S.map (nondegenerateInclusion A)).Exact → S.Exact :=
  @nondegenerateInclusion_exact_of_map_exact.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)) → S.Exact →
    (S.map (nondegeneratePartFunctor hA)).Exact :=
  @nondegeneratePartFunctor_map_exact.{uA, uM}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateInclusion.{0, 1} A).PreservesHomology :=
  @nondegenerateInclusion_preservesHomology.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{0, 1} hA).PreservesEpimorphisms :=
  @nondegeneratePartFunctor_preservesEpimorphisms.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{0, 1} hA).PreservesHomology :=
  @nondegeneratePartFunctor_preservesHomology.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{0, 1} A)) →
    ((S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) :=
  @nondegenerateInclusion_exact_map_iff.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{0, 1} A)) → S.Exact →
    (S.map (nondegenerateInclusion A)).Exact :=
  @nondegenerateInclusion_map_exact.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{0, 1} A)) →
    (S.map (nondegenerateInclusion A)).Exact → S.Exact :=
  @nondegenerateInclusion_exact_of_map_exact.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NonUnitalModuleCat.{0, 1} A)) → S.Exact →
    (S.map (nondegeneratePartFunctor hA)).Exact :=
  @nondegeneratePartFunctor_map_exact.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegenerateInclusion.{1, 0} A).PreservesHomology :=
  @nondegenerateInclusion_preservesHomology.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{1, 0} hA).PreservesEpimorphisms :=
  @nondegeneratePartFunctor_preservesEpimorphisms.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{1, 0} hA).PreservesHomology :=
  @nondegeneratePartFunctor_preservesHomology.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{1, 0} A)) →
    ((S.map (nondegenerateInclusion A)).Exact ↔ S.Exact) :=
  @nondegenerateInclusion_exact_map_iff.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{1, 0} A)) → S.Exact →
    (S.map (nondegenerateInclusion A)).Exact :=
  @nondegenerateInclusion_map_exact.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NondegenerateModuleCat.{1, 0} A)) →
    (S.map (nondegenerateInclusion A)).Exact → S.Exact :=
  @nondegenerateInclusion_exact_of_map_exact.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (S : ShortComplex (NonUnitalModuleCat.{1, 0} A)) → S.Exact →
    (S.map (nondegeneratePartFunctor hA)).Exact :=
  @nondegeneratePartFunctor_map_exact.{1, 0}

end Langlands.Algebra
