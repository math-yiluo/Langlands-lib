import Langlands.Algebra.NonUnitalModuleCornerExactnessStatements
import Langlands.Algebra.NonUnitalModuleExactnessProof
import Langlands.Algebra.NondegenerateModuleExactnessProof
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of the actual original-module corner functors

The fixed-preimage argument of Renard I.3.1, printed p.19 / PDF25,
applies to every original nonunital action. The nondegenerate result
then follows through the published exact inclusion.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM

namespace NonUnitalModuleCorner

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)

/-- Injectivity restricts to the actual fixed-part subtypes. -/
theorem restrict_injective {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N)
    (hf : Function.Injective f.toAddMonoidHom) :
    Function.Injective (restrict e f) := by
  intro x y h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

/-- Projecting an original preimage gives a preimage in the fixed part. -/
theorem restrict_surjective {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N)
    (hf : Function.Surjective f.toAddMonoidHom) :
    Function.Surjective (restrict e f) := by
  intro y
  obtain ⟨m, hm⟩ := hf y.val
  refine ⟨projection e m, ?_⟩
  apply Subtype.ext
  change f.toAddMonoidHom ((e : A) • m) = y.val
  rw [f.map_smul, hm]
  exact y.property

/-- The actual ambient corner functor preserves categorical monomorphisms. -/
instance functor_preservesMonomorphisms :
    (functor.{uA, uM} e).PreservesMonomorphisms where
  preserves {M N} f _ := by
    have hf : Mono ((IntegerUnitization.equivalence A).functor.map f) := inferInstance
    have hi : Function.Injective f.toAddMonoidHom :=
      (ModuleCat.mono_iff_injective _).1 hf
    exact (ModuleCat.mono_iff_injective _).2 (restrict_injective e f hi)

/-- The actual ambient corner functor preserves categorical epimorphisms. -/
instance functor_preservesEpimorphisms :
    (functor.{uA, uM} e).PreservesEpimorphisms where
  preserves {M N} f _ := by
    have hf : Epi ((IntegerUnitization.equivalence A).functor.map f) := inferInstance
    have hs : Function.Surjective f.toAddMonoidHom :=
      (ModuleCat.epi_iff_surjective _).1 hf
    exact (ModuleCat.epi_iff_surjective _).2 (restrict_surjective e f hs)

/-- Every exact original triple remains exact after taking its fixed parts. -/
theorem functor_map_exact (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A))
    (hS : S.Exact) : (S.map (functor e)).Exact := by
  apply (S.map (functor e)).moduleCat_exact_iff.2
  intro y hy
  have hk : y.val ∈ S.g.kernelSubmodule := by
    change S.g.toAddMonoidHom y.val = 0
    exact congrArg Subtype.val hy
  have hr : y.val ∈ S.f.rangeSubmodule :=
    ((NonUnitalModuleCat.exact_iff_rangeSubmodule_eq_kernelSubmodule S).1 hS).symm ▸ hk
  obtain ⟨m, hm⟩ := hr
  change S.f.toAddMonoidHom m = y.val at hm
  refine ⟨projection e m, ?_⟩
  apply Subtype.ext
  change S.f.toAddMonoidHom ((e : A) • m) = y.val
  rw [S.f.map_smul, hm]
  exact y.property

/-- Both one-sided sequence tests, including their Mono/Epi conclusions. -/
theorem functor_sequenceExact :
    Langlands.Renard.SequenceExact (functor.{uA, uM} e) := by
  constructor
  · intro S ⟨hS, hf⟩
    exact ⟨functor_map_exact e S hS, (functor e).map_mono S.f⟩
  · intro S ⟨hS, hg⟩
    exact ⟨functor_map_exact e S hS, (functor e).map_epi S.g⟩

/-- The nondegenerate composite preserves the required boundary monomorphisms. -/
theorem nondegenerateFunctor_preservesMonomorphisms (hA : IsIdempotented A) :
    (nondegenerateFunctor.{uA, uM} e).PreservesMonomorphisms := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, uM} hA
  change (nondegenerateInclusion A ⋙ functor.{uA, uM} e).PreservesMonomorphisms
  infer_instance

/-- The nondegenerate composite preserves the required boundary epimorphisms. -/
theorem nondegenerateFunctor_preservesEpimorphisms (hA : IsIdempotented A) :
    (nondegenerateFunctor.{uA, uM} e).PreservesEpimorphisms := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, uM} hA
  change (nondegenerateInclusion A ⋙ functor.{uA, uM} e).PreservesEpimorphisms
  infer_instance

/-- Preserve every exact triple in the actual nondegenerate original category. -/
theorem nondegenerateFunctor_map_exact (hA : IsIdempotented A)
    (S : ShortComplex (NondegenerateModuleCat.{uA, uM} A)) :
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    S.Exact → (S.map (nondegenerateFunctor e)).Exact := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  intro hS
  exact functor_map_exact e (S.map (nondegenerateInclusion A))
    (nondegenerateInclusion_map_exact hA S hS)

/-- Full sequence exactness for the actual nondegenerate corner functor. -/
theorem nondegenerateFunctor_sequenceExact (hA : IsIdempotented A) :
    letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
    Langlands.Renard.SequenceExact (nondegenerateFunctor.{uA, uM} e) := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := nondegenerateFunctor_preservesMonomorphisms.{uA, uM} e hA
  let := nondegenerateFunctor_preservesEpimorphisms.{uA, uM} e hA
  constructor
  · intro S ⟨hS, hf⟩
    exact ⟨nondegenerateFunctor_map_exact e hA S hS,
      (nondegenerateFunctor e).map_mono S.f⟩
  · intro S ⟨hS, hg⟩
    exact ⟨nondegenerateFunctor_map_exact e hA S hS,
      (nondegenerateFunctor e).map_epi S.g⟩

end NonUnitalModuleCorner

/-- The exact closed ambient target, with no idempotentedness hypothesis. -/
theorem nonUnitalModuleCornerExactness :
    NonUnitalModuleCornerExactnessStatement.{uA, uM} := by
  intro A _ e
  exact ⟨NonUnitalModuleCorner.functor_sequenceExact e,
    NonUnitalModuleCorner.functor_map_exact e⟩

/-- The exact closed nondegenerate target, for the named abelian structures. -/
theorem nondegenerateModuleCornerExactness :
    NondegenerateModuleCornerExactnessStatement.{uA, uM} := by
  intro A _ hA e
  exact ⟨NonUnitalModuleCorner.nondegenerateFunctor_sequenceExact e hA,
    NonUnitalModuleCorner.nondegenerateFunctor_map_exact e hA⟩

example : NonUnitalModuleCornerExactnessStatement.{0, 1} :=
  nonUnitalModuleCornerExactness.{0, 1}

example : NonUnitalModuleCornerExactnessStatement.{1, 0} :=
  nonUnitalModuleCornerExactness.{1, 0}

example : NondegenerateModuleCornerExactnessStatement.{0, 1} :=
  nondegenerateModuleCornerExactness.{0, 1}

example : NondegenerateModuleCornerExactnessStatement.{1, 0} :=
  nondegenerateModuleCornerExactness.{1, 0}

end Langlands.Algebra
