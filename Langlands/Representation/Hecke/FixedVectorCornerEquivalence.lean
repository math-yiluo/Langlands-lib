import Langlands.Representation.Hecke.IdempotentGenerationBridge
import Langlands.Representation.Hecke.HomomorphismLeft
import Langlands.Algebra.NonUnitalModuleCornerEquivalenceConstruction
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! # Restricting the smooth Hecke equivalence and comparing corner induction -/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Algebra.NonUnitalModuleIdempotentGenerated

/-- Generatedness is invariant under isomorphisms of the original nondegenerate modules. -/
instance generatedProperty_isClosedUnderIsomorphisms
    {A : Type u} [NonUnitalRing A] (e : Idempotent A) :
    (generatedProperty.{u, v} e).IsClosedUnderIsomorphisms where
  of_iso {M N} f hM := by
    apply NonUnitalModuleCornerInductionGenerated.isGenerated_of_surjective e f.hom.hom _ hM
    intro n
    refine ⟨f.inv.hom.toAddMonoidHom n, ?_⟩
    have h := congrArg (fun t => t.hom.toAddMonoidHom n) f.inv_hom_id
    exact h

end Langlands.Algebra.NonUnitalModuleIdempotentGenerated

namespace Langlands.Hecke

open Langlands.Algebra NonUnitalModuleIdempotentGenerated

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The III.1.4 equivalence restricted to the two corresponding generated subcategories. -/
def fixedVectorGenerationEquivalence :
    (fixedVectorGeneratedProperty.{u, v} K).FullSubcategory ≌
      GeneratedModuleCat.{u, v} (compactOpenIdempotent μ K hK) := by
  let := heckeNondegenerateModuleEquivalence.{u, v} G μ
  apply (heckeNondegenerateModuleFunctor.{u, v} μ).asEquivalence.congrFullSubcategory
  funext V
  exact propext (fixedVectorGenerated_iff_idempotentGenerated μ K hK V).symm

/-- Forgetting the restriction recovers the exact original smooth Hecke functor. -/
theorem fixedVectorGenerationEquivalence_functor_comp_inclusion :
    (fixedVectorGenerationEquivalence.{u, v} μ K hK).functor ⋙
        inclusion (compactOpenIdempotent μ K hK) =
      (fixedVectorGeneratedProperty K).ι ⋙ heckeNondegenerateModuleFunctor μ := rfl

/-- Subobject closure transfers across III.1.4 and the generation bridge. -/
theorem idempotentGenerated_closedUnderSubobjects_of_fixedVectorGenerated
    [hsub : (fixedVectorGeneratedProperty.{u, v} K).IsClosedUnderSubobjects] :
    (generatedProperty.{u, v} (compactOpenIdempotent μ K hK)).IsClosedUnderSubobjects := by
  letI := heckeNondegenerateModuleEquivalence.{u, v} G μ
  let E := (heckeNondegenerateModuleFunctor.{u, v} μ).asEquivalence
  let P := fixedVectorGeneratedProperty.{u, v} K
  let Q := generatedProperty.{u, v} (compactOpenIdempotent μ K hK)
  constructor
  intro N M f _ hM
  have hPV : P (E.inverse.obj M) :=
    (fixedVectorGenerated_iff_idempotentGenerated μ K hK _).mpr
      (Q.prop_of_iso (E.counitIso.app M).symm hM)
  have hPW : P (E.inverse.obj N) := P.prop_of_mono (E.inverse.map f) hPV
  exact Q.prop_of_iso (E.counitIso.app N)
    ((fixedVectorGenerated_iff_idempotentGenerated μ K hK _).mp hPW)

/-- The fixed-part equivalence under the explicit subobject-closure hypothesis. -/
def fixedVectorCornerEquivalence
    [hsub : (fixedVectorGeneratedProperty.{u, max u v} K).IsClosedUnderSubobjects] :
    (fixedVectorGeneratedProperty.{u, max u v} K).FullSubcategory ≌
      ModuleCat.{max u v} (Idempotent.Corner (compactOpenIdempotent μ K hK)) :=
  (fixedVectorGenerationEquivalence.{u, max u v} μ K hK).trans
    (NonUnitalModuleCornerSimpleProof.generatedEquivalence (Homomorphism.isIdempotented μ)
      (compactOpenIdempotent μ K hK)
      (idempotentGenerated_closedUnderSubobjects_of_fixedVectorGenerated μ K hK))

/-- The equivalence uses the exact original fixed-part functor. -/
theorem fixedVectorCornerEquivalence_functor
    [hsub : (fixedVectorGeneratedProperty.{u, max u v} K).IsClosedUnderSubobjects] :
    (fixedVectorCornerEquivalence.{u, v} μ K hK).functor =
      (fixedVectorGeneratedProperty K).ι ⋙ heckeNondegenerateModuleFunctor μ ⋙
        NonUnitalModuleCorner.nondegenerateFunctor (compactOpenIdempotent μ K hK) := rfl

/-- Its inverse, viewed as a nondegenerate Hecke module, is actual corner induction. -/
def fixedVectorCornerEquivalence_inverseIso
    [hsub : (fixedVectorGeneratedProperty.{u, max u v} K).IsClosedUnderSubobjects] :
    (fixedVectorCornerEquivalence.{u, v} μ K hK).inverse ⋙
        (fixedVectorGeneratedProperty K).ι ⋙ heckeNondegenerateModuleFunctor μ ≅
      NonUnitalModuleCornerInduction.nondegenerateFunctor
        (Homomorphism.isIdempotented μ) (compactOpenIdempotent μ K hK) := by
  let R := fixedVectorGenerationEquivalence.{u, max u v} μ K hK
  let I := NonUnitalModuleCornerInductionGenerated.generatedFunctor
    (Homomorphism.isIdempotented μ) (compactOpenIdempotent μ K hK)
  exact Functor.isoWhiskerLeft I
    (Functor.isoWhiskerRight R.counitIso (inclusion (compactOpenIdempotent μ K hK)))

end Langlands.Hecke
