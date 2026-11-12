import Langlands.Algebra.NonUnitalModuleCornerClosedEvaluation
import Mathlib.CategoryTheory.Abelian.Transfer

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleProof

open CategoryTheory CategoryTheory.Limits
open NonUnitalModuleCorner NonUnitalModuleCornerInduction NonUnitalModuleCornerEvaluation
open NonUnitalModuleIdempotentGenerated NonUnitalModuleCornerSimpleStatements
open NonUnitalModuleCornerInductionGenerated

attribute [local instance] rightCornerModule cornerModule tensorModule

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- Evaluation as an isomorphism of the actual generated category. -/
def generatedEvaluationIso (hA : IsIdempotented A) (e : Idempotent A)
    (hsub : (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects)
    (V : GeneratedModuleCat.{uA, max uA uM} e) :
    (cornerFunctor e ⋙ generatedFunctor hA e).obj V ≅ V := by
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  let f : (cornerFunctor e ⋙ generatedFunctor hA e).obj V ⟶ V :=
    ObjectProperty.homMk (ObjectProperty.homMk (evaluation e V.obj.obj))
  have hb := evaluation_bijective_of_closed hA e hsub V
  have : Mono f.hom := (NondegenerateModuleExactnessConcrete.mono_iff hA f.hom).2 hb.1
  have : Epi f.hom := (NondegenerateModuleExactnessConcrete.epi_iff hA f.hom).2 hb.2
  have : IsIso f.hom := isIso_of_mono_of_epi f.hom
  have : IsIso ((inclusion.{uA, max uA uM} e).map f) :=
    (inferInstance : IsIso f.hom)
  have : IsIso f := isIso_of_reflects_iso f (inclusion.{uA, max uA uM} e)
  exact asIso f

/-- The evaluation isomorphisms are natural by published whole-map naturality. -/
def generatedEvaluationNaturalIso (hA : IsIdempotented A) (e : Idempotent A)
    (hsub : (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects) :
    cornerFunctor.{uA, max uA uM} e ⋙ generatedFunctor hA e ≅
      𝟭 (GeneratedModuleCat.{uA, max uA uM} e) :=
  NatIso.ofComponents (generatedEvaluationIso hA e hsub) (by
    intro V V' f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (evaluation_naturality e f.hom.hom).symm)

/-- The published fixed-part equivalence, without a universe lift at this carrier bound. -/
def generatedFixedNaturalIso (hA : IsIdempotented A) (e : Idempotent A) :
    𝟭 (ModuleCat.{max uA uM} (Idempotent.Corner e)) ≅
      generatedFunctor hA e ⋙ cornerFunctor e :=
  NatIso.ofComponents (fun W => (fixedPartEquivalence e W).toModuleIso) (by
    intro W W' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change tmul e (e : A) (f.hom w) = inducedMap e f.hom (tmul e (e : A) w)
    rw [inducedMap_tmul])

/-- The actual corner and induction functors give an equivalence under subobject closure. -/
def generatedEquivalence (hA : IsIdempotented A) (e : Idempotent A)
    (hsub : (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects) :
    GeneratedModuleCat.{uA, max uA uM} e ≌
      ModuleCat.{max uA uM} (Idempotent.Corner e) :=
  CategoryTheory.Equivalence.mk (cornerFunctor e) (generatedFunctor hA e)
    (generatedEvaluationNaturalIso hA e hsub).symm (generatedFixedNaturalIso hA e).symm

/-- Sufficiency in the equivalence criterion. -/
theorem corner_isEquivalence_of_closed (hA : IsIdempotented A) (e : Idempotent A)
    (hsub : (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects) :
    (cornerFunctor.{uA, max uA uM} e).IsEquivalence :=
  (generatedEquivalence hA e hsub).isEquivalence_functor

/-- Transport of abelianness keeps the inherited preadditive structure. -/
theorem generatedCategoryAbelian : GeneratedCategoryAbelianStatement.{uA, uM} := by
  intro A _ hA e hsub _hquot
  let F := cornerFunctor.{uA, max uA uM} e
  have : F.IsEquivalence := corner_isEquivalence_of_closed hA e hsub
  have : HasFiniteProducts (GeneratedModuleCat.{uA, max uA uM} e) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence F⟩
  exact ⟨abelianOfEquivalence F, rfl⟩

end Langlands.Algebra.NonUnitalModuleCornerSimpleProof
