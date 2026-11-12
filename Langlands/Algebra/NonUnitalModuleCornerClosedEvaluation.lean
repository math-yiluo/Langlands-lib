import Langlands.Algebra.NonUnitalModuleCornerSimpleEvaluation

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleProof

open CategoryTheory
open NonUnitalModuleCorner NonUnitalModuleCornerInduction NonUnitalModuleCornerEvaluation
open NonUnitalModuleIdempotentGenerated NonUnitalModuleCornerSimpleStatements
open NonUnitalModuleCornerEvaluationProof NonUnitalModuleCornerInductionGenerated

attribute [local instance] rightCornerModule cornerModule tensorModule

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- Generatedness is always closed under categorical quotients in `M(A)`. -/
theorem generated_closed_quotients (hA : IsIdempotented A) (e : Idempotent A) :
    (generatedProperty.{uA, uM} e).IsClosedUnderQuotients := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  constructor
  intro X Y f hf hX
  exact isGenerated_of_surjective e f.hom
    ((NondegenerateModuleExactnessConcrete.epi_iff hA f).1 hf) hX

/-- Closure under subobjects forces the kernel of corner evaluation to vanish. -/
theorem evaluation_bijective_of_closed (hA : IsIdempotented A) (e : Idempotent A)
    (hsub : (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects)
    (V : GeneratedModuleCat.{uA, max uA uM} e) :
    Function.Bijective (evaluation e V.obj.obj) := by
  let := hsub
  let T : NondegenerateModuleCat.{uA, max uA uM} A :=
    nondegenerateObject hA e (FixedPart e V.obj.obj)
  let S := NonUnitalModuleHom.kernelSubmodule (evaluation e V.obj.obj)
  have : Mono (NondegenerateModuleCat.subtypeHom T S) :=
    NondegenerateModuleCat.mono_subtypeHom T S
  have hS : IsGeneratedByIdempotent e S :=
    (generatedProperty e).prop_of_mono (NondegenerateModuleCat.subtypeHom T S)
      (tensor_isGenerated e (FixedPart e V.obj.obj))
  have he : ∀ s : S, originalAction (e : A) s = 0 := by
    intro s
    apply Subtype.ext
    exact NonUnitalSubmodule.idempotent_smul_eq_zero_of_mem
      (evaluation_kernel_le_annihilator e V.obj.obj s.property)
  have hz : ∀ s : S, s = 0 :=
    (isGenerated_iff_zero_of_coordinate_zero e he).1 hS
  refine ⟨(injective_iff_map_eq_zero (evaluation e V.obj.obj).toAddMonoidHom).2 ?_,
    (evaluation_surjective_iff e V.obj.obj).2 V.property⟩
  intro t ht
  exact congrArg Subtype.val (hz ⟨t, ht⟩)

/-- The inverse-functor clause, on the published tensor and evaluation. -/
theorem cornerInductionInverse : CornerInductionInverseStatement.{uA, uM} := by
  intro A _ hA e hsub _hquot V
  exact evaluation_bijective_of_closed hA e hsub V

end Langlands.Algebra.NonUnitalModuleCornerSimpleProof
