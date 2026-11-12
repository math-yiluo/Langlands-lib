import Langlands.Algebra.NonUnitalModuleCornerEquivalenceConstruction

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerSimpleProof

open CategoryTheory
open NonUnitalModuleCorner NonUnitalModuleCornerInduction
open NonUnitalModuleIdempotentGenerated NonUnitalModuleCornerSimpleStatements
open NonUnitalModuleCornerInductionGenerated

attribute [local instance] rightCornerModule cornerModule tensorModule

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A]

/-- Nondegeneracy descends along an original surjective intertwiner. -/
theorem nondegenerate_of_surjective {M : Type uM} {N : Type uN}
    [AddCommGroup M] [AddCommGroup N] [NonUnitalModule A M] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A M N) (hf : Function.Surjective f.toAddMonoidHom)
    (hM : IsNondegenerate A M) : IsNondegenerate A N := by
  intro n
  obtain ⟨m, rfl⟩ := hf n
  obtain ⟨e, he⟩ := hM m
  exact ⟨e, (f.map_smul (e : A) m).symm.trans (congrArg f.toAddMonoidHom he)⟩

/-- Reflection of the quotient comparison forces zero annihilator on generated objects. -/
theorem generated_annihilator_zero_of_equivalence (hA : IsIdempotented A) (e : Idempotent A)
    [(cornerFunctor.{uA, max uA uM} e).IsEquivalence]
    (V : GeneratedModuleCat.{uA, max uA uM} e) :
    ∀ m ∈ NonUnitalSubmodule.idempotentAnnihilator e V.obj.obj, m = 0 := by
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  let Q := (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj V.obj
  have hQ : IsGeneratedByIdempotent e Q.obj :=
    isGenerated_of_surjective e (annihilatorQuotientProjection e V.obj.obj)
      (annihilatorQuotientProjection_surjective e) V.property
  let p : V ⟶ (⟨Q, hQ⟩ : GeneratedModuleCat e) :=
    ObjectProperty.homMk (ObjectProperty.homMk (annihilatorQuotientProjection e V.obj.obj))
  let F := cornerFunctor.{uA, max uA uM} e
  have : Mono (F.map p) := (ModuleCat.mono_iff_injective _).2
    (IdempotentAnnihilatorComparisons.fixed_projection_bijective e V.obj.obj).1
  have : Epi (F.map p) := (ModuleCat.epi_iff_surjective _).2
    (IdempotentAnnihilatorComparisons.fixed_projection_bijective e V.obj.obj).2
  have : IsIso (F.map p) := isIso_of_mono_of_epi (F.map p)
  have : IsIso p := isIso_of_reflects_iso p F
  have : IsIso ((inclusion.{uA, max uA uM} e).map p) := inferInstance
  have : IsIso p.hom := ‹IsIso ((inclusion.{uA, max uA uM} e).map p)›
  have hi := (NondegenerateModuleExactnessConcrete.mono_iff hA p.hom).1 inferInstance
  intro m hm
  apply hi
  change annihilatorQuotientProjection e V.obj.obj m =
    annihilatorQuotientProjection e V.obj.obj 0
  rw [map_zero]
  exact (annihilatorQuotientProjection_eq_zero_iff e m).2 hm

/-- Necessity of subobject closure, using the source's quotient by the generated part. -/
theorem generated_closed_subobjects_of_equivalence (hA : IsIdempotented A) (e : Idempotent A)
    [(cornerFunctor.{uA, max uA uM} e).IsEquivalence] :
    (generatedProperty.{uA, max uA uM} e).IsClosedUnderSubobjects := by
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  constructor
  intro X Y f hf hY
  let g : NonUnitalModuleCat.of A (aeM e X.obj) ⟶ Y.obj :=
    f.hom.comp (submoduleInclusion e)
  let Q := NonUnitalModuleCat.concreteCokernel g
  let p : Y.obj ⟶ Q := NonUnitalModuleCat.concreteCokernelπ g
  have hp : Function.Surjective p.toAddMonoidHom :=
    Submodule.mkQ_surjective _
  have hQ : IsNondegenerate A Q := nondegenerate_of_surjective p hp Y.property
  have hQg : IsGeneratedByIdempotent e Q := isGenerated_of_surjective e p hp hY
  let VQ : GeneratedModuleCat.{uA, max uA uM} e := ⟨⟨Q, hQ⟩, hQg⟩
  have hz := generated_annihilator_zero_of_equivalence hA e VQ
  have hi := (NondegenerateModuleExactnessConcrete.mono_iff hA f).1 hf
  intro x
  have hpx : p.toAddMonoidHom (f.hom.toAddMonoidHom x) = 0 := by
    apply hz
    intro a
    rw [← p.map_smul, ← f.hom.map_smul]
    apply (NonUnitalModuleCat.concreteCokernelπ_eq_zero_iff g _).2
    refine ⟨⟨(e : A) • (a • x), coordinate_mem e (a • x)⟩, ?_⟩
    change f.hom.toAddMonoidHom ((e : A) • (a • x)) =
      f.hom.toAddMonoidHom (((e : A) * a) • x)
    rw [mul_smul]
  obtain ⟨s, hs⟩ := (NonUnitalModuleCat.concreteCokernelπ_eq_zero_iff g _).1 hpx
  have heq : s.val = x := hi hs
  exact heq ▸ s.property

/-- The exact equivalence criterion with the published carrier universe. -/
theorem cornerEquivalenceCriterion : CornerEquivalenceCriterionStatement.{uA, uM} := by
  intro A _ hA e
  constructor
  · intro h
    let := h
    exact ⟨generated_closed_subobjects_of_equivalence hA e, generated_closed_quotients hA e⟩
  · rintro ⟨hsub, _hquot⟩
    exact corner_isEquivalence_of_closed hA e hsub

end Langlands.Algebra.NonUnitalModuleCornerSimpleProof
