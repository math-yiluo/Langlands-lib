import Langlands.Algebra.NondegenerateModuleLocallyFiniteTypeStatements
import Langlands.Algebra.NondegenerateModuleSubobject
import Langlands.Algebra.NonUnitalModuleFinitenessProof
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Mathlib.RingTheory.Finiteness.Basic

/-! Local finite type in the original nondegenerate category of Renard I.6. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra.NondegenerateModuleLocallyFiniteTypeProof

open NondegenerateModuleLocallyFiniteTypeStatements

section Transport

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {X : C} {Y : D}

/-- Source finite type depends only on the actual subobject order. -/
private theorem finiteType_of_orderIso (e : Subobject X ≃o Subobject Y)
    (hY : Langlands.Renard.IsFiniteTypeObject Y) :
    Langlands.Renard.IsFiniteTypeObject X :=
  (Langlands.Renard.finiteTypeFiniteSubcover C X).2
    (NonUnitalModuleFiniteness.hasFiniteSubcoverProperty_of_orderIso e
      ((Langlands.Renard.finiteTypeFiniteSubcover D Y).1 hY))

end Transport

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- Finite generation of the original range proves finite type of the
actual chosen subobject domain, with no replacement of its module structure. -/
private theorem finiteType_of_fg_range (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) (P : Subobject M)
    (hfg : letI := CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M.obj));
      (NonUnitalSubmodule.intUnitizedOrderIso
        (NondegenerateModuleCat.subobjectOrderIso hA M P)).FG) :
    Langlands.Renard.IsFiniteTypeObject (P : NondegenerateModuleCat A) := by
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, uM} hA
  let N : NondegenerateModuleCat.{uA, uM} A := P
  let := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M.obj))
  let := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := N.obj))
  let f := (IntegerUnitization.extendMap A P.arrow.hom).hom
  have hf : Function.Injective f :=
    (NondegenerateModuleExactnessConcrete.mono_iff hA P.arrow).1 inferInstance
  have hrange : LinearMap.range f =
      NonUnitalSubmodule.intUnitizedOrderIso
        (NondegenerateModuleCat.subobjectOrderIso hA M P) := by
    ext m
    exact (NondegenerateModuleCat.mem_subobjectOrderIso hA P m).symm
  have htop := Submodule.fg_of_fg_map_injective f hf (N := ⊤) (by
    rw [Submodule.map_top, hrange]
    exact hfg)
  have hfinite : Module.Finite (Unitization ℤ A) N.obj := ⟨htop⟩
  exact finiteType_of_orderIso (NondegenerateModuleCat.ambientSubobjectOrderIso N)
    ((NonUnitalModuleFiniteness.finiteType_iff_finite N.obj).2 hfinite)

/-- Finite subsets generate an increasing cover in the actual subobject order. -/
theorem directedFiniteTypeCover : DirectedFiniteTypeCoverStatement.{uA, uM} := by
  classical
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  intro M
  let := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M.obj))
  let e : Subobject M ≃o Submodule (Unitization ℤ A) M.obj :=
    (NondegenerateModuleCat.subobjectOrderIso hA M).trans
      NonUnitalSubmodule.intUnitizedOrderIso
  let F : Finset M.obj → Subobject M := fun S =>
    e.symm (Submodule.span (Unitization ℤ A) (S : Set M.obj))
  have heF (S : Finset M.obj) :
      e (F S) = Submodule.span (Unitization ℤ A) (S : Set M.obj) :=
    e.apply_symm_apply _
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro S T hST
    exact e.symm.monotone (Submodule.span_mono hST)
  · intro S
    apply finiteType_of_fg_range hA M (F S)
    change (e (F S)).FG
    rw [heF]
    exact Submodule.fg_span S.finite_toSet
  · intro S m hm
    apply (NondegenerateModuleCat.mem_subobjectOrderIso hA (F S) m).1
    change m ∈ e (F S)
    rw [heF]
    exact Submodule.subset_span hm
  · refine ⟨fun _ _ => le_top, ?_⟩
    intro Q hQ
    apply e.le_iff_le.mp
    rw [e.map_top]
    intro m _
    apply e.monotone (hQ ⟨{m}, rfl⟩)
    rw [heF]
    exact Submodule.subset_span (Finset.mem_singleton_self m)

/-- The explicit finite-subset cover implies the canonical source AB6 law. -/
theorem sourceAB6 : SourceAB6Statement.{uA, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  intro M
  obtain ⟨F, _, hfinite, _, hcover⟩ := directedFiniteTypeCover.{uA, uM} A hA M
  exact Langlands.Renard.IsLocallyFiniteTypeObjectOfSize.isLocallyFiniteTypeObject
    ⟨Finset M.obj, F, hfinite, hcover⟩

/-- Both exact universally quantified local finite-type targets. -/
theorem locallyFiniteTypeAssertions : LocallyFiniteTypeAssertions.{uA, uM} :=
  ⟨directedFiniteTypeCover, sourceAB6⟩

example : DirectedFiniteTypeCoverStatement.{uA, uM} :=
  directedFiniteTypeCover.{uA, uM}
example : SourceAB6Statement.{uA, uM} := sourceAB6.{uA, uM}
example : LocallyFiniteTypeAssertions.{uA, uM} := locallyFiniteTypeAssertions.{uA, uM}
example : LocallyFiniteTypeAssertions.{0, 1} := locallyFiniteTypeAssertions.{0, 1}
example : LocallyFiniteTypeAssertions.{1, 0} := locallyFiniteTypeAssertions.{1, 0}

end Langlands.Algebra.NondegenerateModuleLocallyFiniteTypeProof
