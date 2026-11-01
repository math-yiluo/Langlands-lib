import Langlands.Algebra.NondegenerateModuleExactnessProof
import Langlands.Algebra.NonUnitalModuleExactnessProof
import Langlands.Algebra.NonUnitalModuleSubobject

/-! Concrete criteria for exactness and the boundary mono/epi in the actual nondegenerate category. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra

universe uA v

namespace NondegenerateModuleExactnessConcrete

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)

include hA

theorem exact_iff (S : ShortComplex (NondegenerateModuleCat.{uA, v} A)) :
    let := NondegenerateModuleCat.abelian.{uA, v} A hA
    S.Exact ↔ ∀ y : S.X₂.obj, S.g.hom.toAddMonoidHom y = 0 →
      ∃ x : S.X₁.obj, S.f.hom.toAddMonoidHom x = y := by
  let := NondegenerateModuleCat.abelian.{uA, v} A hA
  rw [← nondegenerateInclusion_exact_map_iff hA S,
    NonUnitalModuleCat.exact_iff_rangeSubmodule_eq_kernelSubmodule]
  constructor
  · intro h y hy
    change y ∈ NonUnitalModuleHom.rangeSubmodule (S.map (nondegenerateInclusion A)).f
    rw [h]
    exact hy
  · intro h
    apply SetLike.ext
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg (fun k => k.hom.toAddMonoidHom x) S.zero
    · exact h y

theorem mono_iff {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    let := NondegenerateModuleCat.abelian.{uA, v} A hA
    Mono f ↔ Function.Injective f.hom.toAddMonoidHom := by
  let := NondegenerateModuleCat.abelian.{uA, v} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, v} hA
  constructor
  · intro hf
    exact (NonUnitalModuleCat.mono_iff_injective f.hom).1
      ((nondegenerateInclusion A).map_mono f)
  · intro hf
    exact (nondegenerateInclusion A).mono_of_mono_map (f := f)
      ((NonUnitalModuleCat.mono_iff_injective f.hom).2 hf)

theorem epi_iff {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    let := NondegenerateModuleCat.abelian.{uA, v} A hA
    Epi f ↔ Function.Surjective f.hom.toAddMonoidHom := by
  let := NondegenerateModuleCat.abelian.{uA, v} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, v} hA
  let E := IntegerUnitization.equivalence.{uA, v} A
  constructor
  · intro hf
    let : Epi f.hom := (nondegenerateInclusion A).map_epi f
    exact (ModuleCat.epi_iff_surjective (E.functor.map f.hom)).1 inferInstance
  · intro hf
    have he : Epi (E.functor.map f.hom) := (ModuleCat.epi_iff_surjective _).2 hf
    have hfhom : Epi f.hom := E.functor.epi_of_epi_map he
    exact (nondegenerateInclusion A).epi_of_epi_map (f := f) hfhom

end NondegenerateModuleExactnessConcrete

end Langlands.Algebra
