import Langlands.Representation.CuspidalSupport.ConstituentSemisimpleStatement
import Langlands.Representation.Classification.SupercuspidalSupport
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.GroupTheory.Subgroup.Center

/-! The semisimple base case for the constituent extraction argument. -/

noncomputable section

namespace Langlands.CuspidalSupport

open CategoryTheory
open scoped MonoidAlgebra

universe uR uG uV

/-- Adjoining a scalar-acting center does not change invariant subspaces, so
semisimplicity passes from a subgroup to its join with the center. -/
theorem semisimple_sup_center_of_scalar {R : Type uR} [Field R]
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (H : Subgroup G)
    (hscalar : ∀ z : Subgroup.center G, ∃ c : R, ∀ v : V, ρ z v = c • v)
    (hH : Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)) :
    Representation.IsSemisimpleRepresentation
      (ρ.comp (H ⊔ Subgroup.center G).subtype) := by
  let e : Subrepresentation (ρ.comp (H ⊔ Subgroup.center G).subtype) ≃o
      Subrepresentation (ρ.comp H.subtype) :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := fun g _ hv =>
            S.apply_mem_toSubmodule ⟨g.val, Subgroup.mem_sup_left g.property⟩ hv }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g v hv
            obtain ⟨h, hh, z, hz, heq⟩ := Subgroup.mem_sup_of_normal_right.mp g.property
            obtain ⟨c, hc⟩ := hscalar ⟨z, hz⟩
            change ρ g.val v ∈ S.toSubmodule
            rw [← heq, map_mul, Module.End.mul_apply, hc]
            exact S.apply_mem_toSubmodule ⟨h, hh⟩ (S.toSubmodule.smul_mem c hv) }
      left_inv := fun _ => by apply Subrepresentation.toSubmodule_injective; rfl
      right_inv := fun _ => by apply Subrepresentation.toSubmodule_injective; rfl
      map_rel_iff' := by rfl }
  exact e.complementedLattice_iff.mpr hH

/-- Every actual subquotient of a semisimple representation has both an actual
embedding and an actual quotient map. Irreducibility is unnecessary. -/
theorem constituent_of_semisimple {R : Type uR} [Field R]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {A D : SmoothRep.{uR, uG, uV} R G}
    (hA : Representation.IsSemisimpleRepresentation A.representation)
    (h : SmoothRep.IsSubquotient D A) :
    SmoothRep.IsSubrepresentation D A ∧ SmoothRep.IsQuotient D A := by
  let : IsSemisimpleModule R[G] A.representation.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hA
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  let j := Representation.IntertwiningMap.equivLinearMapAsModule
    C.representation A.representation (SmoothRep.hom i)
  let f := Representation.IntertwiningMap.equivLinearMapAsModule
    C.representation D.representation (SmoothRep.hom q)
  have hj : Function.Injective j := hi
  have hf : Function.Surjective f := hq
  let : IsSemisimpleModule R[G] C.representation.asModule :=
    IsSemisimpleModule.of_injective j hj
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property j hj
    (LinearMap.id : C.representation.asModule →ₗ[R[G]] C.representation.asModule)
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property f hf
    (LinearMap.id : D.representation.asModule →ₗ[R[G]] D.representation.asModule)
  have hr' : Function.LeftInverse r j := fun x =>
    congrArg (fun t : C.representation.asModule →ₗ[R[G]] C.representation.asModule => t x) hr
  have hs' : Function.LeftInverse f s := fun x =>
    congrArg (fun t : D.representation.asModule →ₗ[R[G]] D.representation.asModule => t x) hs
  constructor
  · refine ⟨SmoothRep.ofHom ((Representation.IntertwiningMap.equivLinearMapAsModule
      D.representation A.representation).symm (j.comp s)), ?_⟩
    exact hj.comp hs'.injective
  · refine ⟨SmoothRep.ofHom ((Representation.IntertwiningMap.equivLinearMapAsModule
      A.representation D.representation).symm (f.comp r)), ?_⟩
    exact hf.comp hr'.surjective

/-- Scalar-center transfer and extraction, with precisely the published target. -/
theorem semisimpleConstituentExtraction :
    SemisimpleConstituentExtractionTheorem.{uR, uG, uV} := by
  constructor
  · exact @semisimple_sup_center_of_scalar
  · exact @constituent_of_semisimple

end Langlands.CuspidalSupport
