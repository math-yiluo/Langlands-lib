import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.FunctionField

/-! # The generic stalk of a birational morphism -/

universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem birationalOver_isIso_generic_stalkMap
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (f : Z ⟶ S) (hf : Scheme.BirationalOver f (𝟙 S)) :
    IsIso (f.stalkMap (genericPoint Z)) := by
  obtain ⟨e, he⟩ := hf
  have heq : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
    simpa [Scheme.PartialIso.IsOver] using (Eq.symm he)
  have : IsOpenImmersion (e.source.ι ≫ f) := by
    rw [heq]
    infer_instance
  have hi (x : e.source.toScheme) : IsIso (f.stalkMap (e.source.ι x)) := by
    have hc : IsIso (f.stalkMap (e.source.ι x) ≫ e.source.ι.stalkMap x) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (e.source.ι.stalkMap x)
  have : Nonempty e.source.toScheme := e.dense_source.nonempty.to_subtype
  have hi' := hi (genericPoint e.source)
  rwa [genericPoint_eq_of_isOpenImmersion e.source.ι] at hi'

theorem birationalOver_map_genericPoint
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (f : Z ⟶ S) (hf : Scheme.BirationalOver f (𝟙 S)) :
    f (genericPoint Z) = genericPoint S := by
  obtain ⟨e, he⟩ := hf
  have heq : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι := by
    simpa [Scheme.PartialIso.IsOver] using (Eq.symm he)
  have : IsOpenImmersion (e.source.ι ≫ f) := by
    rw [heq]
    infer_instance
  have : Nonempty e.source.toScheme := e.dense_source.nonempty.to_subtype
  calc
    f (genericPoint Z) = (e.source.ι ≫ f) (genericPoint e.source) := by
      change f (genericPoint Z) = f (e.source.ι (genericPoint e.source))
      rw [genericPoint_eq_of_isOpenImmersion e.source.ι]
    _ = genericPoint S := genericPoint_eq_of_isOpenImmersion (e.source.ι ≫ f)


noncomputable def birationalFunctionFieldIso
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (f : Z ⟶ S) (hf : Scheme.BirationalOver f (𝟙 S)) :
    S.functionField ≅ Z.functionField := by
  have := birationalOver_isIso_generic_stalkMap f hf
  exact (S.presheaf.stalkCongr
    (.of_eq (birationalOver_map_genericPoint f hf).symm)) ≪≫
      asIso (f.stalkMap (genericPoint Z))

set_option backward.isDefEq.respectTransparency false in
theorem birationalFunctionFieldIso_stalkSpecializes
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (f : Z ⟶ S) (hf : Scheme.BirationalOver f (𝟙 S)) (z : Z) :
    S.presheaf.stalkSpecializes (genericPoint_specializes (f z)) ≫
        (birationalFunctionFieldIso f hf).hom =
      f.stalkMap z ≫ Z.presheaf.stalkSpecializes (genericPoint_specializes z) := by
  simpa [birationalFunctionFieldIso, TopCat.Presheaf.stalkCongr_hom,
    ← Category.assoc] using
      f.stalkSpecializes_stalkMap (genericPoint Z) z (genericPoint_specializes z)

noncomputable def stalkToSourceFunctionField
    {S Z : Scheme.{u}} [IsIntegral Z] (f : Z ⟶ S) (z : Z) :
    S.presheaf.stalk (f z) ⟶ Z.functionField :=
  f.stalkMap z ≫ Z.presheaf.stalkSpecializes (genericPoint_specializes z)

set_option backward.isDefEq.respectTransparency false in
theorem birationalOver_isFractionRing_stalk
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (f : Z ⟶ S) (hf : Scheme.BirationalOver f (𝟙 S)) (z : Z) :
    letI := (stalkToSourceFunctionField f z).hom.toAlgebra
    IsFractionRing (S.presheaf.stalk (f z)) Z.functionField := by
  let := (stalkToSourceFunctionField f z).hom.toAlgebra
  let e := birationalFunctionFieldIso f hf
  let g : S.functionField →ₐ[S.presheaf.stalk (f z)] Z.functionField :=
    { e.hom.hom with
      commutes' := fun r => by
        change e.hom (S.presheaf.stalkSpecializes
          (genericPoint_specializes (f z)) r) = stalkToSourceFunctionField f z r
        exact congrArg (fun k : S.presheaf.stalk (f z) ⟶ Z.functionField => k r)
          (birationalFunctionFieldIso_stalkSpecializes f hf z) }
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofBijective g (ConcreteCategory.bijective_of_isIso e.hom))

end Langlands.AlgebraicGeometry
