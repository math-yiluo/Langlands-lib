import Langlands.AlgebraicGeometry.Picard.BirationalUnramifiedOpenImmersionStatement
import Langlands.AlgebraicGeometry.Picard.BirationalGenericStalk
import Langlands.AlgebraicGeometry.Picard.IntegralLocalSections
import Langlands.AlgebraicGeometry.Picard.LocalUnramifiedBirationalAlgebraProof

/-! # Birational unramified morphisms are open immersions -/

universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem isIso_stalkMap_of_birational_unramified
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (hS : GeometricallyUnibranchIntegralScheme S)
    (f : Z ⟶ S) [LocallyOfFiniteType f] [FormallyUnramified f]
    (hf : Scheme.BirationalOver f (𝟙 S)) (z : Z) :
    IsIso (f.stalkMap z) := by
  let R := S.presheaf.stalk (f z)
  let B := Z.presheaf.stalk z
  let K := Z.functionField
  let : Algebra R B := (f.stalkMap z).hom.toAlgebra
  let : Algebra R K := (stalkToSourceFunctionField f z).hom.toAlgebra
  have : IsFractionRing R K := birationalOver_isFractionRing_stalk f hf z
  have : IsLocalHom (algebraMap R B) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  have : Algebra.EssFiniteType R B := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f z
  have : Algebra.FormallyUnramified R B := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f z
  let j : B →ₐ[R] K :=
    { (Z.presheaf.stalkSpecializes (genericPoint_specializes z)).hom with
      commutes' := fun _ => rfl }
  have hj : Function.Injective j := IsFractionRing.injective B K
  have hsurj : Function.Surjective (f.stalkMap z) :=
    algebraMap_surjective_of_essFiniteType_unramified_fractionRing_embedding
      R (hS (f z)) B K j hj
  have hinj : Function.Injective (f.stalkMap z) := by
    intro a b hab
    apply IsFractionRing.injective R K
    exact congrArg j hab
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

theorem birationalUnramifiedOpenImmersion :
    BirationalUnramifiedOpenImmersionStatement.{u} := by
  intro S Z _ _ hS f _ _ _ hf
  exact isOpenImmersion_of_isIso_stalkMap_of_integral f
    (isIso_stalkMap_of_birational_unramified hS f hf)

end Langlands.AlgebraicGeometry
