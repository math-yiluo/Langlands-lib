import Langlands.Algebra.RenardLocalModuleUniversalStatement

/-! # The categorical universal property of the actual module localization -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard.ModuleLocalization

universe u v w

/-- The published factor commutes with the actual canonical map. -/
theorem categoricalFactorizationStatement :
    CategoricalFactorizationStatement.{u, v, w} := by
  intro R _ S M _ _ N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  cases x with
  | up m =>
    change factor S N.property
      (f.hom.comp (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap)
        (LocalizedModule.mkLinearMap S M m) = f (ULift.up m)
    exact LinearMap.congr_fun
      (factor_comp S N.property
        (f.hom.comp (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap)) m

/-- Every commuting morphism in the actual full subcategory is the published factor. -/
theorem categoricalFactorUniquenessStatement :
    CategoricalFactorUniquenessStatement.{u, v, w} := by
  intro R _ S M _ _ N f g hg
  let f₀ : M →ₗ[R] N.obj :=
    f.hom.comp (ULift.moduleEquiv (R := R) (M := M)).symm.toLinearMap
  let g₀ : LocalizedModule S M →ₗ[R] N.obj :=
    g.hom.hom.comp
      (ULift.moduleEquiv (R := R) (M := LocalizedModule S M)).symm.toLinearMap
  have hg₀ : g₀.comp (LocalizedModule.mkLinearMap S M) = f₀ := by
    ext m
    exact congrArg
      (fun k : raisedSource.{u, v, w} (R := R) M ⟶ N.obj => k (ULift.up m)) hg
  have heq : g₀ = factor S N.property f₀ :=
    factor_unique S N.property f₀ g₀ hg₀
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  cases z with
  | up z =>
    exact LinearMap.congr_fun heq z

/-- The canonical structured arrow has actual initiality data. -/
theorem categoricalInitialityStatement :
    CategoricalInitialityStatement.{u, v, w} := by
  intro R _ S M _ _
  refine ⟨Limits.IsInitial.ofUniqueHom ?_ ?_⟩
  · intro A
    exact StructuredArrow.homMk (canonicalFactor.{u, v, w} S M A.right A.hom)
      (categoricalFactorizationStatement.{u, v, w} R S M A.right A.hom)
  · intro A g
    apply StructuredArrow.hom_ext
    exact categoricalFactorUniquenessStatement.{u, v, w}
      R S M A.right A.hom g.right (StructuredArrow.w g)

/-- The exact published categorical localization aggregate, at independent universes. -/
theorem categoricalUniversalStatements :
    CategoricalUniversalStatements.{u, v, w} :=
  ⟨categoricalFactorizationStatement,
    categoricalFactorUniquenessStatement,
    categoricalInitialityStatement⟩

end Langlands.Renard.ModuleLocalization
