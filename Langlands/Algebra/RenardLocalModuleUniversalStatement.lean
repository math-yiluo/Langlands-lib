import Langlands.Algebra.RenardLocalModuleCategory

/-! # The actual categorical universal property of module localization -/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Renard.ModuleLocalization

universe u v w

/-- The constructed factor satisfies the actual right universal-arrow equation. -/
def CategoricalFactorizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : LocalModuleCat.{u, max u v w} S)
    (f : raisedSource.{u, v, w} (R := R) M ⟶ N.obj),
    canonicalModuleMap.{u, v, w} S M ≫
      (localModuleInclusion.{u, max u v w} S).map
        (canonicalFactor.{u, v, w} S M N f) = f

/-- Every local-category factor satisfying the canonical equation is the
constructed factor; no universal-property certificate is supplied as input. -/
def CategoricalFactorUniquenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : LocalModuleCat.{u, max u v w} S)
    (f : raisedSource.{u, v, w} (R := R) M ⟶ N.obj)
    (g : canonicalLocalObject.{u, v, w} S M ⟶ N),
    canonicalModuleMap.{u, v, w} S M ≫
      (localModuleInclusion.{u, max u v w} S).map g = f →
    g = canonicalFactor.{u, v, w} S M N f

/-- The actual canonical structured arrow admits initiality data.
`Nonempty` makes this a proposition, rather than a choice of that data. -/
def CategoricalInitialityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R)
    (M : Type v) [AddCommGroup M] [Module R M],
    Nonempty (StructuredArrow.IsUniversal
      (canonicalStructuredArrow.{u, v, w} S M))

/-- Closed factorization, uniqueness and initiality assertions over the actual
full subcategory and the explicitly raised actual localized module. -/
def CategoricalUniversalStatements : Prop :=
  CategoricalFactorizationStatement.{u, v, w} ∧
    CategoricalFactorUniquenessStatement.{u, v, w} ∧
    CategoricalInitialityStatement.{u, v, w}

end Langlands.Renard.ModuleLocalization
