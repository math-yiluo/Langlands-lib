import Langlands.AlgebraicGeometry.RelativeDerivations

/-!
# Sheafification of relative derivations

Internal infrastructure: sheafify a presheaf derivation and transfer its
universal property by the module-sheafification adjunction.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open PresheafOfModulesOfCommRing

namespace Langlands.Scheme

variable {X S : AlgebraicGeometry.Scheme.{u}}

/-- The module-sheafification functor on a scheme. -/
def moduleSheafification (X : AlgebraicGeometry.Scheme.{u}) :
    X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The unit from a module presheaf into its associated module sheaf. -/
def moduleSheafificationUnit (P : X.PresheafOfModules) :
    P ⟶ ((moduleSheafification X).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P

/-- The sheafification adjunction, as an equivalence of morphism types. -/
def moduleSheafificationHomEquiv (P : X.PresheafOfModules) (M : X.Modules) :
    ((moduleSheafification X).obj P ⟶ M) ≃ (P ⟶ M.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)

lemma moduleSheafificationHomEquiv_apply (P : X.PresheafOfModules) (M : X.Modules)
    (α : (moduleSheafification X).obj P ⟶ M) :
    moduleSheafificationHomEquiv P M α = moduleSheafificationUnit P ≫ α.val := by
  rfl

variable {f : X ⟶ S} {P : X.PresheafOfModules}

/-- Postcompose a presheaf derivation with the unit of module sheafification. -/
def sheafifyRelativeDerivation
    (d : Derivation (R := X.presheaf) P (F := Opens.map f.base) f.c) :
    RelativeDerivation f ((moduleSheafification X).obj P) :=
  d.postcomp (moduleSheafificationUnit P)

/-- A universal presheaf derivation identifies its outgoing morphisms with
derivations. This uses its proved universal structure explicitly. -/
def presheafDerivationHomEquiv
    (d : Derivation (R := X.presheaf) P (F := Opens.map f.base) f.c) (h : d.Universal)
    (N : X.PresheafOfModules) :
    (P ⟶ N) ≃ Derivation (R := X.presheaf) N (F := Opens.map f.base) f.c where
  toFun α := d.postcomp α
  invFun δ := h.desc δ
  left_inv _α := h.postcomp_injective _ _ (h.fac _)
  right_inv δ := h.fac δ

/-- The universal morphism equivalence after sheafification. This is a transfer
construction; it does not assert that a universal presheaf derivation exists. -/
def sheafifyRelativeDerivationHomEquiv
    (d : Derivation (R := X.presheaf) P (F := Opens.map f.base) f.c) (h : d.Universal)
    (M : X.Modules) :
    ((moduleSheafification X).obj P ⟶ M) ≃ RelativeDerivation f M :=
  (moduleSheafificationHomEquiv P M).trans (presheafDerivationHomEquiv d h M.val)

lemma sheafifyRelativeDerivationHomEquiv_apply
    (d : Derivation (R := X.presheaf) P (F := Opens.map f.base) f.c) (h : d.Universal)
    (M : X.Modules) (α : (moduleSheafification X).obj P ⟶ M) :
    sheafifyRelativeDerivationHomEquiv d h M α =
      RelativeDerivation.postcomp (sheafifyRelativeDerivation d) α := by
  ext U a
  rfl

lemma sheafifyRelativeDerivationHomEquiv_naturality
    (d : Derivation (R := X.presheaf) P (F := Opens.map f.base) f.c) (h : d.Universal)
    {M N : X.Modules} (α : (moduleSheafification X).obj P ⟶ M) (β : M ⟶ N) :
    sheafifyRelativeDerivationHomEquiv d h N (α ≫ β) =
      RelativeDerivation.postcomp (sheafifyRelativeDerivationHomEquiv d h M α) β := by
  simp only [sheafifyRelativeDerivationHomEquiv_apply, RelativeDerivation.postcomp_comp]

/-- The natural equivalence of functors obtained by sheafifying a universal
presheaf derivation. -/
def sheafifyRelativeDerivationCorepresentable
    (d : Derivation (R := X.presheaf) P (F := Opens.map f.base) f.c) (h : d.Universal) :
    (relativeDerivationFunctor f).CorepresentableBy ((moduleSheafification X).obj P) where
  homEquiv := sheafifyRelativeDerivationHomEquiv d h _
  homEquiv_comp β α := sheafifyRelativeDerivationHomEquiv_naturality d h α β

end Langlands.Scheme
