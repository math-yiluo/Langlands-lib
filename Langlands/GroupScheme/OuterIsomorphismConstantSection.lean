import Langlands.GroupScheme.OuterIsomorphismNormalizedSection
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Outer quotients from constant families of representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.GroupIsomorphismScheme

/-- The scheme over `S` consisting of one copy of `S` for every label in `D`. -/
def constantParameter (S : Scheme.{u}) (D : Type u) : Over S :=
  Over.mk (Sigma.desc (fun _ : D => 𝟙 S))

instance constantParameter_isSeparated (S : Scheme.{u}) (D : Type u) :
    IsSeparated (constantParameter S D).hom :=
  AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated
    (fun _ : D => S) (fun _ => 𝟙 S) (fun _ => inferInstance)

instance constantParameter_etale (S : Scheme.{u}) (D : Type u) :
    Etale (constantParameter S D).hom :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun _ : D => inferInstance)

instance constantParameter_locallyQuasiFinite (S : Scheme.{u}) (D : Type u) :
    LocallyQuasiFinite (constantParameter S D).hom :=
  IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite.{u})
    (fun _ : D => inferInstance)

instance constantParameter_locallyOfFiniteType (S : Scheme.{u}) (D : Type u) :
    LocallyOfFiniteType (constantParameter S D).hom := by
  infer_instance

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)
  (D : Type u) (s : constantParameter S D ⟶ I.parameter)
  (h : ∀ (T : Over S), Function.Bijective
    (fun z : (T ⟶ A.X) × (T ⟶ constantParameter S D) =>
      lift z.1 (z.2 ≫ s) ≫ I.actionHom a))

/-- A constant family with unique acting-group decomposition on every scheme test
gives an actual outer quotient. -/
def outerOfConstantSection [Flat A.X.hom] [QuasiCompact A.X.hom] :
    OuterIsomorphismScheme I a :=
  I.outerOfNormalizedSection a s h

variable [Flat A.X.hom] [QuasiCompact A.X.hom]

@[simp] theorem outerOfConstantSection_parameter :
    (I.outerOfConstantSection a D s h).parameter = constantParameter S D := rfl

instance outerOfConstantSection_isSeparated :
    IsSeparated (I.outerOfConstantSection a D s h).parameter.hom := by
  change IsSeparated (constantParameter S D).hom
  infer_instance

instance outerOfConstantSection_etale :
    Etale (I.outerOfConstantSection a D s h).parameter.hom := by
  change Etale (constantParameter S D).hom
  infer_instance

instance outerOfConstantSection_locallyQuasiFinite :
    LocallyQuasiFinite (I.outerOfConstantSection a D s h).parameter.hom := by
  change LocallyQuasiFinite (constantParameter S D).hom
  infer_instance

instance outerOfConstantSection_locallyOfFiniteType :
    LocallyOfFiniteType (I.outerOfConstantSection a D s h).parameter.hom := by
  change LocallyOfFiniteType (constantParameter S D).hom
  infer_instance

end Langlands.GroupScheme.GroupIsomorphismScheme
