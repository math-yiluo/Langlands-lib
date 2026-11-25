/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.AlgebraicGeometry.EtaleStructureSectionsEquiv

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

/-- The lifted étale structure-module sheaf has natural additive section identifications.
Source: blueprint `lemma-p-torsion-affine-curve-characteristic--3`, the maps paragraph; Stacks, Tags
03DR and 03DU for the section presheaf, and Tags 0096 and 01CA for pullback of the structure module.
(blueprint: lem-sc-as-sequence-construction-helper)

Proof: Choose G to be the displayed lifted sheaf, with the identity isomorphism.
For u : U → C, the morphism epsilon_u adjoint to the structure-sheaf map u-sharp is
an isomorphism by tensorPullbackObjUnitToUnit_isIso. Evaluating it on the top open
identifies sections of u*O_C with Gamma(U, O_U). Compose this additive equivalence
with ULift.down to obtain a U. For g : V → U over C, the restriction is section
pullback by the adjunction unit followed by the unit-normalized composition
isomorphism and transport along g ≫ u = v. The unit characterization of epsilon_u
and epsilon_v identifies its image under epsilon_v with g-sharp after epsilon_u:
both morphisms have the same adjoint, namely the composite structure-sheaf map.
Uniqueness under the adjunction proves equality. On top-open sections this is
exactly the stated restriction identity, which is preserved by ULift.down. -/
theorem artinSchreier_construction (C : Scheme.{u}) :
    ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : G ≅ (sheafCompose C.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
      (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤)),
      ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x) := by
  refine ⟨_, Iso.refl _, etaleStructureSectionsEquiv C, ?_⟩
  intro U V g x
  exact etaleStructureSectionsEquiv_naturality C U V g x

end AlgebraicGeometry
