/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.Algebra.Category.Grp.Limits
import WeilConjectures.CategoryTheory.SheafAbelianObjectsSurjective
import WeilConjectures.CategoryTheory.SheafAbelianObjectsInjective

/-!
# Sectionwise abelian sheaves and commutative group objects

Source: Stacks Project, Section 00YR and Proposition 00YV.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Source: Stacks Project Section 00YR, quadruples and Proposition 00YV.
(blueprint: lem-weil-pbc-sheaf-abelian-objects-bijective)
Proof: for an internal commutative group object, evaluate multiplication, unit, and
inverse on every section. These operations give an additive commutative group by
evaluating the internal group identities, using that products and the terminal sheaf
are sectionwise. Naturality makes every restriction additive. The underlying sets
already form a sheaf, so Presheaf.isSheaf_iff_isSheaf_forget makes the algebraic
presheaf a sheaf as well. No choice of a new underlying set is needed.
For surjectivity, apply F to the reconstructed sheaf. The section formulas identify
its three internal operations with the original operations, and hF identifies the
underlying sheaf. Extensionality and proof irrelevance give equality of objects.
For injectivity, an equality F(A)=F(B) identifies underlying sheaves through hF;
the section formulas identify their addition, zero and negation. Natural and integer
scalar multiplication and subtraction are determined by these operations and their
recursion laws. Thus the additive group structures agree. Restrictions agree by
extensionality of homomorphisms, and sheaf witnesses agree by proof irrelevance. -/
theorem sheafAbelianObjects_bijective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w}))
    (hsections : (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)))) :
    Function.Bijective F.obj := by
  exact ⟨sheafAbelianObjects_injective J F hF hsections,
    sheafAbelianObjects_surjective J F hF hsections⟩

end CategoryTheory
