/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Geometric stalks on the small pro-etale site

Source: the Weil conjectures blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence;
Stacks Project, Tag 0F6B and the preceding definition of pro-etale neighbourhood
(auxiliary; not a blueprint node).

The bounded site has objects in `Type (u + 1)` and morphisms in `Type u`.
Neighbourhoods and colimits are formed in the larger universe `u + 1`.
The generic stalk specializes to sets and to modules over any fixed commutative ring.
For varying coefficients we use `PresheafOfModules.colimitFunctor`: its scalar action
is induced by sectionwise scalar multiplication after common refinement, rather than
regarding semilinear restriction maps as linear over a fixed section ring.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- Pointed weakly etale neighbourhoods of `y`. Objects are weakly etale `U → Y`
with a lift `Spec Ω → U` over `Y`; arrows are `Y`-morphisms preserving the lift.
Source: Stacks Project, definition preceding Tag 0F6B
(auxiliary; not a blueprint node). -/
abbrev ProEtaleGeometricNeighbourhood [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :=
  StructuredArrow (Over.mk y) (ProEt.forget Y)

/-- Forget the lift in a pointed neighbourhood, retaining its object of the pro-etale site.
Source: Stacks Project, definition preceding Tag 0F6B
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleGeometricNeighbourhoodForget [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    ProEtaleGeometricNeighbourhood y ⥤ Y.ProEt :=
  StructuredArrow.proj (Over.mk y) (ProEt.forget Y)

/-- The neighbourhood category is cofiltered, equivalently its opposite is filtered.
Source: Stacks Project, Tag 0F6B (auxiliary; not a blueprint node).

Proof: `(Y,y)` gives nonemptiness. The fibre product of two neighbourhoods with
its paired lift gives a common refinement (base change and composition of weakly
etale maps, `lem-weil-pbc-weakly-etale-composition-base-change`, `def-pc-fibre-product`).
For parallel arrows `h₁,h₂ : U → V`, put `Q = V ×_Y V`, weakly etale over `Y`.
The between-objects lemma `lemma-stability--5` makes
`(h₁,h₂) : U → Q` weakly etale. Put `E = U ×_Q V`, using the diagonal `V → Q`.
Base change makes `E → V` weakly etale, and composition makes `E → Y` weakly etale.
The paired lift exists since both arrows preserve the point; the pullback equation
gives `h₁p = q = h₂p` for the projections `p : E → U` and `q : E → V`.
Thus the pointed projection `p` equalizes the arrows.
All these finite constructions remain in the chosen bound (`prose-01-10`). -/
theorem proEtaleGeometricNeighbourhood_isCofiltered [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    IsCofiltered (ProEtaleGeometricNeighbourhood y) := by
  infer_instance

attribute [instance] proEtaleGeometricNeighbourhood_isCofiltered

/-- The bounded neighbourhood category is small in the larger universe.
Source: the blueprint size convention (auxiliary; not a blueprint node). -/
noncomputable instance proEtaleGeometricNeighbourhood_initiallySmall [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) : InitiallySmall.{u + 1} (ProEtaleGeometricNeighbourhood y) :=
  initiallySmall_of_essentiallySmall _

/-- Colimits over pointed neighbourhoods exist in categories with colimits in the larger
universe. Source: the blueprint size convention
(auxiliary; not a blueprint node). -/
noncomputable instance proEtaleGeometricNeighbourhood_hasColimitsOfShape [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (C : Type v) [Category.{w} C]
    [HasColimitsOfSize.{u + 1, u + 1} C] :
    HasColimitsOfShape (ProEtaleGeometricNeighbourhood y)ᵒᵖ C :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The diagram `D_F`: evaluate `F` on neighbourhoods and use its restriction maps.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleGeometricStalkDiagram [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {C : Type v} [Category.{w} C] (F : Sheaf (ProEt.topology Y) C) :
    (ProEtaleGeometricNeighbourhood y)ᵒᵖ ⥤ C :=
  (proEtaleGeometricNeighbourhoodForget y).op ⋙ F.obj

/-- The geometric stalk, the colimit of sections over pointed weakly etale neighbourhoods.
Take `C = Type (u + 1)` for sets, or `C = ModuleCat A` for fixed coefficients.
For sets the colimit is the disjoint union of sections modulo the equivalence relation
generated by restriction along pointed arrows. In fixed modules it is the direct sum
modulo the submodule generated by the differences of a section and its restriction.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence; Stacks
Project, Tags 040R, 03PN, 0F6B (auxiliary; not a blueprint node). -/
noncomputable def proEtaleGeometricStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    {C : Type v} [Category.{w} C] [HasColimitsOfSize.{u + 1, u + 1} C]
    (F : Sheaf (ProEt.topology Y) C) : C :=
  colimit (proEtaleGeometricStalkDiagram y F)

/-- The set-valued geometric stalk in the chosen larger universe.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence
(auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleGeometricSetStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf (ProEt.topology Y) (Type (u + 1))) : Type (u + 1) :=
  proEtaleGeometricStalk y F

/-- The stalk with fixed commutative coefficients, using the same diagram in `A`-modules.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence
(auxiliary; not a blueprint node). -/
noncomputable abbrev proEtaleGeometricFixedModuleStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) : ModuleCat.{u + 1} A :=
  proEtaleGeometricStalk y F

/-- The diagram of rings underlying a commutative ring sheaf on pointed neighbourhoods.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleGeometricStalkRingDiagram [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (ProEtaleGeometricNeighbourhood y)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (proEtaleGeometricNeighbourhoodForget y).op ⋙ O.obj ⋙
    forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The stalk ring, with operations induced from sections at common pointed refinements.
Its underlying set is the filtered colimit of the underlying sets; forgetting commutativity
here allows use of the general `PresheafOfModules` construction.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence
(auxiliary; not a blueprint node). -/
noncomputable def proEtaleGeometricStalkRing [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) : RingCat.{u + 1} :=
  colimit (proEtaleGeometricStalkRingDiagram y O)

/-- The stalk of an `O`-module sheaf as a module over the stalk ring. The Mathlib
colimit-module construction takes the additive colimit and defines scalar multiplication
by representing scalars and vectors at a common refinement. Its action respects the
semilinear restriction maps; no single section ring is used as a fixed coefficient ring.
Source: the blueprint, `definition-ind-etale-pro-etale-weakly--3`, last sentence; Stacks Project,
Tags 0F6B and 002F (auxiliary; not a blueprint node). -/
noncomputable def proEtaleGeometricModuleStalk [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    ModuleCat.{u + 1} (proEtaleGeometricStalkRing y O) :=
  (PresheafOfModules.colimitFunctor
    (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))).obj
      ((PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
        (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj F.val)

end AlgebraicGeometry.Scheme
