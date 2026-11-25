/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# The canonical extension presentation of an étale torsor

Source: Stacks Project, Cohomology on Sites, Lemma 03AJ, construction from the free abelian
sheaf (auxiliary; not a blueprint node).
-/

@[expose] public section

universe uE wE

open CategoryTheory CategoryTheory.Limits Opposite

-- Use the site itself as a small model in the larger coefficient universe.
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace CategoryTheory.Sheaf.Torsor

/-- The canonical extension associated to a torsor, specified by its quotient universal
property. It is the quotient of `G ⊕ ℤ[T]` by `j(g +ᵥ t) = j(t) + i(g)`; maps out of this
quotient are precisely a homomorphism out of `G` and a natural map out of `T` satisfying
that relation. The augmentation kills `G` and sends every generator to the constant `1`.
This characterizes the construction in Stacks, Tag 03AJ, without choosing representatives.
(auxiliary; not a blueprint node) -/
structure ExtensionPresentation (S : AlgebraicGeometry.Scheme.{uE})
    {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uE wE + 1}} (T : Torsor G) where
  middle : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uE wE + 1}
  inclusion : G ⟶ middle
  generator (U : S.Etaleᵒᵖ) : T.sheaf.obj.obj U → middle.obj.obj U
  generator_natural {U V : S.Etaleᵒᵖ} (f : U ⟶ V) (t : T.sheaf.obj.obj U) :
    middle.obj.map f (generator U t) = generator V (T.sheaf.obj.map f t)
  generator_vadd (U : S.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U) :
    generator U (T.vadd U g t) = generator U t + inclusion.hom.app U g
  universal (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{max uE wE + 1}) (k : G ⟶ A)
      (j : ∀ U : S.Etaleᵒᵖ, T.sheaf.obj.obj U → A.obj.obj U)
      (hn : ∀ ⦃U V : S.Etaleᵒᵖ⦄ (f : U ⟶ V) (t : T.sheaf.obj.obj U),
        A.obj.map f (j U t) = j V (T.sheaf.obj.map f t))
      (ha : ∀ (U : S.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.sheaf.obj.obj U),
        j U (T.vadd U g t) = j U t + k.hom.app U g) :
    ∃! l : middle ⟶ A, inclusion ≫ l = k ∧
      ∀ (U : S.Etaleᵒᵖ) (t : T.sheaf.obj.obj U), l.hom.app U (generator U t) = j U t
  projection : middle ⟶ (constantSheaf S.smallEtaleTopology AddCommGrpCat.{max uE wE + 1}).obj
    (AddCommGrpCat.of (ULift.{max uE wE + 1} ℤ))
  inclusion_projection : inclusion ≫ projection = 0
  projection_generator (U : S.Etaleᵒᵖ) (t : T.sheaf.obj.obj U) :
    projection.hom.app U (generator U t) =
      (toSheafify S.smallEtaleTopology
        ((Functor.const S.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{max uE wE + 1} ℤ)))).app U ⟨1⟩

end CategoryTheory.Sheaf.Torsor
