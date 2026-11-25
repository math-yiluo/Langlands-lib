/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Exact injective augmentation on a total simplicial site

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79, lemma-augmentation-cech-complex
(blueprint: lem-trf-total-site-injective-augmentation-exactness).

The component categories and their coherent inverse-image geometric morphisms are
represented by `TotalSiteSystemData`; `a` gives the component augmentations and their
identity/composition coherences, and `totalInverse` identifies every component inverse
image with the induced total inverse image.  The displayed maps are the adjoint mates of
the component transition maps, and the augmentation is the mate of the degree-zero
counit component.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w x y u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

/-- A compatible family of component objects, with the identity and composition laws.
Source: Stacks Project, Tag 09WF and the preceding system description
(blueprint: lem-trf-total-site-component-restriction). -/
structure TotalSiteCompatibleSystem
    (A : SimplexCategoryᵒᵖ → Type v) [∀ i, Category.{w} (A i)]
    (pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j)
    (pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i))
    (pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g) where
  obj : ∀ i, A i
  transition : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i), (pull f).obj (obj i) ⟶ obj j
  transition_id : ∀ i, transition (𝟙 i) = (pullId i).hom.app (obj i)
  transition_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
    transition (g ≫ f) = (pullComp f g).hom.app (obj i) ≫
      (pull g).map (transition f) ≫ transition g

/-- Morphisms of the actual compatible families are compatible component maps.
Source: Stacks Project, Tag 09WF (blueprint: lem-trf-total-site-component-restriction). -/
structure TotalSiteCompatibleMorphism
    {A : SimplexCategoryᵒᵖ → Type v} [∀ i, Category.{w} (A i)]
    {pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j}
    {pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i)}
    {pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g}
    (X Y : TotalSiteCompatibleSystem A pull pullId pullComp) where
  app : ∀ i, X.obj i ⟶ Y.obj i
  comm : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (pull f).map (app i) ≫ Y.transition f = X.transition f ≫ app j

/-- A fully faithful, essentially surjective presentation of the compatible-system category.
`map_bijective` identifies each Hom set with ALL compatible component maps;
`essentially_surjective` realizes EVERY compatible family, up to compatible component
isomorphisms. Together these are the equivalence criterion, with evaluation given by
`component`. No arbitrary category with transitions qualifies. `pull_id_left`,
`pull_id_right`, and `pull_assoc` are the two unit laws and the full cocycle identity.
Source: Stacks Project, Tags 09WF and 09WG
(blueprint: lem-trf-total-site-component-restriction). -/
structure TotalSiteSystemData
    (A : SimplexCategoryᵒᵖ → Type v)
    [∀ i, Category.{w} (A i)]
    (pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j)
    (pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i))
    (pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g)
    (T : Type u) [Category.{w} T] [Preadditive T] [∀ i, Preadditive (A i)] where
  pull_id_left : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (X : A i),
    (pullComp f (𝟙 j)).hom.app X ≫ (pullId j).hom.app ((pull f).obj X) =
      eqToHom (congrArg (fun q ↦ (pull q).obj X) (Category.id_comp f))
  pull_id_right : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (X : A i),
    (pullComp (𝟙 i) f).hom.app X ≫ (pull f).map ((pullId i).hom.app X) =
      eqToHom (congrArg (fun q ↦ (pull q).obj X) (Category.comp_id f))
  pull_assoc : ∀ {i j k l : SimplexCategoryᵒᵖ}
    (f : j ⟶ i) (g : k ⟶ j) (h : l ⟶ k) (X : A i),
    (pullComp f (h ≫ g)).hom.app X ≫ (pullComp g h).hom.app ((pull f).obj X) =
      eqToHom (congrArg (fun q ↦ (pull q).obj X) (Category.assoc h g f)) ≫
        (pullComp (g ≫ f) h).hom.app X ≫ (pull h).map ((pullComp f g).hom.app X)
  component : ∀ i, T ⥤ A i
  component_additive : ∀ i, (component i).Additive
  transition : ∀ (X : T) (i j : SimplexCategoryᵒᵖ) (f : j ⟶ i),
    (pull f).obj ((component i).obj X) ⟶ (component j).obj X
  transition_id : ∀ (X : T) (i : SimplexCategoryᵒᵖ),
    transition X i i (𝟙 i) = (pullId i).hom.app ((component i).obj X)
  transition_comp : ∀ (X : T) (i j k : SimplexCategoryᵒᵖ)
    (f : j ⟶ i) (g : k ⟶ j),
    transition X i k (g ≫ f) =
      (pullComp f g).hom.app ((component i).obj X) ≫
        (pull g).map (transition X i j f) ≫ transition X j k g
  transition_naturality : ∀ {X Y : T} (h : X ⟶ Y)
    (i j : SimplexCategoryᵒᵖ) (f : j ⟶ i),
    (pull f).map ((component i).map h) ≫ transition Y i j f =
      transition X i j f ≫ (component j).map h
  map_bijective : ∀ (X Y : T), Function.Bijective
    (fun h : X ⟶ Y ↦
      (⟨fun i ↦ (component i).map h, fun f ↦ transition_naturality h _ _ f⟩ :
        TotalSiteCompatibleMorphism
          ⟨fun i ↦ (component i).obj X, fun f ↦ transition X _ _ f,
            transition_id X, fun f g ↦ transition_comp X _ _ _ f g⟩
          ⟨fun i ↦ (component i).obj Y, fun f ↦ transition Y _ _ f,
            transition_id Y, fun f g ↦ transition_comp Y _ _ _ f g⟩))
  essentially_surjective : ∀ F : TotalSiteCompatibleSystem A pull pullId pullComp,
    ∃ (X : T) (e : ∀ i, (component i).obj X ≅ F.obj i),
      ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
        (pull f).map (e i).hom ≫ F.transition f = transition X i j f ≫ (e j).hom
  pull_exact : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    PreservesFiniteLimits (pull f) ∧ PreservesFiniteColimits (pull f)

attribute [instance] TotalSiteSystemData.component_additive

/-- The direct-image comparison corresponding by adjunction to an identity
inverse-image comparison.  Source: Stacks Project, `spaces-simplicial.tex`,
the identity coherence in the simplicial augmentation (blueprint:
`lem-trf-total-site-injective-augmentation-exactness`). -/
noncomputable def augmentationDirectIdIso {E : Type u₁}
    [Category.{v₁} E] (m : GeometricMorphism E E)
    (h : m.inverse ≅ 𝟭 E) : m.direct ≅ 𝟭 E :=
  (conjugateIsoEquiv m.adj Adjunction.id) h.symm

/-- The direct-image comparison corresponding by adjunction to a composition
inverse-image comparison.  Source: Stacks Project, `spaces-simplicial.tex`,
the composition coherence in the simplicial augmentation (blueprint:
`lem-trf-total-site-injective-augmentation-exactness`). -/
noncomputable def augmentationDirectCompIso {E : Type u₁} {F : Type u₂} {G : Type u₃}
    [Category.{v₁} E] [Category.{v₂} F] [Category.{v₃} G]
    (m : GeometricMorphism E G) (f : GeometricMorphism F G)
    (g : GeometricMorphism E F)
    (h : m.inverse ≅ f.inverse ⋙ g.inverse) :
    m.direct ≅ g.direct ⋙ f.direct :=
  (conjugateIsoEquiv m.adj (f.adj.comp g.adj)) h.symm

/-- Data of a simplicial family of abelian sheaf categories with an augmentation to a
common abelian sheaf category.  The fields are the site morphisms, their identity and
composition coherences, the compatible-system presentation of the total site, the
component augmentation morphisms and their coherences, and the induced total
augmentation.  Source: Stacks Project, Tags 09WF, 09WG and 0D79
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
structure TotalSiteAugmentationData
    (A : SimplexCategoryᵒᵖ → Type v)
    [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
    (T : Type u) [Category.{w} T] [Abelian T]
    (D : Type x) [Category.{y} D] [Abelian D] where
  u : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) →
    GeometricMorphism (A j) (A i)
  pullId : ∀ i, (u (𝟙 i)).inverse ≅ 𝟭 (A i)
  pullComp : ∀ {_i _j k : SimplexCategoryᵒᵖ} (f : _j ⟶ _i) (g : k ⟶ _j),
    (u (g ≫ f)).inverse ≅ (u f).inverse ⋙ (u g).inverse
  system : TotalSiteSystemData A (fun {_i _j} f ↦ (u f).inverse)
    pullId pullComp T
  a : ∀ i, GeometricMorphism (A i) D
  aComp : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (a j).direct ≅ ((u f).comp (a i)).direct
  aComp_id : ∀ i,
    (aComp (𝟙 i)).trans
        ((Functor.isoWhiskerRight
            (augmentationDirectIdIso (u (𝟙 i)) (pullId i)) (a i).direct).trans
          (Functor.leftUnitor (a i).direct)) = Iso.refl _
  aComp_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
    (aComp (g ≫ f)).trans
        ((Functor.isoWhiskerRight
            (augmentationDirectCompIso (m := u (g ≫ f)) (f := u f) (g := u g)
              (pullComp f g)) (a i).direct).trans
          (Functor.associator (u g).direct (u f).direct (a i).direct)) =
      (aComp g).trans (Functor.isoWhiskerLeft (u g).direct (aComp f))
  total : GeometricMorphism T D
  totalInverse : ∀ i, (a i).inverse ≅ total.inverse ⋙ system.component i
  totalInverse_transition : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (G : D),
    system.transition (total.inverse.obj G) i j f =
      (u f).inverse.map ((totalInverse i).inv.app G) ≫
        (GeometricMorphism.inverseIso (aComp f)).hom.app G ≫
          (totalInverse j).hom.app G

namespace TotalSiteAugmentationData

variable {A : SimplexCategoryᵒᵖ → Type v}
  [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
  {T : Type u} [Category.{w} T] [Abelian T]
  {D : Type x} [Category.{y} D] [Abelian D]
  (S : TotalSiteAugmentationData A T D)

/-- The coface map induced by the transition along the `i`-th face, using the
adjunction `(u face).inverse ⊣ (u face).direct` and the coherence `aComp`.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79,
lemma-augmentation-cech-complex, Hom-adjunction construction
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def faceMap (I : T) (p : ℕ) (i : Fin (p + 2)) :
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk p))).obj I) ⟶
      (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) := by
  exact
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.map
        ((S.u (SimplexCategory.δ i).op).adj.homEquiv _ _
          (S.system.transition I _ _ (SimplexCategory.δ i).op)) ≫
      (S.aComp (SimplexCategory.δ i).op).inv.app _

/-- The alternating face differential in degree `p`.
Source: Stacks Project, `spaces-simplicial.tex`, Tags 0D78 and 0D79,
lemma-simplicial-resolution-augmentation and lemma-augmentation-cech-complex
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def differential (I : T) (p : ℕ) :
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk p))).obj I) ⟶
      (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • S.faceMap I p i

/-- The augmentation map, mate to the degree-zero component of the counit of the
induced total geometric morphism.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79,
lemma-augmentation-cech-complex, augmentation under the Hom adjunction
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def augmentation (I : T) :
    S.total.direct.obj I ⟶
      (S.a (Opposite.op (SimplexCategory.mk 0))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk 0))).obj I) :=
  (S.a (Opposite.op (SimplexCategory.mk 0))).adj.homEquiv (S.total.direct.obj I)
    ((S.system.component (Opposite.op (SimplexCategory.mk 0))).obj I)
    ((S.totalInverse (Opposite.op (SimplexCategory.mk 0))).hom.app
        (S.total.direct.obj I) ≫
      (S.system.component (Opposite.op (SimplexCategory.mk 0))).map
        (S.total.adj.counit.app I))

end TotalSiteAugmentationData

end CategoryTheory
