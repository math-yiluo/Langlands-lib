/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-!
# Cartesian scheme-test presentations of small-etale line modules

Source: Stacks Project, Properties of Spaces, Tag 03G7; Divisors on Spaces, Tag 0D2Z
(blueprint: def-trf-cartesian-line-presentation).

These are the existing presentation definitions, factored out so effective descent
and descent of morphisms can be used independently in their universal property.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Schemes mapping to a presheaf, with commuting triangles as morphisms.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-cartesian-line-presentation). -/
abbrev SchemeTests (F : (Over S)ᵒᵖ ⥤ Type u) := CostructuredArrow yoneda F

/-- The structural map of a scheme test to the scheme base.
Source: Stacks, Tag 0D2Z (blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def testToBase {F : (Over S)ᵒᵖ ⥤ Type u} {T : Over S}
    (f : F ⟶ yoneda.obj T) (W : SchemeTests F) : W.left ⟶ T :=
  yoneda.preimage (W.hom ≫ f)

/-- A family of invertible modules with specified tensor-pullback identifications.
Coherence and identification with the small-etale module are imposed below.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
structure TestLineFamily (F : (Over S)ᵒᵖ ⥤ Type u) where
  module (W : SchemeTests F) : W.left.left.Modules
  invertible (W : SchemeTests F) : (module W).IsInvertible
  pullbackIso {W V : SchemeTests F} (j : W ⟶ V) :
    (Scheme.Modules.tensorPullback j.left.left).obj (module V) ≅ module W

attribute [instance] TestLineFamily.invertible

/-- Pullback of a global section, using the tensor-formula adjunction normalized by
`1 ⊗ eta(s)`, followed by the specified cartesian identification.
Source: Stacks, Tags 0095, 0096 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def TestLineFamily.sectionMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V)
    (s : Γ(L.module V, ⊤)) : Γ(L.module W, ⊤) :=
  (L.pullbackIso j).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      (L.module V)).val.app (op ⊤) s)

/-- The same pullback on tensor powers, using the existing monoidal comparisons.
Source: Stacks, Tags 01CD and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def TestLineFamily.powerMap {F : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) {W V : SchemeTests F} (j : W ⟶ V) (n : ℕ)
    (s : Γ((L.module V).tensorPow n, ⊤)) : Γ((L.module W).tensorPow n, ⊤) :=
  (Scheme.Modules.boundaryPullbackPowIso j.left.left (L.module V) n ≪≫
    Scheme.Modules.boundaryTensorPowIso (L.pullbackIso j) n).hom.app ⊤
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j.left.left)).unit.app
      ((L.module V).tensorPow n)).val.app (op ⊤) s)

/-- The full identity and composition equations of the cartesian pullback isomorphisms.
These are equations of sheaf isomorphisms, so they include every local section.
Source: Stacks, Tags 03G7 and 0097
(blueprint: def-trf-cartesian-line-presentation). -/
def TestLineFamily.IsCoherent {F : (Over S)ᵒᵖ ⥤ Type u} (L : TestLineFamily F) : Prop :=
  (∀ W : SchemeTests F, L.pullbackIso (𝟙 W) =
    (Scheme.Modules.boundaryPullbackComparison (𝟙 W.left.left)).app (L.module W) ≪≫
      (Scheme.Modules.pullbackId W.left.left).app (L.module W)) ∧
    ∀ (W V Z : SchemeTests F) (j : W ⟶ V) (k : V ⟶ Z),
      L.pullbackIso (j ≫ k) =
        (Scheme.Modules.tensorPullbackCompositionIso j.left.left k.left.left
          (j ≫ k).left.left rfl).app (L.module Z) ≪≫
        (Scheme.Modules.tensorPullback j.left.left).mapIso (L.pullbackIso k) ≪≫
        L.pullbackIso j

/-- Restricting a cartesian family along a map of presheaves is its scheme-test pullback.
There are no choices of objects or morphisms in this construction.
Source: Stacks, Tag 0D2Z(3) (blueprint: def-trf-cartesian-line-presentation). -/
noncomputable def TestLineFamily.pullback {F G : (Over S)ᵒᵖ ⥤ Type u}
    (L : TestLineFamily F) (g : G ⟶ F) : TestLineFamily G where
  module W := L.module ((CostructuredArrow.map g).obj W)
  invertible W := L.invertible ((CostructuredArrow.map g).obj W)
  pullbackIso j := L.pullbackIso ((CostructuredArrow.map g).map j)

/-- A cartesian scheme-test presentation of the given small-etale line module.
The additive equivalences are linear over regular functions, and commute with every
small-etale restriction map. Thus the family is the pullback of `line`, not arbitrary
extra line modules on the test schemes.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
structure EtaleLinePresentation (X : AlgebraicSpace S) extends TestLineFamily X.obj.obj where
  coherent : toTestLineFamily.IsCoherent
  line : X.Modules
  isLine : X.IsLineModule line
  etaleSections (T : X.EtaleSite) : Γ(module T.obj, ⊤) ≃+ line.val.obj (op T)
  etaleSections_smul (T : X.EtaleSite) (r : Γ(T.obj.left.left, ⊤))
      (s : Γ(module T.obj, ⊤)) : etaleSections T (r • s) = r • etaleSections T s
  etaleSections_naturality {T U : X.EtaleSite} (j : T ⟶ U)
      (s : Γ(module U.obj, ⊤)) :
    etaleSections T (toTestLineFamily.sectionMap j.hom s) =
      line.val.map j.op (etaleSections U s)

/-- Cartesian isomorphisms of the actual pullback modules on scheme tests.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
structure TestLineIso {F : (Over S)ᵒᵖ ⥤ Type u} (P Q : TestLineFamily F) where
  app (W : SchemeTests F) : P.module W ≅ Q.module W
  naturality {W V : SchemeTests F} (j : W ⟶ V) :
    (P.pullbackIso j).hom ≫ (app W).hom =
      (Scheme.Modules.tensorPullback j.left.left).map (app V).hom ≫ (Q.pullbackIso j).hom

/-- Compatibility with the prescribed small-etale module, rather than only an abstract
isomorphism of the test families. `HEq` uses the fixed equality of the underlying line
modules when applying this predicate to two realizations of the same module.
Source: Stacks, Tags 03G7 and 0D2Z
(blueprint: def-trf-cartesian-line-presentation). -/
def TestLineIso.IsEtaleCompatible {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (e : TestLineIso P.toTestLineFamily Q.toTestLineFamily) : Prop :=
  ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
    HEq (Q.etaleSections T ((e.app T.obj).hom.app ⊤ s)) (P.etaleSections T s)

/-- Cartesian module morphisms between scheme-test families.
Source: Stacks, Properties of Spaces, Tag 03G7; Descent, Tag 023T
(blueprint: def-trf-cartesian-line-presentation). -/
structure TestLineHom {F : (Over S)ᵒᵖ ⥤ Type u} (P Q : TestLineFamily F) where
  app (W : SchemeTests F) : P.module W ⟶ Q.module W
  naturality {W V : SchemeTests F} (j : W ⟶ V) :
    (P.pullbackIso j).hom ≫ app W =
      (Scheme.Modules.tensorPullback j.left.left).map (app V) ≫ (Q.pullbackIso j).hom

/-- Equality of cartesian module morphisms is equality on every scheme test.
Source: Stacks, Tag 03G7 (blueprint: def-trf-cartesian-line-presentation). -/
@[ext] theorem TestLineHom.ext {F : (Over S)ᵒᵖ ⥤ Type u} {P Q : TestLineFamily F}
    {e f : TestLineHom P Q} (h : ∀ W, e.app W = f.app W) : e = f := by
  cases e
  cases f
  simp_all [mk.injEq, funext_iff]

/-- The identity cartesian module morphism.
Source: Stacks, Tag 03G7 (blueprint: def-trf-cartesian-line-presentation). -/
def TestLineHom.id {F : (Over S)ᵒᵖ ⥤ Type u} (P : TestLineFamily F) : TestLineHom P P where
  app W := 𝟙 (P.module W)
  naturality j := by simp

/-- Composition of cartesian module morphisms is composition on every test.
Source: Stacks, Tag 03G7 (blueprint: def-trf-cartesian-line-presentation). -/
def TestLineHom.comp {F : (Over S)ᵒᵖ ⥤ Type u} {P Q R : TestLineFamily F}
    (e : TestLineHom P Q) (f : TestLineHom Q R) : TestLineHom P R where
  app W := e.app W ≫ f.app W
  naturality j := by
    rw [← Category.assoc, e.naturality, Category.assoc, f.naturality,
      Functor.map_comp, Category.assoc]

/-- A cartesian module morphism induces the prescribed map of small-etale modules.
Source: Stacks, Tag 03G7 (blueprint: def-trf-cartesian-line-presentation). -/
def TestLineHom.IsEtaleCompatible {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (e : TestLineHom P.toTestLineFamily Q.toTestLineFamily) (f : P.line ⟶ Q.line) : Prop :=
  ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
    Q.etaleSections T ((e.app T.obj).app ⊤ s) =
      f.val.app (op T) (P.etaleSections T s)

/-- Compatibility with small-etale maps is preserved by composition.
Source: Stacks, Tag 03G7 (blueprint: def-trf-cartesian-line-presentation). -/
theorem TestLineHom.IsEtaleCompatible.comp {X : AlgebraicSpace S}
    {P Q R : EtaleLinePresentation X}
    {e : TestLineHom P.toTestLineFamily Q.toTestLineFamily}
    {f : TestLineHom Q.toTestLineFamily R.toTestLineFamily}
    {a : P.line ⟶ Q.line} {b : Q.line ⟶ R.line}
    (he : e.IsEtaleCompatible P Q a) (hf : f.IsEtaleCompatible Q R b) :
    (e.comp f).IsEtaleCompatible P R (a ≫ b) := by
  intro T s
  change R.etaleSections T ((f.app T.obj).app ⊤ ((e.app T.obj).app ⊤ s)) = _
  rw [hf, he]
  rfl

end AlgebraicGeometry.AlgebraicSpace
