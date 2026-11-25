/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import WeilConjectures.AlgebraicGeometry.TensorCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSinglePullbackComposition
import WeilConjectures.AlgebraicGeometry.TensorCoefficientPullbackComposition

/-! # Composition of tensor coefficient single-pullback comparisons
Source: Stacks Project, Tag 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option cleanup.letToHave false
universe v
open CategoryTheory
namespace AlgebraicGeometry
open Scheme.Modules
noncomputable section

-- The naturality calculation for three successive components is category algebra.
private theorem naturality_three {D : Type*} [Category D]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : D}
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (f₃ : A₃ ⟶ B₃)
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (a₂ : A₂ ⟶ A₃)
    (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂) (b₂ : B₂ ⟶ B₃)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (h₂ : f₂ ≫ b₂ = a₂ ≫ f₃) :
    f₀ ≫ (b₀ ≫ b₁ ≫ b₂) = (a₀ ≫ a₁ ≫ a₂) ≫ f₃ := by
  calc
    _ = (f₀ ≫ b₀) ≫ b₁ ≫ b₂ := by simp only [Category.assoc]
    _ = (a₀ ≫ f₁) ≫ b₁ ≫ b₂ := congrArg (fun x ↦ x ≫ b₁ ≫ b₂) h₀
    _ = a₀ ≫ (f₁ ≫ b₁) ≫ b₂ := by simp only [Category.assoc]
    _ = a₀ ≫ (a₁ ≫ f₂) ≫ b₂ := congrArg (fun x ↦ a₀ ≫ x ≫ b₂) h₁
    _ = a₀ ≫ a₁ ≫ (f₂ ≫ b₂) := by simp only [Category.assoc]
    _ = a₀ ≫ a₁ ≫ (a₂ ≫ f₃) := congrArg (fun x ↦ a₀ ≫ a₁ ≫ x) h₂
    _ = _ := by simp only [Category.assoc]

-- Prove reassociation once in an abstract category, without unfolding sheaf functors.
private theorem paste_maps {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : D}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)
    (j : X₁ ⟶ X₅) (k : X₅ ⟶ X₃) (u : X₅ ⟶ X₆) (v : X₆ ⟶ X₄)
    (m : X₀ ⟶ X₇) (n : X₇ ⟶ X₆)
    (hn : g ≫ h = j ≫ k) (hd : k ≫ i = u ≫ v)
    (hc : m ≫ n = f ≫ j ≫ u) :
    (f ≫ g) ≫ h ≫ i = m ≫ n ≫ v := by
  calc
    _ = f ≫ (g ≫ h) ≫ i := by simp only [Category.assoc]
    _ = f ≫ (j ≫ k) ≫ i := congrArg (fun x ↦ f ≫ x ≫ i) hn
    _ = f ≫ j ≫ (k ≫ i) := by simp only [Category.assoc]
    _ = f ≫ j ≫ (u ≫ v) := congrArg (fun x ↦ f ≫ j ≫ x) hd
    _ = (f ≫ j ≫ u) ≫ v := by simp only [Category.assoc]
    _ = (m ≫ n) ≫ v := congrArg (fun x ↦ x ≫ v) hc.symm
    _ = _ := Category.assoc _ _ _

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The single-complex coefficient morphism of a commuting triangle.
It uses the fixed ordinary-to-tensor identification, without inverting the
single-pullback map. Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-single-coefficient-map) -/
@[irreducible]
def tensorSingleCoefficientMap {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    (derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback q).obj L)) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback q1).obj L) :=
  Scheme.Modules.canonicalSinglePullbackMap a ((Scheme.Modules.tensorPullback q).obj L) ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
        (Scheme.Modules.tensorCoefficientComparison q q1 a h L).hom

/-- Defining equation of the single-complex coefficient morphism.
Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-single-coefficient-map) -/
theorem tensorSingleCoefficientMap_eq {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    tensorSingleCoefficientMap q q1 a h L =
      Scheme.Modules.canonicalSinglePullbackMap a ((Scheme.Modules.tensorPullback q).obj L) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
            (Scheme.Modules.tensorCoefficientComparison q q1 a h L).hom := by
  delta tensorSingleCoefficientMap
  rfl

attribute [local irreducible] Scheme.Modules.tensorPullback

-- The single embeddings use both the scheme and ringed-space module categories.
private theorem single_naturality {A B : Scheme.{v}} (a : B ⟶ A)
    {M N : A.Modules} (f : M ⟶ N) :
    (derivedPullback a).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).map f) ≫
        Scheme.Modules.canonicalSinglePullbackMap a N =
      Scheme.Modules.canonicalSinglePullbackMap a M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map
            ((Scheme.Modules.pullback a).map f) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive a
  let ε := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{v, v + 1})) a
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction a)
  let Q := DerivedCategory.Qh.{v + 1}
    (C := SheafOfModules.{v} (moduleRings B.toRingedSpace))
  let H := HomotopyCategory.quotient
    (SheafOfModules.{v} (moduleRings B.toRingedSpace)) (ComplexShape.up ℤ)
  let s := HomologicalComplex.singleMapHomologicalComplex
    (W₁ := SheafOfModules.{v} (moduleRings A.toRingedSpace))
    (W₂ := SheafOfModules.{v} (moduleRings B.toRingedSpace))
    (Scheme.Modules.tensorPullback a) (ComplexShape.up ℤ) 0
  let SA := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0
  let SB := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0
  let HA := HomotopyCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0
  let T := (Scheme.Modules.tensorPullback a).mapHomotopyCategory (ComplexShape.up ℤ)
  have he := ε.naturality (HA.map f)
  change (derivedPullback a).map (SA.map f) ≫ ε.app (HA.obj N) =
    ε.app (HA.obj M) ≫ Q.map (T.map (HA.map f)) at he
  have hs := congrArg (fun k ↦ Q.map (H.map k)) (s.hom.naturality f)
  simp only [Functor.map_comp, Functor.comp_map] at hs
  change Q.map (T.map (HA.map f)) ≫ Q.map (H.map (s.hom.app N)) =
    Q.map (H.map (s.hom.app M)) ≫ SB.map ((Scheme.Modules.tensorPullback a).map f) at hs
  have ht := congrArg (fun k ↦ SB.map k) (t.hom.naturality f)
  simp only [Functor.map_comp] at ht
  simpa only [canonicalSinglePullbackMap, cast_eq, Category.assoc,
    ε, t, Q, H, s, SA, SB, HA, T, Scheme.Modules, Scheme.ringCatSheaf,
    moduleRings] using naturality_three
    ((derivedPullback a).map (SA.map f)) (Q.map (T.map (HA.map f)))
    (SB.map ((Scheme.Modules.tensorPullback a).map f))
    (SB.map ((Scheme.Modules.pullback a).map f))
    (ε.app (HA.obj M)) (Q.map (H.map (s.hom.app M))) (SB.map (t.hom.app M))
    (ε.app (HA.obj N)) (Q.map (H.map (s.hom.app N))) (SB.map (t.hom.app N)) he hs ht

attribute [local irreducible] canonicalSinglePullbackMap

private theorem derived_glue {A B C : Scheme.{v}} (a : B ⟶ A) (b : C ⟶ B)
    (M : A.Modules) (N : B.Modules) (P : C.Modules)
    (d1 : (Scheme.Modules.pullback a).obj M ⟶ N)
    (d2 : (Scheme.Modules.pullback b).obj N ⟶ P)
    (d3 : (Scheme.Modules.pullback (b ≫ a)).obj M ⟶ P)
    (hd : (Scheme.Modules.pullback b).map d1 ≫ d2 =
      (Scheme.Modules.pullbackComp b a).hom.app M ≫ d3) :
    (derivedPullback b).map (Scheme.Modules.canonicalSinglePullbackMap a M ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map d1) ≫
      Scheme.Modules.canonicalSinglePullbackMap b N ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0).map d2 =
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) b a).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj M) ≫
      Scheme.Modules.canonicalSinglePullbackMap (b ≫ a) M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0).map d3 := by
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0
  have hn := single_naturality b d1
  have hc := Scheme.Modules.canonicalSinglePullbackComposition b a M
  have hd' := congrArg (fun k ↦ S.map k) hd
  simp only [Functor.map_comp] at hd'
  simpa only [Functor.map_comp] using paste_maps
    ((derivedPullback b).map (Scheme.Modules.canonicalSinglePullbackMap a M))
    ((derivedPullback b).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map d1))
    (Scheme.Modules.canonicalSinglePullbackMap b N) (S.map d2)
    (Scheme.Modules.canonicalSinglePullbackMap b ((Scheme.Modules.pullback a).obj M))
    (S.map ((Scheme.Modules.pullback b).map d1))
    (S.map ((Scheme.Modules.pullbackComp b a).hom.app M)) (S.map d3)
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) b a).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj M))
    (Scheme.Modules.canonicalSinglePullbackMap (b ≫ a) M) hn hd' hc

/-- Coefficient comparisons compose, before any direct image or base-change mate.
Source: Stacks Project, Tag 0D5S; step 3 of
lem-sc-picard-coefficient-transpose-pasting.
(blueprint: lem-sc-tensor-single-pullback-composition)

Proof: Apply canonicalSinglePullbackComposition to b,a and the module
q tensor-pullback L. Naturality of the single-pullback comparison moves the
single embedding of d1 through the b comparison. The remaining underived
identity says pullbackComp(b,a), transport along hab, and d3 equal the
pullback of d1 followed by d2. Transpose that identity under the composed
ordinary pullback adjunctions and the selected tensor adjunctions. The
leftAdjointUniq counit identities cancel the ordinary-to-tensor comparisons.
The definition of each c as the conjugate of pushforwardComp then reduces
the equality to associativity of pushforward composition, with transports
along h1,h2,h3. These transports agree by hab and proof irrelevance.
Injectivity of the adjunction equivalences proves the underived identity;
map it by the single functor and substitute in the derived composition
formula. No single comparison is inverted. Thus zero modules, identity
morphisms and empty schemes require no special hypotheses. -/
theorem tensorSinglePullback_composition
    {A B C X : Scheme.{v}} (q : A ⟶ X) (q1 : B ⟶ X) (q2 : C ⟶ X)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (h1 : a ≫ q = q1) (h2 : b ≫ q1 = q2) (h3 : a' ≫ q = q2)
    (hab : b ≫ a = a') (L : X.Modules) :
  let d1 := Scheme.Modules.tensorCoefficientComparison q q1 a h1 L
  let d2 := Scheme.Modules.tensorCoefficientComparison q1 q2 b h2 L
  let d3 := Scheme.Modules.tensorCoefficientComparison q q2 a' h3 L
  let M := (Scheme.Modules.tensorPullback q).obj L
  let N := (Scheme.Modules.tensorPullback q1).obj L
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj M
  (derivedPullback b).map (Scheme.Modules.canonicalSinglePullbackMap a M ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings B.toRingedSpace)) 0).map d1.hom) ≫
    Scheme.Modules.canonicalSinglePullbackMap b N ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0).map d2.hom =
  (canonicalDerivedPullbackComposition b a ≪≫
    eqToIso (congrArg (fun r ↦ derivedPullback r) hab)).hom.app K ≫
      (Scheme.Modules.canonicalSinglePullbackMap a' M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings C.toRingedSpace)) 0).map d3.hom) := by
  subst a'
  dsimp only
  have hd := Scheme.Modules.tensorCoefficientPullback_composition
    q q1 q2 a b (b ≫ a) h1 h2 h3 rfl L
  have hd' : (Scheme.Modules.pullback b).map
      (Scheme.Modules.tensorCoefficientComparison q q1 a h1 L).hom ≫
      (Scheme.Modules.tensorCoefficientComparison q1 q2 b h2 L).hom =
    (Scheme.Modules.pullbackComp b a).hom.app ((Scheme.Modules.tensorPullback q).obj L) ≫
      (Scheme.Modules.tensorCoefficientComparison q q2 (b ≫ a) h3 L).hom := by
    simpa only [eqToIso_refl, Iso.trans_refl] using hd
  simpa only [canonicalDerivedPullbackComposition, eqToIso_refl, Iso.trans_refl,
    Category.assoc] using derived_glue a b ((Scheme.Modules.tensorPullback q).obj L)
      ((Scheme.Modules.tensorPullback q1).obj L) ((Scheme.Modules.tensorPullback q2).obj L)
      (Scheme.Modules.tensorCoefficientComparison q q1 a h1 L).hom
      (Scheme.Modules.tensorCoefficientComparison q1 q2 b h2 L).hom
      (Scheme.Modules.tensorCoefficientComparison q q2 (b ≫ a) h3 L).hom hd'

/-- Composition API for the fixed single-complex coefficient morphisms.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-sc-tensor-single-pullback-composition)
Proof: unfold only the coefficient-morphism wrapper and apply the recorded
coefficient composition theorem. The generic schemes stay as parameters. -/
theorem tensorSingleCoefficientMap_composition
    {A B C X : Scheme.{v}} (q : A ⟶ X) (q1 : B ⟶ X) (q2 : C ⟶ X)
    (a : B ⟶ A) (b : C ⟶ B) (a' : C ⟶ A)
    (h1 : a ≫ q = q1) (h2 : b ≫ q1 = q2) (h3 : a' ≫ q = q2)
    (hab : b ≫ a = a') (L : X.Modules) :
    (derivedPullback b).map (tensorSingleCoefficientMap q q1 a h1 L) ≫
      tensorSingleCoefficientMap q1 q2 b h2 L =
    (canonicalDerivedPullbackComposition b a ≪≫
      eqToIso (congrArg (fun r ↦ derivedPullback r) hab)).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings A.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback q).obj L)) ≫
      tensorSingleCoefficientMap q q2 a' h3 L := by
  delta tensorSingleCoefficientMap
  exact tensorSinglePullback_composition q q1 q2 a b a' h1 h2 h3 hab L

end
end AlgebraicGeometry
