import Langlands.AlgebraicGeometry.ConnectedCoproductFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # The equivalence relation of a finite free action on a scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry

/-- A scheme action, written in the order of composition of morphisms, that is
free on points valued in every nonempty scheme. Finiteness of the group is imposed
on the constructions that require it. -/
structure FiniteFreeSchemeAction (G : Type u) [Group G] (X : Scheme.{u}) where
  act : G → (X ≅ X)
  one : (act 1).hom = 𝟙 X
  mul : ∀ g h, (act g).hom ≫ (act h).hom = (act (g * h)).hom
  free : ∀ {T : Scheme.{u}} [Nonempty T] (a : T ⟶ X),
    Function.Injective (fun g => a ≫ (act g).hom)

namespace FiniteFreeSchemeAction

variable {G : Type u} [Group G] {X : Scheme.{u}} (A : FiniteFreeSchemeAction G X)

/-- The disjoint union of the graphs of the action. -/
def relationScheme (_A : FiniteFreeSchemeAction G X) : Scheme.{u} := ∐ fun _ : G => X

def source : A.relationScheme ⟶ X := Sigma.desc fun _ => 𝟙 X

def target : A.relationScheme ⟶ X := Sigma.desc fun g => (A.act g).hom

@[reassoc (attr := simp)] lemma ι_source (g : G) :
    Sigma.ι (fun _ : G => X) g ≫ A.source = 𝟙 X :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)] lemma ι_target (g : G) :
    Sigma.ι (fun _ : G => X) g ≫ A.target = (A.act g).hom :=
  Sigma.ι_comp_desc _ _

instance : Etale A.source :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) fun _ => inferInstance

instance : Etale A.target :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) fun _ => inferInstance

theorem reflexive (T : Scheme.{u}) (a : T ⟶ X) :
    ∃ r : T ⟶ A.relationScheme, r ≫ A.target = a ∧ r ≫ A.source = a := by
  refine ⟨a ≫ Sigma.ι (fun _ : G => X) 1, ?_, ?_⟩ <;> simp [A.one]

/-- Reversal of an action arrow. -/
def reverse : A.relationScheme ⟶ A.relationScheme :=
  Sigma.desc fun g => (A.act g).hom ≫ Sigma.ι (fun _ : G => X) g⁻¹

@[reassoc (attr := simp)] lemma reverse_target :
    A.reverse ≫ A.target = A.source := by
  apply Sigma.hom_ext
  intro g
  simp [reverse, A.mul, A.one]

@[reassoc (attr := simp)] lemma reverse_source :
    A.reverse ≫ A.source = A.target := by
  apply Sigma.hom_ext
  intro g
  simp [reverse]

theorem symmetric (T : Scheme.{u}) (r : T ⟶ A.relationScheme) :
    ∃ r' : T ⟶ A.relationScheme,
      r' ≫ A.target = r ≫ A.source ∧ r' ≫ A.source = r ≫ A.target := by
  exact ⟨r ≫ A.reverse, by simp, by simp⟩

section Finite

variable [Finite G]

/-- The coproduct presentation of a pair of composable action arrows. -/
def composableScheme : Scheme.{u} :=
  ∐ fun p : G × G => pullback (𝟙 X) (A.act p.2).hom

def composableLeft : A.composableScheme ⟶ A.relationScheme :=
  Sigma.desc fun p => pullback.fst (𝟙 X) (A.act p.2).hom ≫ Sigma.ι (fun _ : G => X) p.1

def composableRight : A.composableScheme ⟶ A.relationScheme :=
  Sigma.desc fun p => pullback.snd (𝟙 X) (A.act p.2).hom ≫ Sigma.ι (fun _ : G => X) p.2

theorem composable_isPullback :
    IsPullback A.composableLeft A.composableRight A.source A.target :=
  FinitaryPreExtensive.isPullback_sigmaDesc
    (fun _ : G => 𝟙 X) (fun g => (A.act g).hom)

/-- Composition on each actual component, then on the disjoint union. -/
def compose : A.composableScheme ⟶ A.relationScheme :=
  Sigma.desc fun p => pullback.snd (𝟙 X) (A.act p.2).hom ≫ Sigma.ι (fun _ : G => X) (p.2 * p.1)

omit [Finite G] in
@[reassoc (attr := simp)] theorem compose_target :
    A.compose ≫ A.target = A.composableLeft ≫ A.target := by
  apply Sigma.hom_ext
  intro p
  simp only [compose, composableLeft, Sigma.ι_comp_desc_assoc, ι_target,
    Category.assoc]
  rw [← A.mul]
  rw [← Category.assoc, ← pullback.condition]
  simp

omit [Finite G] in
@[reassoc (attr := simp)] theorem compose_source :
    A.compose ≫ A.source = A.composableRight ≫ A.source := by
  apply Sigma.hom_ext
  intro p
  simp [compose, composableRight]

theorem transitive (T : Scheme.{u}) (r r' : T ⟶ A.relationScheme)
    (h : r ≫ A.source = r' ≫ A.target) :
    ∃ r'' : T ⟶ A.relationScheme,
      r'' ≫ A.target = r ≫ A.target ∧ r'' ≫ A.source = r' ≫ A.source := by
  let l := A.composable_isPullback.lift r r' h
  refine ⟨l ≫ A.compose, ?_, ?_⟩
  · rw [Category.assoc, A.compose_target, ← Category.assoc]
    rw [A.composable_isPullback.lift_fst]
  · rw [Category.assoc, A.compose_source, ← Category.assoc]
    rw [A.composable_isPullback.lift_snd]

end Finite

section Monicity

variable [X.IsSeparated]

instance graph_isClosedImmersion (g : G) :
    IsClosedImmersion (prod.lift (A.act g).hom (𝟙 X)) := by
  have h : prod.lift (A.act g).hom (𝟙 X) =
      prod.lift (𝟙 X) (𝟙 X) ≫ prod.map (A.act g).hom (𝟙 X) := by
    apply prod.hom_ext <;> simp
  rw [h]
  infer_instance

instance relation_surjectiveOnStalks :
    SurjectiveOnStalks (prod.lift A.target A.source) := by
  have h : prod.lift A.target A.source =
      Sigma.desc (fun g => prod.lift (A.act g).hom (𝟙 X)) := by
    apply Sigma.hom_ext
    intro g
    apply prod.hom_ext <;> simp
  rw [h]
  exact IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks.{u}) fun g => inferInstance

omit [X.IsSeparated] in
theorem fieldPoint_injective (K : Type u) [Field K] :
    Function.Injective (fun r : Spec (.of K) ⟶ A.relationScheme =>
      r ≫ prod.lift A.target A.source) := by
  intro r r' h
  obtain ⟨g, a, rfl⟩ := connectedHom_factor_coproduct (fun _ : G => X) r
  obtain ⟨g', a', rfl⟩ := connectedHom_factor_coproduct (fun _ : G => X) r'
  have hs := congrArg (fun f => f ≫ prod.snd) h
  have ht := congrArg (fun f => f ≫ prod.fst) h
  simp only [Category.assoc, prod.lift_snd, ι_source, Category.comp_id] at hs
  subst a'
  have hg : g = g' := A.free a (by simpa using ht)
  subst g'
  rfl

omit [X.IsSeparated] in
instance relation_universallyInjective :
    UniversallyInjective (prod.lift A.target A.source) :=
  ((tfae_universallyInjective (prod.lift A.target A.source)).out 2 1).mp A.fieldPoint_injective

instance relation_mono : Mono (prod.lift A.target A.source) :=
  SurjectiveOnStalks.mono_of_injective (Scheme.Hom.injective _)

end Monicity

end FiniteFreeSchemeAction
end Langlands.AlgebraicGeometry
