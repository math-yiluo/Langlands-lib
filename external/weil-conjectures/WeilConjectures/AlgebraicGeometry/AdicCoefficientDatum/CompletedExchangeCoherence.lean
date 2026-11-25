/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeUnit
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-!
# Naturality, units, and pasting of completed exchange

Source: blueprint proper base change, completed exchange coherence, order 1348
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
The comparison maps below retain ordinary tensor-unit normalization. They do not
replace canonical completed pullback compositions by arbitrary natural isomorphisms.

## Main statements

- `AdicCoefficientDatum.completedExchange_naturality`: naturality for arbitrary maps.
- `AdicCoefficientDatum.completedExchange_identity_horizontal`: horizontal identities.
- `AdicCoefficientDatum.completedExchange_identity_vertical`: vertical identities.
- `AdicCoefficientDatum.completedExchange_horizontal`: horizontal pasting.
- `AdicCoefficientDatum.completedExchange_vertical`: vertical pasting.

## Main definitions

- `AdicCoefficientDatum.completedPullComp`: the unit-normalized composition comparison.
- `AdicCoefficientDatum.completedPullId`: the unit-normalized identity comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [local irreducible] AdicCoefficientDatum.pullComp AdicCoefficientDatum.pushComp

-- Comparing derived functor presentations requires unfolding their factor isomorphisms.
private def ordinaryToCompletedFormula {U V : Scheme.{t}} (u : U ⟶ V) :
    d.pull u ⟶ d.completedPull u :=
  Functor.whiskerLeft (d.pull u) (d.constantRlimAdjunction U).unit ≫
    Functor.whiskerRight (d.derivedConstantPullbackIso u).inv
      (completedRlim U (d.completedRing U)) ≫
    Functor.whiskerRight
      (Functor.whiskerRight (completedReductionAugmentation d V) (d.towerPull u))
      (completedRlim U (d.completedRing U))

private theorem ordinaryToCompleted_naturality {U V : Scheme.{t}} (u : U ⟶ V)
    {K L : d.derived V} (a : K ⟶ L) :
    (d.pull u).map a ≫ d.ordinaryToCompleted u L =
      d.ordinaryToCompleted u K ≫ (d.completedPull u).map a := by
  simpa only [ordinaryToCompletedFormula, AdicCoefficientDatum.ordinaryToCompleted,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc] using (ordinaryToCompletedFormula d u).naturality a

private def ordinaryToCompletedNat {U V : Scheme.{t}} (u : U ⟶ V) :
    d.pull u ⟶ d.completedPull u where
  app K := d.ordinaryToCompleted u K
  naturality := by
    intro K L a
    exact ordinaryToCompleted_naturality d u a

private theorem adjunction_precomp_bijective
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {X Y : C} (j : X ⟶ Y) (N : D)
    (hj : Function.Bijective (fun a : Y ⟶ G.obj N ↦ j ≫ a)) :
    Function.Bijective (fun a : F.obj Y ⟶ N ↦ F.map j ≫ a) := by
  let E := (adj.homEquiv Y N).trans
    ((Equiv.ofBijective _ hj).trans (adj.homEquiv X N).symm)
  have he (a : F.obj Y ⟶ N) : E a = F.map j ≫ a := by
    change (adj.homEquiv X N).symm (j ≫ adj.homEquiv Y N a) = _
    simpa using adj.homEquiv_naturality_left_symm j (adj.homEquiv Y N a)
  have h : (fun a : F.obj Y ⟶ N ↦ F.map j ≫ a) = E := funext fun a ↦ (he a).symm
  rw [h]
  exact E.bijective

private theorem iso_precomp_bijective {C : Type*} [Category C]
    {X Y : C} (e : X ≅ Y) (N : C) :
    Function.Bijective (fun a : Y ⟶ N ↦ e.hom ≫ a) := by
  constructor
  · intro a b hab
    exact (cancel_epi e.hom).1 hab
  · intro a
    exact ⟨e.inv ≫ a, by simp⟩

private theorem unit_normalized_iso
    {C D : Type*} [Category C] [Category D] (P F G : C ⥤ D)
    (j : P ⟶ F) (q : P ⟶ G) (S : D → Prop)
    (hF : ∀ K, S (F.obj K)) (hG : ∀ K, S (G.obj K))
    (hj : ∀ K N, S N → Function.Bijective (fun a : F.obj K ⟶ N ↦ j.app K ≫ a))
    (hq : ∀ K N, S N → Function.Bijective (fun a : G.obj K ⟶ N ↦ q.app K ≫ a)) :
    ∃! α : F ≅ G, ∀ K, j.app K ≫ α.hom.app K = q.app K := by
  let E (K : C) := Equiv.ofBijective _ (hj K _ (hG K))
  let e (K : C) := (E K).symm (q.app K)
  have he (K : C) : j.app K ≫ e K = q.app K := (E K).apply_symm_apply _
  let B (K : C) := Equiv.ofBijective _ (hq K _ (hF K))
  let b (K : C) := (B K).symm (j.app K)
  have hb (K : C) : q.app K ≫ b K = j.app K := (B K).apply_symm_apply _
  let α (K : C) : F.obj K ≅ G.obj K :=
    { hom := e K
      inv := b K
      hom_inv_id := by
        apply (hj K _ (hF K)).1
        dsimp only
        rw [← Category.assoc, he, hb, Category.comp_id]
      inv_hom_id := by
        apply (hq K _ (hG K)).1
        dsimp only
        rw [← Category.assoc, hb, he, Category.comp_id] }
  have hn {K L : C} (a : K ⟶ L) : F.map a ≫ (α L).hom = (α K).hom ≫ G.map a := by
    apply (hj K _ (hG L)).1
    change j.app K ≫ F.map a ≫ e L = j.app K ≫ e K ≫ G.map a
    rw [← j.naturality_assoc a, he, ← Category.assoc, he, q.naturality]
  refine ⟨NatIso.ofComponents α (fun a ↦ hn a), he, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (hj K _ (hG K)).1
  exact (hβ K).trans (he K).symm

private theorem compositeUnit_bijective {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) (K : d.derived W) (N : d.derived U)
    (hN : d.TowerComplete U N) :
    Function.Bijective (fun a : (d.completedPull h).obj ((d.completedPull g).obj K) ⟶ N ↦
      (d.pullComp h g).hom.app K ≫ (d.pull h).map (d.ordinaryToCompleted g K) ≫
        d.ordinaryToCompleted h ((d.completedPull g).obj K) ≫ a) := by
  have h₁ := (d.completedPull_reflection h).2 ((d.completedPull g).obj K) N hN
  have h₂ := adjunction_precomp_bijective
    (proEtaleRingDerivedAdjunction h (d.completedRing V) (d.completedRing U)
      (d.integralRingIso h)) (d.ordinaryToCompleted g K) N
    ((d.completedPull_reflection g).2 K ((d.push h).obj N) (d.push_complete h N hN))
  have h₃ := iso_precomp_bijective ((d.pullComp h g).app K) N
  exact h₃.comp (h₂.comp h₁)

/-- Completed composition is uniquely fixed by its ordinary completion-unit equation.
Source: blueprint coherence, canonical associativity and proof step 5; Stacks Tag 099N (5)
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: under constant-to-completed restriction, completed pullback is ordinary pullback
followed by the derived completion reflector. Pullback of quotient reductions is the
strict tensor balancing map. The two successive completion units therefore factor
uniquely through the completion of the composite pullback. On strict K-flat quotient
models the inverse comparison is tensor reassociation, sending (x tensor b) tensor a
to x tensor q(b)a. The quotient cocycle and unit identities make both composites
identities. The reflector universal property proves uniqueness of the displayed natural
iso, so no choice of arbitrary comparison is permitted. -/
theorem AdicCoefficientDatum.completedPullComp_existsUnique {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    ∃! α : d.completedPull (h ≫ g) ≅ d.completedPull g ⋙ d.completedPull h,
      ∀ K : d.derived W,
        d.ordinaryToCompleted (h ≫ g) K ≫ α.hom.app K =
          (d.pullComp h g).hom.app K ≫
            (d.pull h).map (d.ordinaryToCompleted g K) ≫
              d.ordinaryToCompleted h ((d.completedPull g).obj K) := by
  let q : d.pull (h ≫ g) ⟶ d.completedPull g ⋙ d.completedPull h :=
    { app K := (d.pullComp h g).hom.app K ≫
        (d.pull h).map (d.ordinaryToCompleted g K) ≫
          d.ordinaryToCompleted h ((d.completedPull g).obj K)
      naturality := by
        intro K L a
        have hn := ((d.pullComp h g).hom ≫
          Functor.whiskerRight (ordinaryToCompletedNat d g) (d.pull h) ≫
          Functor.whiskerLeft (d.completedPull g) (ordinaryToCompletedNat d h)).naturality a
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.whiskerLeft_app, ordinaryToCompletedNat, Category.assoc] using hn }
  have hq : ∀ K N, d.TowerComplete U N → Function.Bijective
      (fun a : (d.completedPull g ⋙ d.completedPull h).obj K ⟶ N ↦ q.app K ≫ a) := by
    intro K N hN
    have H := compositeUnit_bijective d h g K N hN
    convert H using 1
    funext a
    simp only [q, Category.assoc]
  exact unit_normalized_iso (d.pull (h ≫ g)) _ _
    (ordinaryToCompletedNat d (h ≫ g)) q (d.TowerComplete U)
    ((d.completedPull_reflection (h ≫ g)).1)
    (fun K ↦ (d.completedPull_reflection h).1 ((d.completedPull g).obj K))
    (fun K N hN ↦ by
      simpa only [ordinaryToCompletedNat] using
        (d.completedPull_reflection (h ≫ g)).2 K N hN) hq

/-- The canonical completed pullback composition, fixed by its completion units.
Source: blueprint coherence, canonical associativity
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.completedPullComp {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    d.completedPull (h ≫ g) ≅ d.completedPull g ⋙ d.completedPull h :=
  (d.completedPullComp_existsUnique h g).choose

/-- On complete inputs the identity completed pullback has its unique unit-normalized
identity comparison. Source: blueprint coherence, proof steps 5 and 6
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
Proof: constant tower identity and its derived mate identify the displayed comparison
with the canonical completion unit. Completeness makes it invertible. Compose its
inverse with ordinary pullback identity; invertibility forces the asserted uniqueness. -/
theorem AdicCoefficientDatum.completedPullId_existsUnique (T : Scheme.{t})
    (K : d.derived T) (hK : d.TowerComplete T K) :
    ∃! α : (d.completedPull (𝟙 T)).obj K ≅ K,
      d.ordinaryToCompleted (𝟙 T) K ≫ α.hom = (d.pullId T).hom.app K := by
  let R := OrderedExchange.res d T
  have : R.ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction (𝟙 T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeConstantRing T A) (d.completedRing T)
      (exchangeScalar d T) (exchangeScalar d T) (exchangeConstantIso (𝟙 T) A)
      (d.integralRingIso (𝟙 T)) (exchangeScalar_comm d (𝟙 T))).1
  have hc : OrderedExchange.IsComplete d T (R.obj K) :=
    ((OrderedExchange.restriction_complete d T).1 K).1 hK
  let e := ((OrderedExchange.alpha d (𝟙 T)).symm.app K) ≪≫
    R.mapIso ((d.pullId T).app K)
  have hu : IsIso ((OrderedExchange.unit d T).app
      ((OrderedExchange.pull (A := A) (𝟙 T)).obj (R.obj K))) := by
    have : IsIso ((OrderedExchange.unit d T).app (R.obj K)) := hc
    have hn := (OrderedExchange.unit d T).naturality e.hom
    change e.hom ≫ (OrderedExchange.unit d T).app (R.obj K) =
      (OrderedExchange.unit d T).app
        ((OrderedExchange.pull (A := A) (𝟙 T)).obj (R.obj K)) ≫
          (OrderedExchange.completion d T).map e.hom at hn
    have hi : IsIso ((OrderedExchange.unit d T).app
        ((OrderedExchange.pull (A := A) (𝟙 T)).obj (R.obj K)) ≫
        (OrderedExchange.completion d T).map e.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((OrderedExchange.completion d T).map e.hom)
  have hp := (OrderedExchange.phi_existsUnique d (𝟙 T)).exists.choose_spec
    (⟨K, hK⟩ : OrderedExchange.AComplete d T)
  have : IsIso (R.map (d.ordinaryToCompleted (𝟙 T) K) ≫
      (OrderedExchange.phi d (𝟙 T)).hom.app ⟨K, hK⟩) := by
    change IsIso ((OrderedExchange.res d T).map _ ≫ _)
    rw [show (OrderedExchange.phi d (𝟙 T)).hom =
      (OrderedExchange.phi_existsUnique d (𝟙 T)).exists.choose.hom from rfl, hp]
    infer_instance
  have : IsIso (R.map (d.ordinaryToCompleted (𝟙 T) K)) :=
    IsIso.of_isIso_comp_right _ ((OrderedExchange.phi d (𝟙 T)).hom.app ⟨K, hK⟩)
  have : IsIso (d.ordinaryToCompleted (𝟙 T) K) := isIso_of_reflects_iso _ R
  refine ⟨(asIso (d.ordinaryToCompleted (𝟙 T) K)).symm ≪≫
    (d.pullId T).app K, ?_, ?_⟩
  · simp
  · intro β hβ
    apply Iso.ext
    apply (cancel_epi (d.ordinaryToCompleted (𝟙 T) K)).1
    simpa using hβ

/-- The completed identity comparison on a complete object, retaining its unit.
Source: blueprint coherence, identity-square clause
(blueprint: lemma-weil-pbc-completed-exchange-coherence). -/
def AdicCoefficientDatum.completedPullId (T : Scheme.{t})
    (K : d.derived T) (hK : d.TowerComplete T K) :
    (d.completedPull (𝟙 T)).obj K ≅ K :=
  (d.completedPullId_existsUnique T K hK).choose

end AlgebraicGeometry.Scheme
