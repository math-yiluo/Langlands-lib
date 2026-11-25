/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of the two operations, without their laws

Source: blueprint proposition-jacobian-over-ground-field--1, multiplication and unit step;
Stacks Project, Descent, Tag 02W0.
(blueprint: lem-pd-raw-monoid-operations-descent).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

private noncomputable def projectPoint
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    {T : Scheme.{u}} (f : T ⟶ X) (a : Over.mk f ⟶ V) : Over.mk (f ≫ p) ⟶ V₀ :=
  (Over.map p).map a ≫ Over.homMk qV hqV.w

private noncomputable def localPoint
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (A : Over Y) (a : A ⟶ V₀) : Over.mk (pullback.snd A.hom p) ⟶ V :=
  Over.homMk (hqV.lift (pullback.fst A.hom p ≫ a.left) (pullback.snd A.hom p)
    (by rw [Category.assoc, Over.w a, pullback.condition]))
    (hqV.lift_snd _ _ _)

private theorem localPoint_projection
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (A : Over Y) (a : A ⟶ V₀) :
    (localPoint qV hqV A a).left ≫ qV = pullback.fst A.hom p ≫ a.left :=
  hqV.lift_fst _ _ _

private theorem transport_eq_of_projection
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y}
    (D : Over.DescentDatum p V)
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V), (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) (b : Over.mk f₂ ⟶ V) (hab : a.left ≫ qV = b.left ≫ qV) :
    D.transport f₁ f₂ h a = b := by
  apply Over.OverMorphism.ext
  apply hqV.hom_ext
  · exact (hDV f₁ f₂ h a).trans hab
  · exact (Over.w _).trans (Over.w b).symm

private theorem descend_local_morphism
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    {V : Over X} {V₀ : Over Y} (qV : V.left ⟶ V₀.left)
    (hqV : IsPullback qV V.hom V₀.hom p) (A : Over Y)
    (d : Over.mk (pullback.snd A.hom p) ⟶ V)
    (hd : ∀ {T : Scheme.{u}} (g₁ g₂ : T ⟶ Limits.pullback A.hom p),
      g₁ ≫ pullback.fst A.hom p = g₂ ≫ pullback.fst A.hom p →
      g₁ ≫ d.left ≫ qV = g₂ ≫ d.left ≫ qV) :
    ∃ k : A ⟶ V₀, pullback.fst A.hom p ≫ k.left = d.left ≫ qV := by
  let k := EffectiveEpi.desc (pullback.fst A.hom p) (d.left ≫ qV) hd
  have hk : pullback.fst A.hom p ≫ k = d.left ≫ qV := EffectiveEpi.fac _ _ _
  have hw : k ≫ V₀.hom = A.hom := by
    apply (cancel_epi (pullback.fst A.hom p)).mp
    rw [← Category.assoc, hk, Category.assoc, hqV.w, ← Category.assoc,
      Over.w d, pullback.condition]
    rfl
  exact ⟨Over.homMk k hw, hk⟩

/-- The invariant multiplication and unit descend as morphisms. This assertion includes
no associativity, unit law, or commutativity downstairs.
Source: blueprint proposition-jacobian-over-ground-field--1, multiplication and unit step;
Stacks Project, Descent, Tag 02W0.
(blueprint: lem-pd-raw-monoid-operations-descent).

Proof: Pull back the scheme V₀ times_Y V₀ along p. Its two projections lift uniquely to V
by the cartesian square hqV. Multiply these two lifted points and compose with qV.
For two maps into this pullback with equal projections downstairs, hDV and the
cartesian square identify their lifted points by D.transport. The equation hμ then
says that the two products have equal images under qV. The pullback projection is fpqc,
hence an effective epimorphism (representable fpqc descent, Tag 02W0); its universal
property gives a unique morphism m to V₀. Its factorization equation gives the
displayed multiplication identity: a pair
of V-points over T lifts to this product cover, and the cartesian square identifies
the two pullbacks of the universal lifted points with the original pair.
For the unit use the same argument on Y times_Y X: hη identifies the two transported
unit points, and hDV identifies their images under qV. Descend to e from the terminal
object over Y. Pulling its factorization equation along the map induced by T to X
gives its displayed identity. The structure-map equations
for m and e follow after precomposition with the same fpqc projections. Empty bases
and empty schemes obey the same universal properties and introduce no exception. -/
theorem exists_raw_monoid_operations_of_effective_projection
    {X Y : Scheme.{u}} {p : X ⟶ Y} [Flat p] [Surjective p] [QuasiCompact p]
    {V : Over X} [MonObj V] (D : Over.DescentDatum p V)
    {V₀ : Over Y} (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V), (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a b : Over.mk f₁ ⟶ V), D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    let q : (Over.map p).obj V ⟶ V₀ := Over.homMk qV hqV.w;
    ∃ (m : V₀ ⊗ V₀ ⟶ V₀) (e : 𝟙_ (Over Y) ⟶ V₀),
      (∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
        (Over.map p).map (lift a b ≫ μ[V]) ≫ q =
          lift ((Over.map p).map a ≫ q) ((Over.map p).map b ≫ q) ≫ m) ∧
      (∀ {T : Scheme.{u}} (f : T ⟶ X),
        (Over.map p).map (toUnit (Over.mk f) ≫ η[V]) ≫ q =
          toUnit (Over.mk (f ≫ p)) ≫ e) := by
  let A := V₀ ⊗ V₀
  let a := localPoint qV hqV A (fst V₀ V₀)
  let b := localPoint qV hqV A (snd V₀ V₀)
  obtain ⟨m, hm⟩ := descend_local_morphism p qV hqV A (lift a b ≫ μ[V]) (by
    intro T g₁ g₂ hg
    have hf : (g₁ ≫ pullback.snd A.hom p) ≫ p =
        (g₂ ≫ pullback.snd A.hom p) ≫ p := by
      simp only [Category.assoc, ← pullback.condition]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ A.hom) hg
    let c₁ : Over.mk (g₁ ≫ pullback.snd A.hom p) ⟶
        Over.mk (pullback.snd A.hom p) := Over.homMk g₁
    let c₂ : Over.mk (g₂ ≫ pullback.snd A.hom p) ⟶
        Over.mk (pullback.snd A.hom p) := Over.homMk g₂
    have ha : D.transport _ _ hf (c₁ ≫ a) = c₂ ≫ a := by
      apply transport_eq_of_projection D qV hqV hDV
      simp only [Over.comp_left, c₁, c₂, Over.homMk_left, Category.assoc]
      dsimp only [a]
      rw [localPoint_projection, ← Category.assoc, hg, Category.assoc]
    have hb : D.transport _ _ hf (c₁ ≫ b) = c₂ ≫ b := by
      apply transport_eq_of_projection D qV hqV hDV
      simp only [Over.comp_left, c₁, c₂, Over.homMk_left, Category.assoc]
      dsimp only [b]
      rw [localPoint_projection, ← Category.assoc, hg, Category.assoc]
    have h := hDV _ _ hf (lift (c₁ ≫ a) (c₁ ≫ b) ≫ μ[V])
    rw [hμ, ha, hb] at h
    simpa only [← comp_lift_assoc, Over.comp_left, c₁, c₂, Over.homMk_left,
      Category.assoc] using h.symm)
  obtain ⟨e, he⟩ := descend_local_morphism p qV hqV (𝟙_ (Over Y))
      (toUnit _ ≫ η[V]) (by
    intro T g₁ g₂ hg
    have hf : (g₁ ≫ pullback.snd (𝟙_ (Over Y)).hom p) ≫ p =
        (g₂ ≫ pullback.snd (𝟙_ (Over Y)).hom p) ≫ p := by
      simp only [Category.assoc, ← pullback.condition]
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ (𝟙_ (Over Y)).hom) hg
    have h := hDV _ _ hf (toUnit _ ≫ η[V])
    rw [hη] at h
    simpa only [Over.comp_left, Over.toUnit_left, Over.mk_hom, Category.assoc] using h.symm)
  refine ⟨m, e, ?_, ?_⟩
  · intro T f c d
    let c₀ := projectPoint qV hqV f c
    let d₀ := projectPoint qV hqV f d
    let k : Over.mk (f ≫ p) ⟶ A := lift c₀ d₀
    let t : T ⟶ Limits.pullback A.hom p := pullback.lift k.left f (Over.w k)
    let s : Over.mk f ⟶ Over.mk (pullback.snd A.hom p) :=
      Over.homMk t (pullback.lift_snd _ _ _)
    have ha : s ≫ a = c := by
      apply Over.OverMorphism.ext
      apply hqV.hom_ext
      · change t ≫ (localPoint qV hqV A (fst V₀ V₀)).left ≫ qV = c.left ≫ qV
        rw [localPoint_projection, ← Category.assoc]
        simp [t, k, c₀, projectPoint]
      · exact (Over.w (s ≫ a)).trans (Over.w c).symm
    have hb : s ≫ b = d := by
      apply Over.OverMorphism.ext
      apply hqV.hom_ext
      · change t ≫ (localPoint qV hqV A (snd V₀ V₀)).left ≫ qV = d.left ≫ qV
        rw [localPoint_projection, ← Category.assoc]
        simp [t, k, d₀, projectPoint]
      · exact (Over.w (s ≫ b)).trans (Over.w d).symm
    have hs : s ≫ (lift a b ≫ μ[V]) = lift c d ≫ μ[V] := by
      rw [comp_lift_assoc, ha, hb]
    apply Over.OverMorphism.ext
    change (lift c d ≫ μ[V]).left ≫ qV = k.left ≫ m.left
    rw [← hs, Over.comp_left, Category.assoc]
    have ht := congrArg (fun z => t ≫ z) hm
    simpa only [s, Over.homMk_left, t, Category.assoc,
      pullback.lift_fst_assoc] using ht.symm
  · intro T f
    let t : T ⟶ Limits.pullback (𝟙_ (Over Y)).hom p :=
      pullback.lift (f ≫ p) f (by simp)
    apply Over.OverMorphism.ext
    change (toUnit (Over.mk f) ≫ η[V]).left ≫ qV =
      (toUnit (Over.mk (f ≫ p)) ≫ e).left
    have ht := congrArg (fun z => t ≫ z) he
    simpa [t, Over.comp_left, Category.assoc] using ht.symm

end CategoryTheory.Over.DescentDatum
